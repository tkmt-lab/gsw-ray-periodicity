"""General (all q) treatment of the four 'congruence' starts 0,3,4,8 for r>=3, s>=10r.

For each start: (1) transient: from the start the walk reaches a lap state S(a0) of its
cylinder without a legal endpoint; (2) lap lemma: on the whole lap range, S(a) -> S(a+2r)
after 4 runs, index +Lambda, no cone point on any lap line (any parity); (3) final phase:
from S(a) with a in the exit window, with the two previous laps as history, the executor
partitions (r,s,a) into leaves; negative leaves exhibit a repeat before any legal endpoint.
Positive leaves are planes a = P(r,s); combined with a = a0 (mod 2r) this gives the
congruence.  Everything is affine in (r,s,a); see symwalk3.py.
"""
import json
import sys
from lap import *

import os
# base region: r >= 3 (default) or a pinned r (D12_PIN_R=1 or 2), and s >= 10 r
_PIN = os.environ.get('D12_PIN_R')
R3 = F(1, 0, 0, -3) if not _PIN else F(1, 0, 0, -int(_PIN))
RPIN = [] if not _PIN else [F(-1, 0, 0, int(_PIN))]
SBIG = F(-10, 1, 0, 0)          # s >= 10 r
SPECS = [
    # start, cell, S-family, transient runs, a0, lap range [lo, hi], exit window [lo, hi]
    dict(start=0, cell=0, S=S0, nT=4, a0=F(2, 0, 0, 0), lap=(F(0, 0, 0, 1), F(-2, 1, 0, -2)),
         win=(F(-2, 1, 0, -1), F(0, 1, 0, -2))),
    dict(start=3, cell=0, S=S0, nT=4, a0=F(2, 0, 0, -1), lap=(F(0, 0, 0, 1), F(-2, 1, 0, -2)),
         win=(F(-2, 1, 0, -1), F(0, 1, 0, -2))),
    dict(start=4, cell=1, S=S1, nT=5, a0=F(3, 1, 0, 0), lap=(F(1, 1, 0, 1), F(-1, 2, 0, -2)),
         win=(F(-1, 2, 0, -1), F(1, 2, 0, -2))),
    dict(start=8, cell=1, S=S2, nT=4, a0=F(2, 0, 0, 0), lap=(F(0, 0, 0, 1), F(-1, 1, 0, -2)),
         win=(F(-1, 1, 0, -1), F(1, 1, 0, -2))),
]


def a_is(form):
    """constraints a == form"""
    return [fsub(F(0, 0, 1, 0), form), fsub(form, F(0, 0, 1, 0))]


def a_between(lo, hi):
    return [fsub(F(0, 0, 1, 0), lo), fsub(hi, F(0, 0, 1, 0))]


def subst_a(T, a0):
    """S-family triple evaluated at a = a0 (a0 a form without a)."""
    def sub(f):
        return fadd((f[0], f[1], 0, f[3]), fmul(f[2], a0))
    return [(sub(p[0]), sub(p[1])) for p in T]


def run_spec(sp):
    out = {'start': sp['start'], 'cell': sp['cell']}
    k, cell, Sf = sp['start'], sp['cell'], sp['S']
    # (1) transient, region r>=3, s>=10r, a=0 (a unused)
    R = Region([R3, SBIG] + RPIN + a_is(F(0, 0, 0, 0)))
    res = execute(R, start_triples()[k], max_runs=sp['nT'] + 1, stop_runs=sp['nT'])
    target = subst_a(Sf(0), sp['a0'])
    ok_T = res['kind'] == 'state' and res['cell'] == cell and res['best_E'] is None and res['best_R'] is None and all(
        R.eq0(fsub(res['T'][j][q], target[j][q])) for j in range(3) for q in range(2))
    out['transient'] = {'ok': ok_T, 'index_of_T2': fstr(res['i']), 'a0': fstr(sp['a0']),
                        'index_form': list(res['i'])}
    # (2) lap lemma on the lap range
    shift = lambda p: (fadd(p[0], F(2, 0, 0, 0)), p[1])
    RL = Region([R3, SBIG] + RPIN + a_between(*sp['lap']))
    leaves = lap_check(RL, cell, Sf(0), 4, shift)
    incs = sorted({fstr(fsub(r_['i'], fconst(2))) for _, kind, r_ in leaves if kind == 'ok'})
    out['lap'] = {'leaves': len(leaves), 'all_ok': all(kind == 'ok' for _, kind, _ in leaves),
                  'index_increment': incs, 'range': [fstr(x) for x in sp['lap']],
                  'increment_form': list(fsub(leaves[0][2]['i'], fconst(2)))}
    assert len(incs) == 1
    lam = fsub(leaves[0][2]['i'], fconst(2))
    # a0 inside lap range or the first exit window, and the progression is the lap sequence
    # (3) final phase with two history laps (needs a >= a0 + 4r)
    par = (fval(res['i'], 0, 0, 0)) % 2  # parity of index of T2 at lap states (constant)
    assert all(v % 2 == 0 for v in res['i'][:-1]) and all(v % 2 == 0 for v in lam[:-1]) and lam[-1] % 2 == 0
    RF = Region([R3, SBIG] + RPIN + a_between(*sp['win']) + [fsub(F(0, 0, 1, 0), fadd(sp['a0'], F(4, 0, 0, 0)))])
    fin = solve_final(RF, Sfn=Sf, cell=cell, lap_len=lam, lap_shift_r=2, i_par=par)
    out['final'] = []
    for Rl, r_ in fin:
        out['final'].append({'extra': [list(c) for c in Rl.cons[len(RF.cons):]], 'kind': r_['kind'],
                             'index_rel': fstr(r_['index']) if 'index' in r_ else None,
                             'index_form': list(r_['index']) if 'index' in r_ else None, 'runs': r_['runs']})
    out['final_kinds'] = sorted({x['kind'] for x in out['final']})
    return out


if __name__ == '__main__':
    res = [run_spec(sp) for sp in SPECS]
    for o in res:
        print(o['start'], o['transient'], o['lap'], o['final_kinds'])
        for x in o['final']:
            if x['kind'] != 'neg':
                print('    ', x)
    json.dump(res, open(sys.argv[1], 'w'), indent=1)
