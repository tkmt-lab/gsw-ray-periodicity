"""Full-history positivity for the cylinder exits (symwalk4, variables r, s, a, b).

For a positive final leaf (a = a_f on a plane P(r,s), endpoint E) we show that NO two of the
vertices with index <= E coincide, where the vertices are: transient lines (start -> S(a0)),
all lap lines (relaxed: a lap from S(b) for EVERY integer b in [a0, a-2r], a superset of the
real laps a0+2rj), and the final lines truncated at E.  Checks: final x final (executor),
final x lap(b), transient x lap(b), transient x final, lap(b) x lap(b') for b+2r <= b' (as
(b, a) with b + 2r <= a <= hi), transient x transient and lap x itself (cylinders.py).
"""
import json
import sys
from symwalk4 import *
from cylinders import SPECS as SPECS3, _PIN

BASE = [F(1, 0, 0, 0, -3), F(-10, 1, 0, 0, 0)] if not _PIN else [
    F(1, 0, 0, 0, -int(_PIN)), F(-1, 0, 0, 0, int(_PIN)), F(-10, 1, 0, 0, 0)]
AV = F(0, 0, 1, 0, 0)
BV = F(0, 0, 0, 1, 0)


def L4(f3):
    return (f3[0], f3[1], 0, 0, f3[3])


def fam(kind, var):
    """S-families of lap.py with parameter var (AV or BV)."""
    one, m1, zero = fconst(1), fconst(-1), fconst(0)
    if kind in ('S0', 'S1'):
        return [(fadd(var, one), m1), (var, zero), (fadd(var, one), zero)]
    return [(fadd(var, one), m1), (fadd(var, one), zero), (var, zero)]


SPECS = []
for sp in SPECS3:
    SPECS.append(dict(start=sp['start'], cell=sp['cell'], S={0: 'S0', 3: 'S0', 4: 'S1', 8: 'S2'}[sp['start']],
                      nT=sp['nT'], a0=L4(sp['a0']), lap=tuple(L4(x) for x in sp['lap']),
                      win=tuple(L4(x) for x in sp['win'])))


def lap_lines(R, sp, var, i0):
    T = fam(sp['S'], var)
    res = execute(R, (sp['cell'], T[0], T[1], T[2]), max_runs=5, stop_runs=4, i0=i0)
    assert res['kind'] == 'state'
    return res['lines'][3:]


def truncate(R, lines, E):
    out = []
    for X in lines:
        par = X.I[-1] % 2
        top = fsub(E, X.I) if par == 1 else fsub(fsub(E, fconst(1)), X.I)   # even form
        assert all(v % 2 == 0 for v in top) or True
        half = tuple(v // 2 for v in top)
        assert all(2 * h == v for h, v in zip(half, top)), 'parity'
        if not R.ge0(half):
            continue
        n = R.fmin([X.n, half])
        out.append(Line(X.cell, X.Z, X.v, X.I, n, X.run, X.pred))
    return out


def no_coincidence(R, Xs, Ys):
    for X in Xs:
        for Y in Ys:
            if coincide(R, X, Y) is not None:
                return False
    return True


def check_leaf(sp, plane_cons, E_form_rel, nruns):
    """plane_cons: extra constraints (3-var forms) of the positive leaf."""
    base = BASE
    win = [fsub(AV, sp['win'][0]), fsub(sp['win'][1], AV), fsub(AV, fadd(sp['a0'], F(4, 0, 0, 0, 0)))]
    plane = [L4(tuple(c[:3]) + (c[3],)) if False else (c[0], c[1], c[2], 0, c[3]) for c in plane_cons]
    brng = [fsub(BV, sp['a0']), fsub(fsub(AV, F(2, 0, 0, 0, 0)), BV)]   # a0 <= b <= a - 2r
    work = [Region(base + win + plane + brng)]
    results = []
    while work:
        R = work.pop()
        if R.empty():
            continue
        try:
            # transient (index from 0)
            res = execute(R, start_triples()[sp['start']], max_runs=sp['nT'] + 1, stop_runs=sp['nT'])
            trans = res['lines']
            iT = res['i']
            # final phase lines from S(a), index base = parity of iT (relative indices)
            T = fam(sp['S'], AV)
            par = iT[-1] % 2
            fin = execute(R, (sp['cell'], T[0], T[1], T[2]), max_runs=nruns + 1, stop_runs=nruns,
                          i0=fconst(par), seeds=False)
            E = (E_form_rel[0], E_form_rel[1], E_form_rel[2], 0, E_form_rel[3])
            fl = truncate(R, fin['lines'], E)
            assert fin['best_R'] is None or not R.le(fin['best_R'], E)
            lb = lap_lines(R, sp, BV, fconst(0))
            ok1 = no_coincidence(R, fl, lb)
            ok2 = no_coincidence(R, fl, trans)
            ok3 = no_coincidence(R, lb, trans)
            results.append((R, ok1, ok2, ok3))
        except Split as e:
            work.extend(e.pieces)
    return results


def check_lap_pairs(sp):
    """lap(a) vs lap(b), b + 2r <= a <= hi, b >= a0 (relaxed)."""
    base = BASE
    rng = [fsub(BV, sp['a0']), fsub(fsub(AV, F(2, 0, 0, 0, 0)), BV), fsub(sp['lap'][1], AV)]
    work = [Region(base + rng)]
    out = []
    while work:
        R = work.pop()
        if R.empty():
            continue
        try:
            la = lap_lines(R, sp, AV, fconst(0))
            lb = lap_lines(R, sp, BV, fconst(0))
            out.append((R, no_coincidence(R, la, lb)))
        except Split as e:
            work.extend(e.pieces)
    return out


if __name__ == '__main__':
    cert = {o['start']: o for o in json.load(open(sys.argv[1]))}
    report = []
    for sp in SPECS:
        o = cert[sp['start']]
        if not o['transient']['ok']:
            print({'start': sp['start'], 'skipped': 'transient not of the cylinder form here'})
            report.append({'start': sp['start'], 'skipped': True})
            continue
        lp = check_lap_pairs(sp)
        rec = {'start': sp['start'], 'lap_pairs_leaves': len(lp), 'lap_pairs_ok': all(x[1] for x in lp), 'pos': []}
        for leaf in o['final']:
            if leaf['kind'] != 'pos':
                continue
            res = check_leaf(sp, leaf['extra'], tuple(leaf['index_form']), leaf['runs'])
            rec['pos'].append({'extra': leaf['extra'], 'leaves': len(res),
                               'final_vs_laps': all(x[1] for x in res), 'final_vs_transient': all(x[2] for x in res),
                               'laps_vs_transient': all(x[3] for x in res)})
        print(rec, flush=True)
        report.append(rec)
    json.dump(report, open(sys.argv[2], 'w'), indent=1)
