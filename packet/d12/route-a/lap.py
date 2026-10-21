"""Lap lemma for the cylinder phase (symwalk3, variables r, s, a)."""
import sys
from symwalk3 import *


def S_state(cell, a_pt_fn):
    pass


def lap_check(region, cell, T, runs, shift, max_leaves=500):
    """Run `runs` runs from triple T (chart `cell`, index 0) on every leaf of `region`.
    Report per leaf: does the final state equal T shifted by `shift` (a -> a+shift form) in the
    same chart, and are all lap lines free of cone points (any parity)."""
    work = [region]
    out = []
    while work:
        R = work.pop()
        if R.empty():
            continue
        try:
            res = execute(R, (cell, T[0], T[1], T[2]), max_runs=runs + 1, stop_runs=runs, i0=fconst(2))
            if res['kind'] != 'state':
                out.append((R, 'no-state', res))
                continue
            # cone-free lap lines (only the lines produced by the runs, not the 3 seed points)
            free = True
            for X in res['lines'][3:]:
                for C in G.cone[X.cell].values():
                    dC = psub(C, X.Z)
                    if R.eq0(cross_cv(X.v, dC)):
                        m = proj(dC, X.v)
                        if R.ge0(m) and R.ge0(fsub(X.n, m)):
                            free = False
            free = free and res['best_R'] is None and res['best_E'] is None
            same = res['cell'] == cell and all(
                R.eq0(fsub(res['T'][j][q], shift(T[j])[q])) for j in range(3) for q in range(2))
            out.append((R, 'ok' if (same and free) else ('moved' if free else 'cone'), res))
        except Split as sp:
            work.extend(sp.pieces)
        if len(out) > max_leaves:
            raise RuntimeError('too many leaves')
    return out


def S0(shift_r=0):
    """Canonical lap state of the start-0 cylinder: chart 0, T=[(a+1,-1),(a,0),(a+1,0)] with
    a replaced by a + shift_r*r."""
    A = F(shift_r, 0, 1, 0)
    return [(fadd(A, fconst(1)), fconst(-1)), (A, fconst(0)), (fadd(A, fconst(1)), fconst(0))]


def final_phase(R, Sfn, cell, lap_len, lap_shift_r, nhist=2, max_runs=40, i_par=1):
    """Executor from S(a) with the lines of the nhist previous laps as history."""
    hist = []
    for h in range(nhist, 0, -1):
        Th = Sfn(-lap_shift_r * h)
        i0 = fadd(fconst(i_par), fmul(-h, lap_len))
        res = execute(R, (cell, Th[0], Th[1], Th[2]), max_runs=5, stop_runs=4, i0=i0)
        assert res['kind'] == 'state'
        assert res['cell'] == cell and all(R.eq0(fsub(res['T'][j][q], Sfn(-lap_shift_r * (h - 1))[j][q]))
                                           for j in range(3) for q in range(2)), 'lap lemma failed'
        hist.extend(res['lines'][3:])
    T = Sfn(0)
    return execute(R, (cell, T[0], T[1], T[2]), max_runs=max_runs, history=hist, i0=fconst(i_par), seeds=False)


def solve_final(region, **kw):
    work, out = [region], []
    while work:
        R = work.pop()
        if R.empty():
            continue
        try:
            out.append((R, final_phase(R, **kw)))
        except Split as sp:
            work.extend(sp.pieces)
    return out


def S1(shift_r=0):
    """start-4 cylinder: chart 1, T=[(a+1,-1),(a,0),(a+1,0)]."""
    return S0(shift_r)


def S2(shift_r=0):
    """start-8 cylinder: chart 1, T=[(a+1,-1),(a+1,0),(a,0)]."""
    A = F(shift_r, 0, 1, 0)
    return [(fadd(A, fconst(1)), fconst(-1)), (fadd(A, fconst(1)), fconst(0)), (A, fconst(0))]
