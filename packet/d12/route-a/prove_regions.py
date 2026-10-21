"""Computer-assisted general proofs over (r,s)-regions with the symbolic executor symwalk.py.

For each region and each of the 10 oriented faces at cone 0 (all starts up to the D6
symmetry, see report), the executor partitions the region into leaves on which the forced
walk has a fixed combinatorial type, with the first event (repeat / legal endpoint) index an
affine form in (r,s).  Every leaf is also cross-checked numerically with d12walk.py on sample
points.  Writes a JSON certificate summary.

usage: python3 prove_regions.py OUT.json main | wedges QLO QHI
"""
import json
import sys
import time
from symwalk import Region, F, solve, start_triples, fstr
from symdrive import check_leaf

CONG = (0, 3, 4, 8)   # starts whose run count is unbounded for s >> r


def region_result(cons, name, starts=range(10), max_runs=200, npts=5):
    R = Region(cons, name)
    out = {'region': name, 'cons': [list(c) for c in cons], 'starts': {}}
    t0 = time.time()
    for k in starts:
        st = start_triples()[k]
        leaves = solve(R, st, max_runs=max_runs)
        recs = []
        for L, res in leaves:
            pts = L.sample(npts)
            bad = check_leaf(L, st, res, pts) if res['kind'] in ('pos', 'neg') else (
                [] if res['kind'] == 'invalid' else ['unfinished'])
            recs.append({'extra': [list(c) for c in L.cons[len(cons):]], 'kind': res['kind'],
                         'index': fstr(res['index']) if 'index' in res else None,
                         'runs': res['runs'], 'pts': pts, 'bad': bad})
        out['starts'][k] = recs
    out['sec'] = round(time.time() - t0, 2)
    out['summary'] = {k: sorted({x['kind'] for x in v}) for k, v in out['starts'].items()}
    out['bad'] = sum(len(x['bad']) for v in out['starts'].values() for x in v)
    pos = sorted({(k, tuple(map(tuple, x['extra']))) for k, v in out['starts'].items() for x in v if x['kind'] == 'pos'})
    out['positive_leaves'] = [[k, list(map(list, e))] for k, e in pos]
    print(name, out['summary'], 'bad', out['bad'], 'sec', out['sec'], flush=True)
    return out


MAIN = [
    ([F(0, 1, -2), F(1, -1, -2)], 'A: s>=2, r>=s+2'),
    ([F(0, 1, -1), F(0, -1, 1), F(1, 0, -3)], 'B: s=1, r>=3'),
    ([F(1, 0, -3), F(-1, 1, 1), F(1, -1, -1)], 'C: s=r-1, r>=3'),
    ([F(1, 0, -3), F(-1, 1, 0), F(1, -1, 0)], 'D: s=r, r>=3'),
    ([F(1, 0, -3), F(-1, 1, -1), F(1, -1, 1)], 'E: s=r+1, r>=3'),
]

if __name__ == '__main__':
    outp = sys.argv[1]
    res = []
    if sys.argv[2] == 'main':
        for cons, name in MAIN:
            res.append(region_result(cons, name))
        # non-congruence starts on the whole region s >= r+2
        res.append(region_result([F(1, 0, -3), F(-1, 1, -2)], 'F: r>=3, s>=r+2 (6 starts)',
                                 starts=[k for k in range(10) if k not in CONG]))
    else:
        qlo, qhi = int(sys.argv[3]), int(sys.argv[4])
        for q in range(qlo, qhi + 1):
            cons = [F(1, 0, -3), F(-q, 1, -2), F(q + 1, -1, 1)]   # q r + 2 <= s <= (q+1) r + 1
            res.append(region_result(cons, 'W%d: r>=3, %dr+2<=s<=%dr+1' % (q, q, q + 1),
                                     starts=CONG, max_runs=4 * q + 40))
    json.dump(res, open(outp, 'w'), indent=0)
