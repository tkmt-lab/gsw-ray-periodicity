"""Run symwalk over a region for the 10 cone-0 starts; cross-check every leaf numerically."""
import json
import sys
import time
from symwalk import Region, F, solve, start_triples, fval, fstr
from d12walk import D12


def check_leaf(R, st, res, pts):
    bad = []
    for (r, s) in pts:
        D = D12(r, s)
        c, z0, z1, z2 = st
        tr = tuple(D.canon(c, (fval(z[0], r, s), fval(z[1], r, s))) for z in (z0, z1, z2))
        x = D.run(tr)
        want = 'endpoint' if res['kind'] == 'pos' else 'repeat'
        if x['kind'] != want or x['stop'] != fval(res['index'], r, s):
            bad.append((r, s, x['kind'], x['stop'], fval(res['index'], r, s)))
    return bad


def run_region(cons, name, max_runs=200, npts=6):
    R = Region(cons, name)
    out = {'region': name, 'cons': [list(c) for c in cons], 'starts': []}
    for k, st in enumerate(start_triples()):
        t0 = time.time()
        leaves = solve(R, st, max_runs=max_runs)
        recs = []
        for L, res in leaves:
            pts = L.sample(npts)
            bad = check_leaf(L, st, res, pts) if res['kind'] in ('pos', 'neg') else ([] if res['kind'] == 'invalid' else ['unfinished'])
            recs.append({'cons': [list(c) for c in L.cons[len(cons):]], 'kind': res['kind'],
                         'index': fstr(res['index']) if 'index' in res else None,
                         'runs': res['runs'], 'checked_points': len(pts), 'bad': bad})
        out['starts'].append({'start': k, 'leaves': recs, 'sec': round(time.time() - t0, 2)})
        kinds = {}
        for x in recs:
            kinds[x['kind']] = kinds.get(x['kind'], 0) + 1
        print(name, 'start', k, 'leaves', len(recs), kinds,
              'bad', sum(len(x['bad']) for x in recs), flush=True)
    return out


if __name__ == '__main__':
    pass
