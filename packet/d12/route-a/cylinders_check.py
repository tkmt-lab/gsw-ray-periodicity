"""Numeric cross-check of cylinders.py on sample points (r,s) with s >= 10r."""
import json
import sys
import symwalk
from symwalk3 import fval
from d12walk import D12
from cylinders import SPECS


def parse(cons):
    return [tuple(c) for c in cons]


def main(cert, pts):
    C = {o['start']: o for o in json.load(open(cert))}
    stats = {'checked': 0, 'bad': []}
    for (r, s) in pts:
        D = D12(r, s)
        for sp in SPECS:
            o = C[sp['start']]
            lo, hi = fval(sp['lap'][0], r, s, 0), fval(sp['lap'][1], r, s, 0)
            a = fval(sp['a0'], r, s, 0)
            j = 0
            while a <= hi:
                a += 2 * r
                j += 1
            lam = fval(tuple(o['lap']['increment_form']), r, s, 0)
            idx_f = fval(tuple(o['transient']['index_form']), r, s, 0) + j * lam
            par = idx_f % 2
            leaf = [x for x in o['final'] if all(fval(tuple(c), r, s, a) >= 0 for c in x['extra'])]
            assert len(leaf) == 1, (r, s, sp['start'], len(leaf))
            leaf = leaf[0]
            pred_abs = fval(tuple(leaf['index_form']), r, s, a) - par + idx_f
            st = symwalk.start_triples()[sp['start']]
            c, z0, z1, z2 = st
            tr = tuple(D.canon(c, (symwalk.fval(z[0], r, s), symwalk.fval(z[1], r, s))) for z in (z0, z1, z2))
            x = D.run(tr)
            ok = (x['kind'] == 'repeat' and x['stop'] <= pred_abs) if leaf['kind'] == 'neg' else (
                x['kind'] == 'endpoint' and x['stop'] == pred_abs)
            stats['checked'] += 1
            if not ok:
                stats['bad'].append((r, s, sp['start'], leaf['kind'], pred_abs, x['kind'], x['stop']))
    return stats


if __name__ == '__main__':
    pts = [(r, s) for r in range(3, 9) for s in range(10 * r, 13 * r + 1)]
    pts += [(11, 133), (13, 157), (17, 205), (19, 191), (23, 277), (9, 181), (12, 241), (14, 141)]
    print(main(sys.argv[1], pts))
