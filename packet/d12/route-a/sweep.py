"""Sweep D12(r,s) with all starts; write one JSON line per (r,s).
Usage: python3 sweep.py OUT.jsonl r_lo r_hi s_lo s_hi [workers]   or   python3 sweep.py OUT.jsonl --pairs FILE.json [workers]"""
import json
import sys
import time
from multiprocessing import Pool
from d12walk import decide


def one(rs):
    r, s = rs
    t0 = time.time()
    S, recs = decide(r, s)
    succ = sum(x['kind'] == 'endpoint' for x in recs)
    # per-start outcomes for cone label 0 (10 starts when r,s large enough)
    n0 = sum(1 for st in S.starts([0]))
    return {'r': r, 's': s, 'starts': len(recs), 'successes': succ, 'positive': succ > 0,
            'cone0': [[x['kind'][0], x['stop'], x['first']] for x in recs[:n0]],
            'min_stop': min(x['stop'] for x in recs), 'max_stop': max(x['stop'] for x in recs),
            'sec': round(time.time() - t0, 3)}


if __name__ == '__main__':
    out = sys.argv[1]
    if sys.argv[2] == '--pairs':
        pairs = [tuple(p) for p in json.load(open(sys.argv[3]))]
        w = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    else:
        a, b, c, d = map(int, sys.argv[2:6])
        pairs = [(r, s) for r in range(a, b + 1) for s in range(c, d + 1)]
        w = int(sys.argv[6]) if len(sys.argv) > 6 else 4
    with Pool(w) as pool, open(out, 'w') as f:
        for rec in pool.imap(one, pairs, chunksize=4):
            f.write(json.dumps(rec) + '\n')
            f.flush()
