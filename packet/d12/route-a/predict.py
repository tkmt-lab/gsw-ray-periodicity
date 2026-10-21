"""Preregistered prediction for D12(r,s) (route-a, fixed before the holdout run).

Conjecture C (closed condition):
    D12(r,s) (r,s >= 1) has a literal gSW path  <=>  s = +-1 (mod r)  or  |r - 3s| = 1.
(For r=1 the congruence always holds; for r=2 it means s odd.)

Auxiliary prediction (number of successful starts / number of starts):
    starts = 96 if s = 1 (every cone point then has a degree-5 neighbour), else 120.
    r=1: s=1 -> 96, s=2 -> 108, s>=3 -> 96.
    r=2: s even -> 0, s=1 -> 96, s=3 -> 60, s odd >= 5 -> 48.
    r>=3: s=1 -> 60 if r=4 else 48;  s=r-1 or s=r+1 -> 48;  s = 1 mod r, s > r+1 -> 36;
          s = -1 mod r, s >= 2r-1 -> 12;  |r-3s| = 1, s >= 2 -> 12;  otherwise 0.
"""
import random
from math import gcd


def conj(r, s):
    return s % r in (1 % r, (r - 1) % r) or abs(r - 3 * s) == 1


def predicted_starts(r, s):
    return 96 if s == 1 else 120


def predicted_successes(r, s):
    if r == 1:
        return {1: 96, 2: 108}.get(s, 96)
    if r == 2:
        if s % 2 == 0:
            return 0
        return {1: 96, 3: 60}.get(s, 48)
    if s == 1:
        return 60 if r == 4 else 48
    if s in (r - 1, r + 1):
        return 48
    if s > r + 1 and s % r == 1:
        return 36
    if s >= 2 * r - 1 and s % r == r - 1:
        return 12
    if abs(r - 3 * s) == 1:
        return 12
    return 0


def holdout_pairs(seed=20261019):
    """Unseen parameters: every pair has max(r,s) >= 41 (the discovery sweep was r,s <= 40)."""
    rng = random.Random(seed)
    seen = set()
    out = []

    def add(r, s, tag):
        if r >= 1 and s >= 1 and max(r, s) >= 41 and (r, s) not in seen:
            seen.add((r, s))
            out.append((r, s, tag))

    # A: 100 uniform pairs in [1,300]^2 (resampled while seen/too small)
    while sum(1 for x in out if x[2] == 'uniform') < 100:
        add(rng.randint(1, 300), rng.randint(1, 300), 'uniform')
    # B: 60 on predicted-positive branches
    for _ in range(12):
        r = rng.randint(3, 120); q = rng.randint(1, 4)
        add(r, q * r + 1, 'pos:s=qr+1'); add(r, q * r - 1, 'pos:s=qr-1')
        s = rng.randint(14, 120); add(3 * s - 1, s, 'pos:r=3s-1'); add(3 * s + 1, s, 'pos:r=3s+1')
        add(rng.randint(41, 300), 1, 'pos:s=1')
    # C: 120 near misses (predicted negative unless the branch coincides)
    for _ in range(12):
        r = rng.randint(4, 120); q = rng.randint(1, 4)
        add(r, q * r + 2, 'near:s=qr+2'); add(r, q * r - 2, 'near:s=qr-2'); add(r, q * r, 'near:s=qr')
        s = rng.randint(14, 120)
        add(3 * s, s, 'near:r=3s'); add(3 * s + 2, s, 'near:r=3s+2'); add(3 * s - 2, s, 'near:r=3s-2')
        add(4 * s + 1, s, 'near:r=4s+1'); add(4 * s - 1, s, 'near:r=4s-1')
        add(2 * s + 1, s, 'near:r=2s+1'); add(2 * s - 1, s, 'near:r=2s-1')
    # D: boundary rows r=1,2 and s=2
    for _ in range(10):
        add(1, rng.randint(41, 400), 'r=1'); add(2, rng.randint(41, 400), 'r=2')
        add(rng.randint(41, 400), 2, 's=2')
    return out


if __name__ == '__main__':
    import json
    import sys
    P = holdout_pairs()
    json.dump([[r, s] for r, s, _ in P], open(sys.argv[1], 'w'))
    from collections import Counter
    print(len(P), sum(conj(r, s) for r, s, _ in P), Counter(t.split(':')[0] for *_, t in P))
