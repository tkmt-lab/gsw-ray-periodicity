"""Arithmetic step of the cylinder argument (brute force over many (r,s); the general argument
is in the report).  For each congruence start: the lap states are a0 + 2r j while <= hi; the
exit state a_f is the first one > hi; the walk is positive iff a_f lies on one of the two
positive planes of cylinders-cert.json.  Check: this holds iff the stated congruence."""
import json
import sys
from symwalk3 import fval

COND = {0: 1, 3: -1, 4: 1, 8: 1}   # start -> s = COND (mod r)


def main(cert_path, rs):
    cert = {o['start']: o for o in json.load(open(cert_path))}
    from cylinders import SPECS
    bad, n = [], 0
    for sp in SPECS:
        o = cert[sp['start']]
        planes = [x['extra'] for x in o['final'] if x['kind'] == 'pos']
        for r, s in rs:
            lo, hi = fval(sp['lap'][0], r, s, 0), fval(sp['lap'][1], r, s, 0)
            wlo, whi = fval(sp['win'][0], r, s, 0), fval(sp['win'][1], r, s, 0)
            a = fval(sp['a0'], r, s, 0)
            assert lo <= a <= hi and wlo == hi + 1 and whi == hi + 2 * r
            while a <= hi:
                a += 2 * r
            assert wlo <= a <= whi
            on = any(all(fval(tuple(c), r, s, a) >= 0 for c in pl) for pl in planes)
            want = (s - COND[sp['start']]) % r == 0
            n += 1
            if on != want:
                bad.append((sp['start'], r, s, a))
    return n, bad


if __name__ == '__main__':
    rs = [(r, s) for r in range(3, 120) for s in range(10 * r, 10 * r + 4 * r + 3)]
    print(main(sys.argv[1], rs))
