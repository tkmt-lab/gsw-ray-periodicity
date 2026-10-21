"""Lazy forced-walk decider for literal gSW paths in D12(r,s) (route-a, 2026-10-19).

Geometry = the Lean-mirrored signature `d12_sig` of ../atlas/reference_model.py:
two lattice 12-gons (regular hexagons of side L=r+2s with 6 marked boundary points), corner
labels 0..11, sides with equal label pairs glued in reverse.  A vertex of the dual
triangulation is a class of lattice sites (cell, z) under the gluing; edges are unit steps
inside one cell.  Nothing is enumerated globally: vertices touched by a walk are built
lazily, so memory is O(walk length) and large (r,s) are cheap.

Decision (Bille-Buchstaber-Spodarev Def. 1(a)): every dual edge has exactly two common
neighbours (asserted on every step), so a literal path is a prefix of the forced
continuation p_{i+1} = (N(p_i) & N(p_{i-1})) - {p_{i-2}} from its first oriented triangle.
For each start (p0 deg 5, p1 ~ p0 deg 6, p2 one of the two common neighbours) we follow
the continuation until the first legal endpoint (odd index >= 3, deg 5, predecessor deg 6)
or the first repeated vertex.
"""
from math import gcd


def rot(z):
    return (-z[1], z[0] + z[1])


def rotN(n, z):
    for _ in range(n % 6):
        z = rot(z)
    return z


UNIT = [(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)]
LAB = [list(range(12)), [0] + list(range(11, 0, -1))]


def walkpts(p, steps):
    out = []
    for length, k in steps:
        out.append(p)
        d = rotN(k, (length, 0))
        p = (p[0] + d[0], p[1] + d[1])
    return out


def d12_polys(r, s):
    """Identical to d12_sig in reference_model.py (Lean AlignedSpecification)."""
    p0 = walkpts((0, 0), [(s, 0), (r + s, 1), (s, 1), (r + s, 2), (s, 2), (r + s, 3),
                          (s, 3), (r + s, 4), (s, 4), (r + s, 5), (s, 5), (r + s, 0)])
    p1 = walkpts((0, 0), [(r + s, 0), (s, 0), (r + s, 1), (s, 1), (r + s, 2), (s, 2),
                          (r + s, 3), (s, 3), (r + s, 4), (s, 4), (r + s, 5), (s, 5)])
    return [p0, p1]


class D12:
    def __init__(self, r, s, lab=LAB, polys=None):
        self.r, self.s = r, s
        self.lab = lab
        self.P = polys if polys is not None else d12_polys(r, s)
        self.seg = []  # per cell: list of (a, d, n)
        for c in range(len(self.P)):
            P = self.P[c]
            row = []
            for k in range(len(P)):
                a, b = P[k], P[(k + 1) % len(P)]
                v = (b[0] - a[0], b[1] - a[1])
                n = gcd(abs(v[0]), abs(v[1]))
                row.append((a, (v[0] // n, v[1] // n), n))
            self.seg.append(row)
        # partner segment: (c,k) [label u->v] glued to (c',j) [label v->u]
        self.partner = {}
        for c in range(len(self.P)):
            for k in range(len(self.P[c])):
                u, v = self.lab[c][k], self.lab[c][(k + 1) % len(self.lab[c])]
                for c2 in range(len(self.P)):
                    for j in range(len(self.P[c2])):
                        if (self.lab[c2][j], self.lab[c2][(j + 1) % len(self.lab[c2])]) == (v, u):
                            assert self.seg[c][k][2] == self.seg[c2][j][2]
                            self.partner[c, k] = (c2, j)
        self._canon = {}
        self._nbr = {}

    def inside(self, c, z):
        for a, d, n in self.seg[c]:
            if d[0] * (z[1] - a[1]) - d[1] * (z[0] - a[0]) < 0:
                return False
        return True

    def on_segments(self, c, z):
        out = []
        for k, (a, d, n) in enumerate(self.seg[c]):
            w = (z[0] - a[0], z[1] - a[1])
            if d[0] * w[1] - d[1] * w[0] != 0:
                continue
            t = w[0] // d[0] if d[0] != 0 else w[1] // d[1]
            if 0 <= t <= n:
                out.append((k, t))
        return out

    def copies(self, c, z):
        seen = {(c, z)}
        stack = [(c, z)]
        while stack:
            c1, z1 = stack.pop()
            for k, t in self.on_segments(c1, z1):
                c2, j = self.partner[c1, k]
                a2, d2, n2 = self.seg[c2][j]
                e = (a2[0] + n2 * d2[0] - t * d2[0], a2[1] + n2 * d2[1] - t * d2[1])
                if (c2, e) not in seen:
                    seen.add((c2, e))
                    stack.append((c2, e))
        return seen

    def canon(self, c, z):
        key = (c, z)
        v = self._canon.get(key)
        if v is None:
            cp = self.copies(c, z)
            v = min(cp)
            for q in cp:
                self._canon[q] = v
        return v

    def nbr(self, v):
        N = self._nbr.get(v)
        if N is None:
            N = set()
            for c, z in self.copies(*v):
                for u in UNIT:
                    w = (z[0] + u[0], z[1] + u[1])
                    if self.inside(c, w):
                        x = self.canon(c, w)
                        if x != v:
                            N.add(x)
            self._nbr[v] = N
        return N

    def deg(self, v):
        return len(self.nbr(v))

    def cone(self, label):
        return self.canon(0, self.P[0][self.lab[0].index(label)])

    def starts(self, labels=range(12)):
        out = []
        for lb in labels:
            p0 = self.cone(lb)
            assert self.deg(p0) == 5
            for p1 in sorted(self.nbr(p0)):
                if self.deg(p1) != 6:
                    continue
                for p2 in sorted(self.nbr(p0) & self.nbr(p1)):
                    out.append((p0, p1, p2))
        return out

    def run(self, start, keep=False, cap=None):
        """Follow the forced continuation.  Returns dict(kind, stop, first, path?)."""
        seq = list(start)
        pos = {seq[0]: 0, seq[1]: 1, seq[2]: 2}
        while True:
            a, b, c = seq[-3], seq[-2], seq[-1]
            cand = (self.nbr(b) & self.nbr(c)) - {a}
            assert len(cand) == 1 and len(self.nbr(b) & self.nbr(c)) == 2, (self.r, self.s)
            x = cand.pop()
            i = len(seq)
            if x in pos:
                res = {'kind': 'repeat', 'stop': i, 'first': pos[x]}
                break
            seq.append(x)
            pos[x] = i
            if i % 2 == 1 and i >= 3 and self.deg(x) == 5 and self.deg(c) == 6:
                res = {'kind': 'endpoint', 'stop': i, 'first': None}
                break
            if cap is not None and i >= cap:
                res = {'kind': 'cap', 'stop': i, 'first': None}
                break
        if keep:
            res['path'] = seq
        return res


def decide(r, s, labels=range(12), keep=False):
    S = D12(r, s)
    recs = []
    for st in S.starts(labels):
        recs.append(S.run(st, keep=keep))
    return S, recs


if __name__ == '__main__':
    import sys
    r, s = int(sys.argv[1]), int(sys.argv[2])
    S, recs = decide(r, s)
    succ = sum(x['kind'] == 'endpoint' for x in recs)
    print(r, s, 'starts', len(recs), 'successes', succ)
