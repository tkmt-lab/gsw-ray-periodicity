"""Parametric (symbolic) execution of the D12 forced walk over polyhedral regions of (r,s).

Everything (cell corners, gluing translations, walk positions, indices, run lengths) is an
integer affine form a*r + b*s + c.  Directions are constant unit lattice vectors.  Every
branch of the walk is decided by the sign of an affine form over the current region R (a 2D
polyhedron with integer points), using exact rational vertex/ray enumeration (real
relaxation, hence sound for all integer points).  If a sign is not constant on R, the region
is split exactly (f >= 0 | f <= -1, or f >= 1 | f == 0 | f <= -1) and the walk is re-executed
on each piece.  Output per leaf region: kind ('neg' = first repeat before any legal endpoint,
'pos' = legal endpoint first) and the event index as an affine form.

Walk model (same as d12walk.py): in a cell chart the triple (p_{i-2},p_{i-1},p_i) continues
by p_{i+1} = p_{i-1}+p_i-p_{i-2} while inside the closed convex cell; when the next point
leaves, the last edge lies on one boundary segment and the triple is transported by that
segment's gluing isometry into the partner cell.  Repeats: coincidences between run lines
(same chart, or across a glued segment).  Legal endpoints: odd-index lines through cone
points whose predecessor (same chart) is not a cone point.
"""
from fractions import Fraction as Fr

# ------------------------------------------------------------------ affine forms


def F(a=0, b=0, c=0):
    return (a, b, c)


ZERO = F()


def fadd(x, y):
    return (x[0] + y[0], x[1] + y[1], x[2] + y[2])


def fsub(x, y):
    return (x[0] - y[0], x[1] - y[1], x[2] - y[2])


def fmul(k, x):
    return (k * x[0], k * x[1], k * x[2])


def fconst(c):
    return (0, 0, c)


def fval(x, r, s):
    return x[0] * r + x[1] * s + x[2]


def fstr(x):
    out = []
    for coef, name in ((x[0], 'r'), (x[1], 's')):
        if coef:
            out.append(('%d%s' % (coef, name)) if abs(coef) != 1 else ('-' if coef < 0 else '') + name)
    if x[2] or not out:
        out.append('%d' % x[2])
    return '+'.join(out).replace('+-', '-')


def padd(p, q):
    return (fadd(p[0], q[0]), fadd(p[1], q[1]))


def psub(p, q):
    return (fsub(p[0], q[0]), fsub(p[1], q[1]))


def pscale(form, d):
    """form * constant vector d"""
    return (fmul(d[0], form), fmul(d[1], form))


def pconst(d):
    return (fconst(d[0]), fconst(d[1]))


def protN(n, p):
    for _ in range(n % 6):
        p = (fmul(-1, p[1]), fadd(p[0], p[1]))
    return p


def vrotN(n, d):
    for _ in range(n % 6):
        d = (-d[1], d[0] + d[1])
    return d


def cross_cv(d, p):
    """cross(constant d, form-point p) = d0*p1 - d1*p0"""
    return fsub(fmul(d[0], p[1]), fmul(d[1], p[0]))


def is_const(p):
    return all(c[0] == 0 and c[1] == 0 for c in p)


def cval(p):
    return (p[0][2], p[1][2])


def ccross(a, b):
    return a[0] * b[1] - a[1] * b[0]


def proj(p, d):
    """the form t with p = t*d (d a constant unit lattice vector); caller ensures parallel."""
    return fmul(d[0], p[0]) if d[0] != 0 else fmul(d[1], p[1])

# ------------------------------------------------------------------ regions


class Split(Exception):
    def __init__(self, pieces):
        self.pieces = pieces


class Region:
    """{(r,s) in Z^2 : f(r,s) >= 0 for f in cons}.  Must be pointed (contain r>=1, s>=1)."""

    def __init__(self, cons, name=''):
        self.cons = list(dict.fromkeys(cons))
        self.name = name
        self._geo = None

    def add(self, *fs):
        return Region(self.cons + list(fs), self.name)

    def geo(self):
        if self._geo is None:
            C = self.cons
            verts = set()
            for i in range(len(C)):
                for j in range(i + 1, len(C)):
                    a1, b1, c1 = C[i]
                    a2, b2, c2 = C[j]
                    det = a1 * b2 - a2 * b1
                    if det == 0:
                        continue
                    r = Fr(-c1 * b2 + c2 * b1, det)
                    s = Fr(-a1 * c2 + a2 * c1, det)
                    if all(f[0] * r + f[1] * s + f[2] >= 0 for f in C):
                        verts.add((r, s))
            rays = set()
            for f in C:
                for d in ((f[1], -f[0]), (-f[1], f[0])):
                    if d == (0, 0):
                        continue
                    if all(g[0] * d[0] + g[1] * d[1] >= 0 for g in C):
                        rays.add(d)
            self._geo = (verts, rays)
        return self._geo

    def empty(self):
        return not self.geo()[0]

    def minmax(self, f):
        verts, rays = self.geo()
        assert verts, 'empty region'
        vals = [f[0] * r + f[1] * s + f[2] for r, s in verts]
        lin = [f[0] * d[0] + f[1] * d[1] for d in rays]
        lo = None if any(x < 0 for x in lin) else min(vals)
        hi = None if any(x > 0 for x in lin) else max(vals)
        return lo, hi

    def ge0(self, f):
        """True iff f>=0 on R, False iff f<=-1 on R, else Split."""
        lo, hi = self.minmax(f)
        if lo is not None and lo >= 0:
            return True
        if hi is not None and hi < 0:
            return False
        raise Split([self.add(f), self.add(fsub(fmul(-1, f), fconst(1)))])

    def eq0(self, f):
        lo, hi = self.minmax(f)
        if lo is not None and hi is not None and lo == 0 and hi == 0:
            return True
        if (lo is not None and lo > 0) or (hi is not None and hi < 0):
            return False
        if f[0] == 0 and f[1] == 0:
            return f[2] == 0
        raise Split([self.add(fsub(f, fconst(1))), self.add(f, fmul(-1, f)),
                     self.add(fsub(fmul(-1, f), fconst(1)))])

    def le(self, f, g):
        return self.ge0(fsub(g, f))

    def fmin(self, fs):
        best = fs[0]
        for g in fs[1:]:
            if not self.le(best, g):
                best = g
        return best

    def fmax(self, fs):
        best = fs[0]
        for g in fs[1:]:
            if self.le(best, g):
                best = g
        return best

    def sample(self, k=6):
        """a few integer points of the region (for numeric cross-checks)."""
        verts, rays = self.geo()
        out = []
        import itertools
        base = sorted(verts)
        cand = set()
        for (r0, s0) in base:
            for d in list(rays) + [(0, 0)]:
                for t in (0, 1, 2, 3, 5, 8, 13, 21):
                    for dr, ds in itertools.product(range(-2, 3), repeat=2):
                        cand.add((int(r0) + t * d[0] + dr, int(s0) + t * d[1] + ds))
        for (r, s) in sorted(cand, key=lambda z: (z[0] + z[1], z)):
            if all(f[0] * r + f[1] * s + f[2] >= 0 for f in self.cons):
                out.append((r, s))
        # spread
        if len(out) > k:
            step = len(out) / k
            out = [out[int(i * step)] for i in range(k)] + [out[-1]]
        return sorted(set(out))

# ------------------------------------------------------------------ D12 geometry (symbolic)


S_ = F(0, 1, 0)
RS = F(1, 1, 0)
LAB = [list(range(12)), [0] + list(range(11, 0, -1))]


def sym_polys():
    def walkpts(steps):
        p = (ZERO, ZERO)
        out = []
        for length, k in steps:
            out.append(p)
            p = padd(p, pscale(length, vrotN(k, (1, 0))))
        assert p == (ZERO, ZERO)
        return out
    p0 = walkpts([(S_, 0), (RS, 1), (S_, 1), (RS, 2), (S_, 2), (RS, 3),
                  (S_, 3), (RS, 4), (S_, 4), (RS, 5), (S_, 5), (RS, 0)])
    p1 = walkpts([(RS, 0), (S_, 0), (RS, 1), (S_, 1), (RS, 2), (S_, 2),
                  (RS, 3), (S_, 3), (RS, 4), (S_, 4), (RS, 5), (S_, 5)])
    return [p0, p1]


class Geo:
    def __init__(self):
        self.P = sym_polys()
        self.seg = []
        for c in range(2):
            row = []
            P = self.P[c]
            for k in range(12):
                a, b = P[k], P[(k + 1) % 12]
                lengthd = None
                # direction: constant unit vector; length: S_ or RS
                for kk in range(6):
                    d = vrotN(kk, (1, 0))
                    for L in (S_, RS):
                        if padd(a, pscale(L, d)) == b:
                            lengthd = (d, L)
                assert lengthd is not None
                row.append((a, lengthd[0], lengthd[1]))
            self.seg.append(row)
        self.glue = {}
        for c in range(2):
            for k in range(12):
                u, v = LAB[c][k], LAB[c][(k + 1) % 12]
                c2 = 1 - c
                j = next(j for j in range(12) if (LAB[c2][j], LAB[c2][(j + 1) % 12]) == (v, u))
                a, d, L = self.seg[c][k]
                a2, d2, L2 = self.seg[c2][j]
                assert L == L2
                m = next(m for m in range(6) if vrotN(m, d) == (-d2[0], -d2[1]))
                end2 = padd(a2, pscale(L2, d2))
                tau = psub(end2, protN(m, a))
                # check both corners
                assert padd(protN(m, padd(a, pscale(L, d))), tau) == a2
                self.glue[c, k] = (c2, j, m, tau)
        self.cone = [{LAB[c][k]: self.P[c][k] for k in range(12)} for c in range(2)]

    def side_form(self, c, k, p):
        a, d, L = self.seg[c][k]
        return cross_cv(d, psub(p, a))

    def side_t(self, c, k, p):
        a, d, L = self.seg[c][k]
        return proj(psub(p, a), d)

    def mapg(self, c, k, p):
        c2, j, m, tau = self.glue[c, k]
        return padd(protN(m, p), tau)


G = Geo()

# ------------------------------------------------------------------ executor


class Line:
    __slots__ = ('cell', 'Z', 'v', 'I', 'n', 'run', 'pred')

    def __init__(self, cell, Z, v, I, n, run, pred=None):
        self.cell, self.Z, self.v, self.I, self.n, self.run = cell, Z, v, I, n, run
        self.pred = pred   # predecessor of point m is pred + m*v (same chart), or None

    def pt(self, m):
        return padd(self.Z, pscale(m, self.v))


def coincide(R, X, Y):
    """Smallest index at which a point of X equals an earlier point of Y (X from a later run
    than Y, or the same run).  Returns a form or None."""
    best = None
    maps = [None] if X.cell == Y.cell else list(range(12))
    for k in maps:
        if k is None:
            ZY, vY = Y.Z, Y.v
        else:
            ZY = G.mapg(Y.cell, k, Y.Z)
            vY = vrotN(G.glue[Y.cell, k][2], Y.v)
        # constraints on m' (Y parameter): list of (alpha, beta) meaning alpha*m'+beta >= 0
        lows, ups = [ZERO], [Y.n]   # m' >= form, m' <= form
        eqs = []                    # forms that must vanish (no m')
        pins = []                   # m' == form
        if k is not None:
            # Y(m') on segment k of Y.cell: side form == 0, 0 <= t <= L
            a, d, L = G.seg[Y.cell][k]
            f0 = G.side_form(Y.cell, k, Y.Z)
            fc = ccross(d, Y.v)
            t0 = G.side_t(Y.cell, k, Y.Z) if fc == 0 else None
            if fc == 0:
                eqs.append(f0)
                td = d[0] * Y.v[0] if d[0] != 0 else d[1] * Y.v[1]   # dt/dm' = +-1
                # 0 <= t0 + td m' <= L
                if td == 1:
                    lows.append(fmul(-1, t0)); ups.append(fsub(L, t0))
                else:
                    lows.append(fsub(t0, L)); ups.append(t0)
            else:
                # f0 + fc m' == 0  -> m' = -f0/fc  (fc = +-1)
                mp = fmul(-fc, f0)
                pins.append(mp)
                tpt = G.side_t(Y.cell, k, Y.pt(mp))
                if not R.ge0(tpt) or not R.ge0(fsub(L, tpt)):
                    continue
        D = ccross(X.v, vY)
        if D != 0:
            dZ = psub(ZY, X.Z)
            m = fmul(D, cross_cv(vY, dZ)) if False else None
            # m = cross(dZ, vY)/D ; m' = cross(dZ, vX)/D ; cross(dZ, v) = -cross_cv(v, dZ)
            m = fmul(-D, cross_cv(vY, dZ))
            mp = fmul(-D, cross_cv(X.v, dZ))
            ok = all(R.eq0(e) for e in eqs)
            ok = ok and all(R.eq0(fsub(mp, q)) for q in pins)
            ok = ok and R.ge0(m) and R.ge0(fsub(X.n, m))
            ok = ok and all(R.ge0(fsub(mp, lo)) for lo in lows) and all(R.ge0(fsub(up, mp)) for up in ups)
            if not ok:
                continue
            idx = R.fmax([fadd(X.I, fmul(2, m)), fadd(Y.I, fmul(2, mp))])
        else:
            sgn = 1 if vY == X.v else -1
            assert vY == (sgn * X.v[0], sgn * X.v[1])
            dZ = psub(ZY, X.Z)
            if not R.eq0(cross_cv(X.v, dZ)):
                continue
            if not all(R.eq0(e) for e in eqs):
                continue
            delta = proj(dZ, X.v)   # X(m) = Y'(m') iff m = delta + sgn*m'
            # 0 <= delta + sgn m' <= X.n
            if sgn == 1:
                lows = lows + [fmul(-1, delta)]; ups = ups + [fsub(X.n, delta)]
            else:
                lows = lows + [fsub(delta, X.n)]; ups = ups + [delta]
            for q in pins:
                lows = lows + [q]; ups = ups + [q]
            if X.run == Y.run:
                raise AssertionError('parallel coincidence inside one run')
            # X later: index = X.I + 2(delta + sgn m'); minimise
            mp = R.fmax(lows) if sgn == 1 else R.fmin(ups)
            if not (all(R.ge0(fsub(mp, lo)) for lo in lows) and all(R.ge0(fsub(up, mp)) for up in ups)):
                continue
            idx = fadd(X.I, fmul(2, fadd(delta, fmul(sgn, mp))))
        if best is None or R.le(idx, best) is True:
            best = idx
    return best


def cone_hit(R, X):
    """Smallest odd index at which X passes through a cone point (None if none / X even)."""
    assert X.I[0] % 2 == 0 and X.I[1] % 2 == 0
    if X.I[2] % 2 == 0:
        return None
    best = None
    for u, C in G.cone[X.cell].items():
        dC = psub(C, X.Z)
        if not R.eq0(cross_cv(X.v, dC)):
            continue
        m = proj(dC, X.v)
        if not (R.ge0(m) and R.ge0(fsub(X.n, m))):
            continue
        if X.pred is None:
            continue
        pm = padd(X.pred, pscale(m, X.v))
        if any(R.eq0(psub(pm, C2)[0]) and R.eq0(psub(pm, C2)[1]) for C2 in G.cone[X.cell].values()):
            continue   # predecessor is a cone point: not a legal endpoint
        idx = fadd(X.I, fmul(2, m))
        if best is None or not R.le(best, idx):
            best = idx
    return best


def start_triples():
    """The 10 oriented faces at cone label 0 (at the origin of both charts)."""
    out = []
    O = (0, 0)
    for c in range(2):
        for u in range(6):
            d1, d2 = vrotN(u, (1, 0)), vrotN(u + 1, (1, 0))
            # unit triangle (O, d1, d2) inside cell c?
            pts = [pconst(d1), pconst(d2)]
            inside = all(R0.ge0(G.side_form(c, k, p)) for p in pts for k in range(12))
            if inside:
                out.append((c, pconst(O), pconst(d1), pconst(d2)))
                out.append((c, pconst(O), pconst(d2), pconst(d1)))
    return out


R0 = Region([F(1, 0, -1), F(0, 1, -2)])   # r>=1, s>=2 (for the start enumeration only)


def execute(R, start, max_runs=200):
    c, z0, z1, z2 = start
    if any(R.eq0(psub(z1, C)[0]) and R.eq0(psub(z1, C)[1]) for C in G.cone[c].values()):
        return {'kind': 'invalid', 'runs': 0}   # p1 must have degree 6
    T = [z0, z1, z2]
    i = fconst(2)
    lines = []
    best_R = best_E = None
    run = 0

    def add_line(X):
        nonlocal best_R, best_E
        if not R.ge0(X.n):
            return
        for Y in lines:
            idx = coincide(R, X, Y)
            if idx is not None and (best_R is None or R.le(idx, best_R)):
                best_R = idx
        e = cone_hit(R, X)
        if e is not None and R.ge0(fsub(e, fconst(3))) and (best_E is None or R.le(e, best_E)):
            best_E = e
        lines.append(X)

    for j, z in enumerate(T):
        add_line(Line(c, z, (1, 0), fconst(j), ZERO, -1 - j))
    trace = []
    while run < max_runs:
        run += 1
        vv = psub(T[2], T[0])
        assert is_const(vv)
        v = cval(vv)
        M = []
        for z in (T[1], T[2]):
            fs = [G.side_form(c, k, z) for k in range(12) if ccross(G.seg[c][k][1], v) == -1]
            M.append(R.fmin(fs))
        M1, M2 = M
        vM = lambda f: pscale(f, v)
        if R.le(M1, M2):
            add_line(Line(c, padd(T[1], pconst(v)), v, fadd(i, fconst(1)), fsub(M1, fconst(1)), run, T[2]))
            add_line(Line(c, padd(T[2], pconst(v)), v, fadd(i, fconst(2)), fsub(M1, fconst(1)), run,
                          padd(T[1], pconst(v))))
            T = [padd(T[2], vM(fsub(M1, fconst(1)))), padd(T[1], vM(M1)), padd(T[2], vM(M1))]
            i = fadd(i, fmul(2, M1))
        else:
            add_line(Line(c, padd(T[1], pconst(v)), v, fadd(i, fconst(1)), M2, run, T[2]))
            add_line(Line(c, padd(T[2], pconst(v)), v, fadd(i, fconst(2)), fsub(M2, fconst(1)), run,
                          padd(T[1], pconst(v))))
            T = [padd(T[1], vM(M2)), padd(T[2], vM(M2)), padd(T[1], vM(fadd(M2, fconst(1))))]
            i = fadd(i, fadd(fmul(2, M2), fconst(1)))
        trace.append((c, v, i))
        # termination: all events with index <= i are known
        cands = [x for x in (best_R, best_E) if x is not None]
        if cands:
            first = R.fmin(cands)
            if R.le(first, i):
                if best_E is not None and (best_R is None or not R.le(best_R, best_E)):
                    return {'kind': 'pos', 'index': best_E, 'runs': run}
                return {'kind': 'neg', 'index': best_R, 'runs': run,
                        'endpoint': best_E}
        # crossing: edge (T[1],T[2]) lies on a boundary segment of cell c
        nxt = padd(T[1], psub(T[2], T[0]))
        found = None
        for k in range(12):
            a, d, L = G.seg[c][k]
            if not R.ge0(fmul(-1, fadd(G.side_form(c, k, nxt), fconst(1)))):
                continue   # next point not beyond this side's line
            if not (R.eq0(G.side_form(c, k, T[1])) and R.eq0(G.side_form(c, k, T[2]))):
                continue
            ts = [G.side_t(c, k, T[1]), G.side_t(c, k, T[2])]
            if all(R.ge0(t) and R.ge0(fsub(L, t)) for t in ts):
                found = k
                break
        assert found is not None, 'no crossing side'
        c2 = G.glue[c, found][0]
        T = [G.mapg(c, found, z) for z in T]
        c = c2
    return {'kind': 'unfinished', 'runs': run}


def solve(region, start, max_leaves=5000, max_runs=200):
    """Exhaustive split-and-execute.  Returns list of (region, result)."""
    work = [region]
    leaves = []
    while work:
        R = work.pop()
        if R.empty():
            continue
        try:
            res = execute(R, start, max_runs)
        except Split as sp:
            work.extend(sp.pieces)
            continue
        leaves.append((R, res))
        if len(leaves) > max_leaves:
            raise RuntimeError('too many leaves')
    return leaves
