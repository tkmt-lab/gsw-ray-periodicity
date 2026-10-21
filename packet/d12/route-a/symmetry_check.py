"""Symbolic check of the two D12 automorphisms used to reduce all 120 starts to the 10 at cone 0.

sigma1: label u -> u+2 (mod 12), each cell to itself;  sigma2: u -> 1-u (mod 12), cells swapped.
For each cell c we search a rotation m (multiple of 60 deg) and translation tau (affine in r,s)
with  rot^m(P_c[u]) + tau = P_{c'}[phi(u)]  for all 12 corner labels, as identities of affine
forms in (r,s).  Orientation-preserving lattice isometries mapping corners to corners map the
convex cells onto each other and respect the label-determined gluing (a point at distance t from
label u on segment (u,v) goes to the point at distance t from phi(u) on (phi(u),phi(v)) in both
cells), hence induce graph automorphisms.  The group generated acts transitively on the 12 labels.
"""
from symwalk import G, LAB, protN, psub, padd

def find(phi, cellmap):
    res = {}
    for c in range(2):
        c2 = cellmap[c]
        P, Q = G.P[c], G.P[c2]
        pos2 = {LAB[c2][k]: k for k in range(12)}
        found = None
        for m in range(6):
            u0 = LAB[c][0]
            tau = psub(Q[pos2[phi(u0)]], protN(m, P[0]))
            if all(padd(protN(m, P[k]), tau) == Q[pos2[phi(LAB[c][k])]] for k in range(12)):
                found = (m, tau)
        res[c] = found
    return res

s1 = find(lambda u: (u + 2) % 12, {0: 0, 1: 1})
s2 = find(lambda u: (1 - u) % 12, {0: 1, 1: 0})
print('sigma1', s1)
print('sigma2', s2)
orbit = {0}
for _ in range(20):
    orbit |= {(u + 2) % 12 for u in orbit} | {(1 - u) % 12 for u in orbit}
print('orbit of label 0:', sorted(orbit), 'ok:', all(v is not None for v in list(s1.values()) + list(s2.values())) and len(orbit) == 12)
