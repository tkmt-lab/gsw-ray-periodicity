"""Exact Fourier--Motzkin infeasibility certificates in a small number of variables."""
from fractions import Fraction as Q
from math import gcd, lcm


def contradiction(forms):
    """Return nonnegative weights whose sum is a strictly negative constant."""
    forms=[tuple(Q(x) for x in f) for f in forms]
    if not forms:
        return None
    dim=len(forms[0])-1
    assert all(len(f)==dim+1 for f in forms)
    rows=[(f,{i:Q(1)}) for i,f in enumerate(forms)]

    def reduced(rows):
        best={}
        for f,w in rows:
            den=lcm(*(x.denominator for x in f[:-1]))
            numer=[int(x*den) for x in f[:-1]]
            g=gcd(*numer)
            if not g:
                if f[-1]<0:
                    ids=sorted(w)
                    proof=dict(indices=ids,weights=[w[i] for i in ids],constant=f[-1])
                    assert all(x>=0 for x in proof['weights'])
                    total=[sum(w[i]*forms[i][j] for i in ids) for j in range(dim+1)]
                    assert total==[Q(0)]*dim+[f[-1]]
                    return None,proof
                continue
            factor=Q(den,g)
            f=tuple(x*factor for x in f)
            w={i:x*factor for i,x in w.items() if x}
            key=f[:-1]
            if key not in best or f[-1]<best[key][0][-1]:
                best[key]=(f,w)
        return list(best.values()),None

    remaining=set(range(dim))
    while True:
        rows,proof=reduced(rows)
        if proof is not None:
            return proof
        if not remaining:
            return None
        axis=min(remaining,key=lambda j:
                 sum(f[j]>0 for f,w in rows)*sum(f[j]<0 for f,w in rows))
        remaining.remove(axis)
        pos=[(f,w) for f,w in rows if f[axis]>0]
        neg=[(f,w) for f,w in rows if f[axis]<0]
        new=[(f,w) for f,w in rows if not f[axis]]
        for f,u in pos:
            for g,v in neg:
                a,b=-g[axis],f[axis]
                h=tuple(a*x+b*y for x,y in zip(f,g))
                w={}
                for i,x in u.items():
                    w[i]=w.get(i,Q(0))+a*x
                for i,x in v.items():
                    w[i]=w.get(i,Q(0))+b*x
                assert h[axis]==0
                new.append((h,w))
        rows=new
