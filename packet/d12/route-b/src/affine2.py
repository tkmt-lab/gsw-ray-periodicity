"""Exact affine arithmetic and two-dimensional Farkas certificates."""
from fractions import Fraction as Q
from itertools import combinations
from math import gcd,lcm

ZERO=(Q(0),Q(0),Q(0))
P=(Q(1),Q(0),Q(0)); R=(Q(0),Q(1),Q(0))
def const(x): return Q(0),Q(0),Q(x)
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def neg(a): return tuple(-x for x in a)
def sub(a,b): return add(a,neg(b))
def mul(a,n): return tuple(x*n for x in a)
def value(a,p,r): return a[0]*p+a[1]*r+a[2]
def pointadd(a,b): return tuple(add(x,y) for x,y in zip(a,b))
def pointsub(a,b): return tuple(sub(x,y) for x,y in zip(a,b))
def pointscale(a,n): return tuple(mul(x,n) for x in a)
def pointturn(a,k):
    x,y=a
    for _ in range(k%6): x,y=neg(y),add(x,y)
    return x,y
def serialize(x):
    if isinstance(x,Q): return str(x)
    if isinstance(x,dict): return {k:serialize(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [serialize(v) for v in x]
    return x

def normalize(a):
    den=lcm(*(x.denominator for x in a)); out=[int(x*den) for x in a]
    g=gcd(*out)
    return tuple(x//g for x in out) if g else (0,0,0)

def simplify(forms):
    best={}
    for f in forms:
        a,b,c=normalize(f)
        if a==b==0:
            if c<0: return [(Q(0),Q(0),Q(-1))]
            continue
        g=gcd(a,b); key=(a//g,b//g); bound=Q(c,g)
        if key not in best or bound<best[key]: best[key]=bound
    return [(Q(a),Q(b),c) for (a,b),c in sorted(best.items())]

def contradiction(forms):
    """Nonnegative exact weights giving a strictly negative constant, or None."""
    def accept(ids,weights):
        if any(x<0 for x in weights): return None
        total=tuple(sum(w*forms[i][k] for i,w in zip(ids,weights)) for k in range(3))
        if total[0]==total[1]==0 and total[2]<0:
            return dict(indices=list(ids),weights=list(weights),constant=total[2])
    for i,f in enumerate(forms):
        if f[0]==f[1]==0 and f[2]<0: return accept([i],[Q(1)])
    for i,j in combinations(range(len(forms)),2):
        f,g=forms[i],forms[j]
        if f[0]*g[1]!=g[0]*f[1]: continue
        k=0 if f[0] else 1
        if f[k]:
            out=accept([i,j],[Q(-g[k],f[k]),Q(1)])
            if out: return out
    for i,j,k in combinations(range(len(forms)),3):
        f,g,h=forms[i],forms[j],forms[k]
        det=f[0]*g[1]-f[1]*g[0]
        if det:
            x=(-h[0]*g[1]+g[0]*h[1])/det
            y=(-f[0]*h[1]+h[0]*f[1])/det
            if x<0 or y<0: continue
            out=accept([i,j,k],[x,y,Q(1)])
            if out: return out
    return None

def fit(points,values):
    """Fit a form to a full-dimensional or affine-line collection exactly."""
    rows=[[Q(p),Q(r),Q(1),Q(v)] for (p,r),v in zip(points,values)]
    pivot=0; pivots=[]
    # Prefer the constant column: a fixed-parameter sample line should not
    # encode the constant 1 as P/3 merely because all sampled P are 3.
    for col in (2,0,1):
        j=next((j for j in range(pivot,len(rows)) if rows[j][col]),None)
        if j is None: continue
        rows[pivot],rows[j]=rows[j],rows[pivot]
        d=rows[pivot][col]; rows[pivot]=[x/d for x in rows[pivot]]
        for j in range(len(rows)):
            if j!=pivot:
                d=rows[j][col]
                if d: rows[j]=[x-d*y for x,y in zip(rows[j],rows[pivot])]
        pivots.append(col); pivot+=1
    if any(all(x==0 for x in row[:3]) and row[3] for row in rows): return None
    out=[Q(0)]*3
    for row,col in zip(rows,pivots): out[col]=row[3]
    assert all(value(out,p,r)==v for (p,r),v in zip(points,values))
    equalities=[]
    for col in range(3):
        if col in pivots: continue
        e=[Q(0)]*3; e[col]=1
        for row,k in zip(rows,pivots): e[k]=-row[col]
        equalities.append(tuple(e))
    return tuple(out),equalities
