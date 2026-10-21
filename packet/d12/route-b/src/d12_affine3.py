"""Three-variable D12 affine geometry and exact Farkas certificates.

Generalized locally from our one-variable checker. Forms are (r,s,h,constant).
"""
from fractions import Fraction
from itertools import combinations,product
from math import gcd
from b2 import turn,add,sub
from affine2 import serialize
from linear_farkas import contradiction

ZERO=(0,0,0,0)
DOMAIN=[]
RECORDS=[]


def fadd(a,b):return tuple(x+y for x,y in zip(a,b))
def scale(a,k):return tuple(x*k for x in a)
def fsub(a,b):return fadd(a,scale(b,-1))
def ev(a,r,s,h):return a[0]*r+a[1]*s+a[2]*h+a[3]
def constant(n):return (0,0,0,n)
def vadd(a,b):return tuple(fadd(x,y) for x,y in zip(a,b))
def vsub(a,b):return tuple(fsub(x,y) for x,y in zip(a,b))
def along(d,t):return tuple(scale(t,k) for k in d)
def translate(a,d):return vadd(a,tuple(constant(k) for k in d))
def vev(a,r,s,h):return tuple(ev(t,r,s,h) for t in a)
def rotate(a,k):return tuple(zip(*(turn((x,y),k) for x,y in zip(*a))))
def det(a,b):return a[0]*b[1]-a[1]*b[0]
def crossfd(a,d):return fsub(scale(a[0],d[1]),scale(a[1],d[0]))
def norm(d):return d[0]*d[0]+d[0]*d[1]+d[1]*d[1]
def ge(a):return contradiction(DOMAIN+[fsub(scale(a,-1),constant(1))]) is not None
def eq(a):return a==ZERO


def empty(label,inequalities,equalities=()):
    forms=DOMAIN+list(inequalities)+[z for e in equalities for z in (e,scale(e,-1))]
    proof=contradiction(forms)
    assert proof is not None,(label,forms)
    RECORDS.append(dict(label=label,forms=forms,**proof))


def positive(form,label):
    empty(label,[fsub(scale(form,-1),constant(1))])


def unit_segment(a,b):
    v=vsub(b,a)
    for k in range(6):
        h=turn((1,0),k);axis=0 if h[0] else 1
        length=scale(v[axis],h[axis])
        if v==along(h,length) and ge(fsub(length,constant(1))):return h,length
    raise AssertionError(('non-unit-direction edge',a,b))


def symbolic_atlas(r,s):
    cells=[list(range(12)),[0]+list(range(11,0,-1))]
    polygons=[]
    for side in (0,1):
        p=[(ZERO,ZERO)]
        for j in range(12):
            length=s if (j%2==0)==(side==0) else fadd(r,s)
            k=(j+1)//2 if side==0 else j//2
            p.append(vadd(p[-1],along(turn((1,0),k),length)))
        assert p.pop()==(ZERO,ZERO)
        polygons.append(p)
    maps={}
    for f in (0,1):
        for i,u in enumerate(cells[f]):
            v=cells[f][(i+1)%12];g=1-f;j=cells[g].index(v)
            assert cells[g][(j+1)%12]==u
            a,b=polygons[f][i],polygons[f][(i+1)%12]
            x,y=polygons[g][(j+1)%12],polygons[g][j]
            k=next(k for k in range(6) if rotate(vsub(b,a),k)==vsub(y,x))
            maps[f,i]=(g,k,vsub(x,rotate(a,k)))
    return dict(cells=cells,polygons=polygons,maps=maps)


def halfplanes(atlas,f,p):
    poly=atlas['polygons'][f]
    return [scale(crossfd(vsub(p,a),unit_segment(a,poly[(i+1)%12])[0]),-1)
            for i,a in enumerate(poly)]


def on_edge(a,b,p):
    h,length=unit_segment(a,b);delta=vsub(p,a);axis=0 if h[0] else 1
    t=scale(delta[axis],h[axis])
    return eq(crossfd(delta,h)) and ge(t) and ge(fsub(length,t))


def convert(case):
    out=[];base=ZERO
    for run in case['runs']:
        r=dict(face=run['face'],a=tuple(map(tuple,run['a'])),d=tuple(run['d']),
               e=tuple(run['e']),length=tuple(run['length']),base=base)
        assert all(x%2==0 for x in r['length'][:-1])
        out.append(r);base=fadd(base,r['length'])
    return out,base


def point(run,j):
    assert all(x%2==0 for x in j[:-1])
    parity=j[-1]%2;t=tuple(x//2 for x in j[:-1])+((j[-1]-parity)//2,)
    return translate(vadd(run['a'],along(run['d'],t)),run['e'] if parity else (0,0))


def rows(runs):
    out=[]
    for i,r in enumerate(runs):
        for parity in (0,1):
            out.append(dict(face=r['face'],a=translate(r['a'],r['e'] if parity else (0,0)),d=r['d'],
                            lo=ZERO,hi=tuple(x//2 for x in r['length'][:-1])+((r['length'][-1]-1-parity)//2,),
                            global_parity=(r['base'][-1]+parity)%2,block=i,parity=parity))
    return out


def bounds(row,u):return [fsub(u,row['lo']),fsub(row['hi'],u)]


def hit_point(row,p):
    axis=0 if row['d'][0] else 1;delta=vsub(p,row['a'])
    u=scale(delta[axis],row['d'][axis])
    return bounds(row,u),[crossfd(delta,row['d'])]


def overlap_intervals(intervals):
    return [fsub(hi,lo) for _,hi in intervals for lo,_ in intervals]


def same_face_intersection(p,q):
    delta=vsub(q['a'],p['a']);d,e=p['d'],q['d'];D=det(d,e)
    if D:
        assert abs(D)==1
        u=scale(crossfd(delta,e),D);v=scale(crossfd(delta,d),D)
        return bounds(p,u)+bounds(q,v),[]
    axis=0 if d[0] else 1;offset=scale(delta[axis],d[axis]);sign=e[axis]*d[axis]
    qends=[fadd(offset,scale(q[t],sign)) for t in ('lo','hi')]
    if sign<0:qends.reverse()
    return overlap_intervals([(p['lo'],p['hi']),qends]),[crossfd(delta,d)]


def edge_intersection(p,q,a,b):
    """Both rows in the first face coordinates, constrained to one glued edge."""
    h,L=unit_segment(a,b);d,e=p['d'],q['d'];axis=0 if h[0] else 1
    D=det(d,e)
    if D:
        assert abs(D)==1;delta=vsub(q['a'],p['a'])
        u=scale(crossfd(delta,e),D);v=scale(crossfd(delta,d),D)
        x=vsub(vadd(p['a'],along(d,u)),a);w=scale(x[axis],h[axis])
        return bounds(p,u)+bounds(q,v)+[w,fsub(L,w)],[crossfd(x,h)]
    if det(d,h):
        D=det(d,h);assert abs(D)==1
        u=scale(crossfd(vsub(a,p['a']),h),D)
        x=vadd(p['a'],along(d,u));ax=0 if e[0] else 1
        v=scale(vsub(x,q['a'])[ax],e[ax]);w=scale(vsub(x,a)[axis],h[axis])
        return bounds(p,u)+bounds(q,v)+[w,fsub(L,w)],[crossfd(vsub(x,q['a']),e)]
    intervals=[];equalities=[]
    for r in (p,q):
        x=vsub(r['a'],a);equalities.append(crossfd(x,h))
        offset=scale(x[axis],h[axis]);sign=r['d'][axis]*h[axis]
        ends=[fadd(offset,scale(r[t],sign)) for t in ('lo','hi')]
        if sign<0:ends.reverse()
        intervals.append(ends)
    return overlap_intervals(intervals+[(ZERO,L)]),equalities


def same_vertex(atlas,f,p,g,q):
    if f==g:return p==q
    poly=atlas['polygons'][f]
    for i,a in enumerate(poly):
        target,k,z=atlas['maps'][f,i]
        if target==g and on_edge(a,poly[(i+1)%12],p) and vadd(rotate(p,k),z)==q:return True
    return False
