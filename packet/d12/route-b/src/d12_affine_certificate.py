"""Univariate affine proof checker, generalized from our earlier two-ray checker.

Each pair is (coefficient of t, constant); integer t >= LOWER.
"""
from fractions import Fraction
from itertools import combinations,product
from math import ceil,floor
from pathlib import Path
import hashlib,json,resource,signal,time
from aligned_atlas import Atlas
from d12 import signature
from b2 import turn,add,sub

ROOT=Path(__file__).resolve().parents[3]
ZERO=(0,0)
RECORDS=[]
LOWER=1


def fadd(a,b):return (a[0]+b[0],a[1]+b[1])
def scale(a,k):return (a[0]*k,a[1]*k)
def fsub(a,b):return fadd(a,scale(b,-1))
def ev(a,s):return a[0]*s+a[1]
def constant(n):return (0,n)
def vadd(a,b):return tuple(fadd(x,y) for x,y in zip(a,b))
def vsub(a,b):return tuple(fsub(x,y) for x,y in zip(a,b))
def along(d,t):return tuple(scale(t,k) for k in d)
def translate(a,d):return vadd(a,tuple(constant(k) for k in d))
def vev(a,s):return tuple(ev(t,s) for t in a)
def rotate(a,k):
    return tuple(zip(turn((a[0][0],a[1][0]),k),turn((a[0][1],a[1][1]),k)))
def det(a,b):return a[0]*b[1]-a[1]*b[0]
def crossfd(a,d):return fsub(scale(a[0],d[1]),scale(a[1],d[0]))
def norm(d):return d[0]*d[0]+d[0]*d[1]+d[1]*d[1]
def ge(a):return a[0]>=0 and ev(a,LOWER)>=0
def eq(a):return a==ZERO


def feasible(inequalities,equalities=()):
    """Least integer t>=LOWER satisfying affine inequalities >=0 and equalities =0."""
    lo,hi=Fraction(LOWER),None
    for a,b in equalities:
        if a==0:
            if b:return None
        else:
            root=Fraction(-b,a)
            lo=max(lo,root);hi=root if hi is None else min(hi,root)
    for a,b in inequalities:
        if a>0:lo=max(lo,Fraction(-b,a))
        elif a<0:
            bound=Fraction(-b,a);hi=bound if hi is None else min(hi,bound)
        elif b<0:return None
    first=ceil(lo)
    return first if hi is None or first<=floor(hi) else None


def empty(label,inequalities,equalities=()):
    witness=feasible(inequalities,equalities)
    RECORDS.append(dict(label=label,inequalities=inequalities,equalities=equalities,witness=witness))
    assert witness is None,(label,witness)


def positive(form,label):
    RECORDS.append(dict(label=label,nonnegative=form))
    assert ge(form),(label,form)


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
        assert r['length'][0]%2==0
        out.append(r);base=fadd(base,r['length'])
    return out,base


def point(run,j):
    assert j[0]%2==0
    parity=j[1]%2;t=(j[0]//2,(j[1]-parity)//2)
    return translate(vadd(run['a'],along(run['d'],t)),run['e'] if parity else (0,0))


def rows(runs):
    out=[]
    for i,r in enumerate(runs):
        for parity in (0,1):
            out.append(dict(face=r['face'],a=translate(r['a'],r['e'] if parity else (0,0)),d=r['d'],
                            lo=ZERO,hi=(r['length'][0]//2,(r['length'][1]-1-parity)//2),
                            global_parity=(r['base'][1]+parity)%2,block=i,parity=parity))
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


def check_starts(atlas):
    accepted=[]
    for f in (0,1):
        for x,y in product(range(-1,2),repeat=2):
            for tri in (((x,y),(x+1,y),(x,y+1)),((x+1,y),(x+1,y+1),(x,y+1))):
                if (0,0) not in tri:continue
                forms=[form for p in tri for form in halfplanes(atlas,f,tuple(constant(k) for k in p))]
                if all(ge(form) for form in forms):accepted.append((f,frozenset(tri)))
                else:assert any(ge(fsub(scale(form,-1),constant(1))) for form in forms)
    assert len(accepted)==5 and len(set(accepted))==5
    return accepted


def check_case(case):
    global LOWER
    LOWER=case['lower']
    atlas=symbolic_atlas(tuple(case['r']),tuple(case['s']));runs,total=convert(case);rr=rows(runs)
    starts=check_starts(atlas)
    first=runs[0];tri=[point(first,constant(i)) for i in range(3)]
    assert all(all(a==0 for a,b in p) for p in tri)
    assert (first['face'],frozenset(vev(p,LOWER) for p in tri)) in starts
    old=Atlas(*signature(ev(case['r'],LOWER),ev(case['s'],LOWER))).starts(0)[case['start']]
    assert (first['face'],[vev(p,LOWER) for p in tri])==old
    for i,r in enumerate(runs):
        positive(fsub(r['length'],constant(3)),f'length-{i}')
        assert norm(r['d'])==norm(r['e'])==norm(sub(r['d'],r['e']))==1
    for i,row in enumerate(rr):
        for which in ('lo','hi'):
            p=vadd(row['a'],along(row['d'],row[which]))
            for j,form in enumerate(halfplanes(atlas,row['face'],p)):
                positive(form,f'inside-{i}-{which}-{j}')
    for i,(a,b) in enumerate(zip(runs,runs[1:])):
        tail=[point(a,fsub(a['length'],constant(j))) for j in (3,2,1)]
        predicted=vsub(vadd(tail[1],tail[2]),tail[0]);found=False
        poly=atlas['polygons'][a['face']]
        for edge,p in enumerate(poly):
            g,k,z=atlas['maps'][a['face'],edge]
            if g!=b['face'] or not all(on_edge(p,poly[(edge+1)%12],q) for q in tail[1:]):continue
            moved=[vadd(rotate(q,k),z) for q in tail[1:]]
            q0=point(b,ZERO);q1=point(b,constant(1));q2=point(b,constant(2))
            if vadd(rotate(predicted,k),z)!=q0:continue
            assert vsub(vadd(moved[1],q0),moved[0])==q1
            assert vsub(vadd(q0,q1),moved[1])==q2
            found=True;break
        assert found,('transition',i)
    if case['stop']=='repeat':
        for i,row in enumerate(rr):
            if row['global_parity']!=1:continue
            for j,p in enumerate(atlas['polygons'][row['face']]):
                empty(f'odd-corner-{i}-{j}',*hit_point(row,p))
        target=tuple(case['repeat_index']);found=False
        for r in runs:
            local=fsub(target,r['base'])
            if ge(local) and ge(fsub(fsub(r['length'],constant(1)),local)):
                end=point(runs[-1],fsub(runs[-1]['length'],constant(1)))
                assert same_vertex(atlas,r['face'],point(r,local),runs[-1]['face'],end)
                assert ge(fsub(fsub(total,constant(2)),target))
                found=True;break
        assert found
    else:
        assert total[0]%2==total[1]%2==0
        end=point(runs[-1],fsub(runs[-1]['length'],constant(1)))
        assert tri[0]==(ZERO,ZERO) and end in atlas['polygons'][runs[-1]['face']]
        # Literal Definition 1(a) only requires vertices 1 and -2 to be hexagons.
        # Interior pentagons at other indices are allowed.
        for label,run,index in [('second',runs[0],constant(1)),
                                ('penultimate',runs[-1],fsub(runs[-1]['length'],constant(2)))]:
            p=point(run,index)
            for j,q in enumerate(atlas['polygons'][run['face']]):
                empty(f'{label}-corner-{j}',[],vsub(p,q))
        for (i,p),(j,q) in combinations(enumerate(rr),2):
            if p['face']==q['face']:
                empty(f'same-face-{i}-{j}',*same_face_intersection(p,q))
            else:
                poly=atlas['polygons'][p['face']]
                for edge,a in enumerate(poly):
                    g,k,z=atlas['maps'][p['face'],edge];assert g==q['face']
                    converted=dict(q,a=rotate(vsub(q['a'],z),-k),d=turn(q['d'],-k))
                    empty(f'glued-edge-{i}-{j}-{edge}',*edge_intersection(p,converted,a,poly[(edge+1)%12]))
    return dict(name=case['name'],start=case['start'],status='PASS',blocks=len(runs),total_vertices=total)


def replay(case,s):
    atlas=Atlas(*signature(ev(case['r'],s),ev(case['s'],s)));runs,_=convert(case)
    points=[]
    for run in runs:
        for j in range(ev(run['length'],s)):
            points.append(atlas.key(run['face'],vev(point(run,constant(j)),s)))
    f,tri=atlas.starts(0)[case['start']];seen={};observed=[]
    for i,key in enumerate(points):
        if i<3:actual=atlas.key(f,tri[i])
        else:
            f,tri,_=atlas.normalize(f,[tri[1],tri[2],sub(add(tri[1],tri[2]),tri[0])])
            actual=atlas.key(f,tri[-1])
        assert key==actual
        if case['stop']=='positive':assert key not in seen
        if case['stop']=='repeat' and i%2==1:assert key[0]!='v'
        observed.append(key);seen.setdefault(key,i)
    if case['stop']=='repeat':assert points[-1]==points[ev(tuple(case['repeat_index']),s)]
    else:assert points[0][0]==points[-1][0]=='v' and all(points[i][0]!='v' for i in (1,-2))
    raw=json.dumps(observed,separators=(',',':')).encode()
    return dict(t=s,name=case['name'],start=case['start'],vertices=len(points),sha256=hashlib.sha256(raw).hexdigest())
