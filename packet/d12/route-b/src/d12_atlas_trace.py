"""Memory-bounded D12 strip tracing on the two original lattice disks."""
from math import gcd
import time
from aligned_atlas import Atlas
from b2 import turn,add,sub,cross
from d12 import signature


class D12Atlas(Atlas):
    def __init__(self,r,s):
        super().__init__(*signature(r,s))
        self.forms=[]
        self.corners=[]
        for cell,poly in zip(self.cells,self.polygons):
            forms=[]
            for i,a in enumerate(poly):
                dx,dy=sub(poly[(i+1)%len(poly)],a)
                g=gcd(dx,dy);dx//=g;dy//=g
                form=(-dy,dx,dy*a[0]-dx*a[1])
                if form not in forms:forms.append(form)
            assert len(forms)==6
            self.forms.append(forms)
            self.corners.append(dict(zip(poly,cell)))

    def inside(self,f,q,den=1):
        x,y=q
        return all(a*x+b*y+c*den>=0 for a,b,c in self.forms[f])

    def key(self,f,q):
        if q in self.corners[f]:return ('v',self.corners[f][q])
        x,y=q
        values=[a*x+b*y+c for a,b,c in self.forms[f]]
        assert min(values)>=0
        if min(values)>0:return ('f',f,x,y)
        return super().key(f,q)

    def step(self,f,tri):
        x,y,z=tri
        nxt=sub(add(y,z),x)
        if self.inside(f,nxt):return f,[y,z,nxt]
        nf,nt,_=super().normalize(f,[y,z,nxt])
        return nf,nt


def trace(atlas,f,tri,*,max_vertices,stop_on_hit=False,deadline=None):
    initial=dict(face=f,triangle=tri)
    chain=[atlas.key(f,p) for p in tri]
    seen=set(chain)
    assert len(seen)==3 and chain[0]==('v',0) and chain[1][0]!='v'
    first_hit=None
    crossings=0
    while len(chain)<=max_vertices:
        if deadline is not None and len(chain)%1024==0:
            assert time.monotonic()<deadline, 'per-case wall cap'
        nf,nt=atlas.step(f,tri)
        crossings+=nf!=f
        key=atlas.key(nf,nt[-1])
        if key in seen:
            return dict(initial=initial,chain=chain,repeat=key,first_hit=first_hit,
                        stop='first-repeat',crossings=crossings)
        chain.append(key);seen.add(key)
        if len(chain)%2==0 and key[0]=='v' and chain[-2][0]!='v' and first_hit is None:
            first_hit=len(chain)
            if stop_on_hit:
                return dict(initial=initial,chain=chain,first_hit=first_hit,
                            stop='positive-witness',crossings=crossings)
        f,tri=nf,nt
    raise AssertionError('distinct vertex bound exceeded')


def maps(r,s):
    L=r+2*s
    return [('R',0,0,1,(s,r+s)),('R',1,1,5,(-L,L)),
            ('J',0,1,5,(-s,s)),('J',1,0,1,(s,0))]


def perm(name,i):return (i+2)%12 if name=='R' else (1-i)%12


def check_symbolic_maps():
    # All coordinates/offsets are affine in r,s by their explicit signature formulas.
    # These three points determine each coefficient including a constant term.
    tests=((1,1),(2,1),(1,2))
    rows=[]
    for name,f,g,k,_ in maps(1,1):
        for label in range(12):
            values=[]
            for r,s in tests:
                cells,polys=signature(r,s)
                offset=next(row[4] for row in maps(r,s) if row[:4]==(name,f,g,k))
                p=polys[f][cells[f].index(label)]
                wanted=polys[g][cells[g].index(perm(name,label))]
                values.append(sub(add(turn(p,k),offset),wanted))
            # Coefficients of r,s,1 reconstructed separately for x and y.
            coeffs=[]
            for axis in (0,1):
                u,v,w=(p[axis] for p in values)
                coeffs.append([v-u,w-u,3*u-v-w])
            assert coeffs==[[0,0,0],[0,0,0]]
            rows.append(dict(generator=name,source_face=f,target_face=g,label=label,
                             rotation=k,difference_affine_coefficients=coeffs))
    reached={0}
    while True:
        new=reached|{perm(name,i) for name in ('R','J') for i in reached}
        if new==reached:break
        reached=new
    assert reached==set(range(12))
    return dict(status='PASS',vertex_correspondences=len(rows),rows=rows,corner_orbit=sorted(reached))
