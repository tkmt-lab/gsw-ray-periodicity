"""Exact local coordinates for aligned signatures; finite derivation aid."""
from itertools import product
from math import gcd
from b2 import add,sub,cross,turn


class Atlas:
    def __init__(self,cells,polygons):
        self.cells,self.polygons=cells,polygons
        owners={(a,cell[(i+1)%len(cell)]):(f,i) for f,cell in enumerate(cells) for i,a in enumerate(cell)}
        self.maps={}
        for (a,b),(f,i) in owners.items():
            g,j=owners[b,a]
            x,y=polygons[f][i],polygons[f][(i+1)%len(cells[f])]
            u,v=polygons[g][(j+1)%len(cells[g])],polygons[g][j]
            k=next(k for k in range(6) if turn(sub(y,x),k)==sub(v,u))
            self.maps[f,i]=g,k,sub(u,turn(x,k))

    def inside(self,f,q,den=1):
        p=self.polygons[f]
        return all(cross(sub(p[(i+1)%len(p)],a),(q[0]-den*a[0],q[1]-den*a[1]))>=0 for i,a in enumerate(p))

    @staticmethod
    def on_segment(q,a,b):
        return cross(sub(b,a),sub(q,a))==0 and all(min(a[k],b[k])<=q[k]<=max(a[k],b[k]) for k in (0,1))

    def normalize(self,f,tri):
        center=tuple(sum(q[k] for q in tri) for k in (0,1))
        if self.inside(f,center,3):
            assert all(self.inside(f,q) for q in tri)
            return f,tri,[]
        poly=self.polygons[f]
        candidates=[i for i,a in enumerate(poly)
                    if sum(self.on_segment(q,a,poly[(i+1)%len(poly)]) for q in tri)==2]
        assert len(candidates)==1,(f,tri,candidates)
        i=candidates[0]
        g,k,z=self.maps[f,i]
        new=[add(turn(q,k),z) for q in tri]
        assert all(self.inside(g,q) for q in new),(f,i,g,new)
        return g,new,[(f,i)]

    def key(self,f,q):
        assert self.inside(f,q)
        poly,cell=self.polygons[f],self.cells[f]
        if q in poly:
            return ('v',cell[poly.index(q)])
        for i,a in enumerate(poly):
            b=poly[(i+1)%len(poly)]
            if not self.on_segment(q,a,b):
                continue
            v=sub(b,a)
            length=gcd(abs(v[0]),abs(v[1]))
            axis=0 if v[0] else 1
            unit=v[axis]//length
            t=(q[axis]-a[axis])//unit
            u,w=cell[i],cell[(i+1)%len(cell)]
            return ('e',u,w,t) if u<w else ('e',w,u,length-t)
        return ('f',f,*q)

    def starts(self,target):
        found={}
        for f,cell in enumerate(self.cells):
            if target not in cell:
                continue
            a,b=self.polygons[f][cell.index(target)]
            for x,y in product(range(a-1,a+2),range(b-1,b+2)):
                for tri in ([(x,y),(x+1,y),(x,y+1)],[(x+1,y),(x+1,y+1),(x,y+1)]):
                    if not all(self.inside(f,q) for q in tri):
                        continue
                    keys=[self.key(f,q) for q in tri]
                    if ('v',target) not in keys:
                        continue
                    i=keys.index(('v',target))
                    tri=tri[i:]+tri[:i]
                    found[tuple(sorted(keys))]=(f,tri)
        assert len(found)==5,(target,found)
        return [(f,t) for f,tri in found.values() for t in (tri,[tri[0],tri[2],tri[1]])]

    def trace(self,f,tri,periodic=False,max_steps=100000):
        chain=[self.key(f,q) for q in tri]
        seen=set(chain)
        first_repeat=None
        rows=[dict(face=f,triangle=tri,route=[])]
        hits=[]
        states={(f,tuple(tri),len(chain)%2):0}
        for _ in range(max_steps):
            x,y,z=tri
            nf,nt,route=self.normalize(f,[y,z,sub(add(y,z),x)])
            key=self.key(nf,nt[-1])
            rows.append(dict(face=nf,triangle=nt,route=route))
            if key in seen and first_repeat is None:
                first_repeat=len(chain)
                if not periodic:
                    return dict(chain=chain,repeat=key,first_repeat=first_repeat,hits=hits,rows=rows)
            if (len(chain)+1)%2==0 and key[0]=='v' and chain[-1][0]!='v':
                hits.append(dict(length=len(chain)+1,endpoint=key,simple=first_repeat is None))
            chain.append(key)
            seen.add(key)
            f,tri=nf,nt
            state=(f,tuple(tri),len(chain)%2)
            if state in states:
                return dict(chain=chain,period_start=states[state],period=len(chain)-3-states[state],
                            first_repeat=first_repeat,hits=hits,rows=rows)
            states[state]=len(chain)-3
        raise AssertionError('orbit limit reached')
