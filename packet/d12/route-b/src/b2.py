"""Independent Graver B2 from eight triangles and six lattice rectangles."""
from itertools import product
from graphs import from_oriented_triangles


def turn(v,k):
    x,y=v
    for _ in range(k%6): x,y=-y,x+y
    return x,y


def cross(a,b): return a[0]*b[1]-a[1]*b[0]
def sub(a,b): return a[0]-b[0],a[1]-b[1]
def add(a,b): return a[0]+b[0],a[1]+b[1]


def construct(p,r):
    assert p>=1 and r>=1
    tetra=[(0,2,1),(0,1,3),(0,3,2),(1,2,3)]
    links={a:{} for a in range(4)}
    for a,b,c in tetra:
        for x,y,z in ((a,b,c),(b,c,a),(c,a,b)): links[x][y]=z
    small=[]
    for a,m in links.items():
        b=min(m); small.append([(a,b),(a,m[b]),(a,m[m[b]])])
    large=[[(a,b),(b,c),(c,a)] for a,b,c in tetra]
    prev_small={v:face[i-1] for face in small for i,v in enumerate(face)}
    prev_large={v:face[i-1] for face in large for i,v in enumerate(face)}
    used=set(); rectangles=[]
    for v,w in prev_small.items():
        if (v,w) in used: continue
        cell=[v,w,prev_large[w],prev_small[prev_large[w]]]
        assert prev_large[cell[-1]]==v and len(set(cell))==4
        rectangles.append(cell)
        used.add((cell[0],cell[1])); used.add((cell[2],cell[3]))
    assert len(rectangles)==6
    cells=small+large+rectangles
    coords=([(0,0),(r,0),(0,r)] for _ in range(4))
    polygons=list(coords)+[[(0,0),(p,p),(-p,2*p)] for _ in range(4)]
    # First edge has length r along (1,-1), second has length sqrt(3)*p.
    polygons += [[(0,0),(r,-r),(r+p,-r+p),(p,p)] for _ in rectangles]
    edge_owner={}
    for f,cell in enumerate(cells):
        for i,a in enumerate(cell):
            b=cell[(i+1)%len(cell)]
            assert (a,b) not in edge_owner
            edge_owner[a,b]=(f,i)
    assert all((b,a) in edge_owner for a,b in edge_owner)
    assert len(edge_owner)==48

    def inside(f,q,den=1):
        poly=polygons[f]
        return all(cross(sub(poly[(i+1)%len(poly)],a),
                         (q[0]-den*a[0],q[1]-den*a[1]))>=0 for i,a in enumerate(poly))

    # Rotation/translation sending coordinates across each glued edge.
    transitions={}
    for (a,b),(f,i) in edge_owner.items():
        g,j=edge_owner[b,a]
        av=polygons[f][i]; bv=polygons[f][(i+1)%len(cells[f])]
        gu=polygons[g][(j+1)%len(cells[g])]; gv=polygons[g][j]
        vec=sub(bv,av); target=sub(gv,gu)
        k=next(k for k in range(6) if turn(vec,k)==target)
        transitions[f,i]=(g,k,sub(gu,turn(av,k)))

    def local_key(f,q):
        poly=polygons[f]; cell=cells[f]
        if q in poly: return ('v',cell[poly.index(q)])
        for i,a in enumerate(poly):
            b=poly[(i+1)%len(poly)]; v=sub(b,a); delta=sub(q,a)
            if cross(v,delta)!=0: continue
            if not (min(a[0],b[0])<=q[0]<=max(a[0],b[0]) and
                    min(a[1],b[1])<=q[1]<=max(a[1],b[1])): continue
            # Every signature edge is an integer multiple of a primitive vector.
            from math import gcd
            length=gcd(abs(v[0]),abs(v[1]))
            unit=(v[0]//length,v[1]//length)
            axis=0 if unit[0] else 1
            assert delta[axis]%unit[axis]==0
            t=delta[axis]//unit[axis]
            u,w=cell[i],cell[(i+1)%len(cell)]
            return ('e',u,w,t) if u<w else ('e',w,u,length-t)
        assert inside(f,q)
        return ('f',f,q[0],q[1])

    def key(f,q):
        if inside(f,q): return local_key(f,q)
        poly=polygons[f]
        bad=[i for i,a in enumerate(poly)
             if cross(sub(poly[(i+1)%len(poly)],a),sub(q,a))<0]
        assert len(bad)==1,(p,r,f,q,bad)
        g,k,offset=transitions[f,bad[0]]
        transformed=add(turn(q,k),offset)
        assert inside(g,transformed),(p,r,f,q,g,transformed)
        return local_key(g,transformed)

    vertex_ids={}; triangles={}
    for f,poly in enumerate(polygons):
        xs=range(min(x for x,y in poly)-1,max(x for x,y in poly)+2)
        ys=range(min(y for x,y in poly)-1,max(y for x,y in poly)+2)
        for x,y in product(xs,ys):
            for triple in (((x,y),(x+1,y),(x,y+1)),
                           ((x+1,y),(x+1,y+1),(x,y+1))):
                center=(sum(a for a,b in triple),sum(b for a,b in triple))
                if not inside(f,center,3): continue
                ids=[]
                for q in triple:
                    k=key(f,q)
                    if k not in vertex_ids: vertex_ids[k]=len(vertex_ids)
                    ids.append(vertex_ids[k])
                assert len(set(ids))==3
                oriented=min(tuple(ids[i:]+ids[:i]) for i in range(3))
                unordered=tuple(sorted(ids))
                if unordered in triangles: assert triangles[unordered]==oriented
                triangles[unordered]=oriented
    expected=12*p*p+24*p*r+4*r*r
    assert len(triangles)==expected,(p,r,len(triangles),expected)
    graph=from_oriented_triangles(list(triangles.values()))
    assert 2*len(graph)-4==expected
    return graph
