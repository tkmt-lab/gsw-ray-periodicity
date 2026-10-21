"""Graver D12: two regular hexagonal disks with offset edge subdivisions."""
from aligned_surface import construct as glue
from b2 import add, turn


def signature(r,s):
    assert r>=1 and s>=1
    cells=[list(range(12)),[0]+list(range(11,0,-1))]
    polygons=[]
    for side in (0,1):
        poly=[(0,0)]
        lengths=(s,r+s)*6 if side==0 else (r+s,s)*6
        for j,length in enumerate(lengths):
            k=(j+1)//2 if side==0 else j//2
            poly.append(add(poly[-1],turn((length,0),k)))
        assert poly.pop()==(0,0)
        polygons.append(poly)
    return cells,polygons


def construct(r,s):
    graph,counts=glue(*signature(r,s))
    assert counts==[6*(r+2*s)**2]*2
    assert 2*len(graph)-4==12*(r+2*s)**2
    return graph
