"""Triangulate and glue convex polygons whose edges follow the triangular lattice."""
from itertools import product
from math import gcd
from b2 import cross, sub
from graphs import from_oriented_triangles


def construct(cells, polygons, *, with_keys=False):
    assert len(cells) == len(polygons)
    owners = {}
    for f, (cell, poly) in enumerate(zip(cells, polygons)):
        assert len(cell) == len(poly) and len(set(cell)) == len(cell)
        for i, a in enumerate(cell):
            b = cell[(i+1) % len(cell)]
            vec = sub(poly[(i+1) % len(poly)], poly[i])
            length = gcd(abs(vec[0]), abs(vec[1]))
            assert length > 0
            assert (vec[0]//length, vec[1]//length) in (
                (1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1))
            assert (a, b) not in owners
            owners[a, b] = (f, length)
    assert all((b, a) in owners and owners[b, a][1] == length
               for (a, b), (f, length) in owners.items())
    vertices = {}
    triangles = []
    cell_counts = []
    for f, (cell, poly) in enumerate(zip(cells, polygons)):
        boundary = {}
        for i, a in enumerate(poly):
            b = poly[(i+1) % len(poly)]
            vec = sub(b, a)
            length = gcd(abs(vec[0]), abs(vec[1]))
            dx, dy = vec[0]//length, vec[1]//length
            u, v = cell[i], cell[(i+1) % len(cell)]
            boundary[a] = ('v', u)
            for t in range(1, length):
                key = ('e', u, v, t) if u < v else ('e', v, u, length-t)
                boundary[a[0]+t*dx, a[1]+t*dy] = key
        xs = range(min(x for x, y in poly), max(x for x, y in poly)+1)
        ys = range(min(y for x, y in poly), max(y for x, y in poly)+1)
        points = {}
        for q in product(xs, ys):
            if any(cross(sub(poly[(i+1) % len(poly)], a), sub(q, a)) < 0
                   for i, a in enumerate(poly)):
                continue
            key = boundary.get(q, ('f', f, *q))
            if key not in vertices:
                vertices[key] = len(vertices)
            points[q] = vertices[key]
        count = 0
        for x, y in product(xs, ys):
            for triple in (((x, y), (x+1, y), (x, y+1)),
                           ((x+1, y), (x+1, y+1), (x, y+1))):
                if all(q in points for q in triple):
                    triangles.append(tuple(points[q] for q in triple))
                    count += 1
        area2 = sum(cross(a, poly[(i+1) % len(poly)]) for i, a in enumerate(poly))
        assert count == area2 > 0, (f, count, area2)
        cell_counts.append(count)
    graph = from_oriented_triangles(triangles)
    if with_keys:
        return graph, cell_counts, vertices
    return graph, cell_counts
