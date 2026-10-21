"""RouteB plane-graph IO and elementary checks, written independently of Study."""
from collections import deque


def read_planar_code(data):
    pos = 0
    while pos < len(data):
        if data[pos:pos + 2] == b">>":
            end = data.index(b"<<", pos) + 2
            header = data[pos:end]
            if header not in (b">>planar_code<<", b">>planar_code le<<"):
                raise ValueError(f"unsupported header {header!r}")
            pos = end
            continue
        n = data[pos]
        pos += 1
        width = 1
        if n == 0:
            width = 2
            n = int.from_bytes(data[pos:pos + 2], "little")
            pos += 2
        if n < 1:
            raise ValueError("empty or truncated graph")
        graph = []
        for _ in range(n):
            neighbors = []
            while True:
                if pos + width > len(data):
                    raise ValueError("truncated adjacency")
                value = int.from_bytes(data[pos:pos + width], "little")
                pos += width
                if value == 0:
                    break
                if not 1 <= value <= n:
                    raise ValueError("vertex out of bounds")
                neighbors.append(value - 1)
            graph.append(tuple(neighbors))
        yield tuple(graph)


def faces(graph):
    """Trace all faces by taking the predecessor of the incoming dart."""
    unused = {(v, w) for v, row in enumerate(graph) for w in row}
    result = []
    while unused:
        start = min(unused)
        u, v = start
        boundary = []
        while True:
            if (u, v) not in unused:
                raise ValueError("invalid rotation system")
            unused.remove((u, v))
            boundary.append(u)
            row = graph[v]
            w = row[(row.index(u) - 1) % len(row)]
            u, v = v, w
            if (u, v) == start:
                break
        result.append(tuple(boundary))
    return result


def validate(graph, dual=True, ipr=False):
    n = len(graph)
    for v, row in enumerate(graph):
        assert row and len(set(row)) == len(row) and v not in row
        assert all(0 <= w < n and v in graph[w] for w in row)
    seen = {0}
    queue = [0]
    for v in queue:
        for w in graph[v]:
            if w not in seen:
                seen.add(w)
                queue.append(w)
    assert len(seen) == n
    fs = faces(graph)
    assert all(len(set(f)) == len(f) for f in fs)
    assert n - sum(map(len, graph)) // 2 + len(fs) == 2
    if dual:
        assert all(len(f) == 3 for f in fs)
        assert all(len(row) in (5, 6) for row in graph)
        assert sum(len(row) == 5 for row in graph) == 12
        if ipr:
            assert all(not (len(graph[v]) == len(graph[w]) == 5)
                       for v, row in enumerate(graph) for w in row)
    else:
        assert all(len(row) == 3 for row in graph)
        assert all(len(f) in (5, 6) for f in fs)
        assert sum(len(f) == 5 for f in fs) == 12
    return fs


def dualize(graph):
    fs = faces(graph)
    owner = {(u, face[(i + 1) % len(face)]): j
             for j, face in enumerate(fs) for i, u in enumerate(face)}
    return tuple(tuple(owner[(face[(i + 1) % len(face)], u)]
                       for i, u in enumerate(face)) for face in fs)


def canonical(graph):
    """Exact unoriented plane-map code via all rooted darts; no hash heuristic."""
    best = None
    degree = min(map(len, graph))
    for root, row in enumerate(graph):
        if len(row) != degree:
            continue
        for first in row:
            for sign in (-1, 1):
                labels = {root: 0}
                queue = deque([(root, first)])
                code = []
                while queue:
                    v, anchor = queue.popleft()
                    neighbors = graph[v]
                    start = neighbors.index(anchor)
                    for i in range(len(neighbors)):
                        w = neighbors[(start + sign * i) % len(neighbors)]
                        if w not in labels:
                            labels[w] = len(labels)
                            queue.append((w, v))
                        code.append(labels[w] + 1)
                    code.append(0)
                candidate = tuple(code)
                if best is None or candidate < best:
                    best = candidate
    return best


def from_oriented_triangles(triangles):
    n = 1 + max(max(t) for t in triangles)
    around = [dict() for _ in range(n)]
    for a, b, c in triangles:
        for u, v, w in ((a, b, c), (b, c, a), (c, a, b)):
            assert v not in around[u]
            around[u][v] = w
    graph = []
    for links in around:
        start = min(links)
        row = [start]
        while links[row[-1]] != start:
            row.append(links[row[-1]])
            assert len(row) <= len(links)
        assert len(row) == len(links)
        graph.append(tuple(row))
    return tuple(graph)


def subdivide(graph, k):
    """GC(k,0): glue barycentric integer points on each original triangular face."""
    assert isinstance(k, int) and k >= 1
    nodes = {((v, k),): v for v in range(len(graph))}
    triangles = []
    for a, b, c in faces(graph):
        def point(x, y):
            key = tuple(sorted((v, w) for v, w in
                               ((a, k - x - y), (b, x), (c, y)) if w))
            if key not in nodes:
                nodes[key] = len(nodes)
            return nodes[key]
        for x in range(k):
            for y in range(k - x):
                triangles.append((point(x, y), point(x + 1, y), point(x, y + 1)))
                if x + y <= k - 2:
                    triangles.append((point(x + 1, y), point(x + 1, y + 1), point(x, y + 1)))
    result = from_oriented_triangles(triangles)
    assert len(result) == k * k * (len(graph) - 2) + 2
    assert len(triangles) == k * k * (2 * len(graph) - 4)
    assert all(len(result[v]) == len(graph[v]) for v in range(len(graph)))
    assert all(len(row) == 6 for row in result[len(graph):])
    return result
