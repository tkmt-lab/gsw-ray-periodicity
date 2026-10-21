"""Check d12walk.D12 (lazy) against the Lean-spec mirror Surface (eager) for small (r,s):
same partition of sites into vertices and same edge set."""
import json
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'atlas'))
import reference_model as M  # noqa: E402
from d12walk import D12  # noqa: E402

out = []
for r in range(1, 7):
    for s in range(1, 6):
        lab, poly = M.d12_sig(r, s)
        S = M.Surface(lab, poly)
        D = D12(r, s)
        assert D.P == poly and D.lab == lab
        to_mine = {}
        ok = True
        for k, (f, z) in enumerate(S.sites):
            v = D.canon(f, z)
            if to_mine.setdefault(S.cls[k], v) != v:
                ok = False
        ok = ok and len(set(to_mine.values())) == S.V
        for c in range(S.V):
            ok = ok and {to_mine[d] for d in S.adj[c]} == D.nbr(to_mine[c])
        out.append({'r': r, 's': s, 'V': S.V, 'same_graph': ok})
        print(r, s, S.V, ok, flush=True)
print(json.dumps({'all_same': all(x['same_graph'] for x in out), 'cases': len(out)}))
