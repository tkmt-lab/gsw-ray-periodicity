#!/bin/sh
# Reproduce every certificate of the D12 classification (route-a, 2026-10-19).
# Pure Python 3, no dependencies.  Peak RSS of each step < 100 MB; total ~5 min (+ ~35 min for W10..W24).
set -e
cd "$(dirname "$0")"
python3 validate_mirror.py | tail -1                       # lazy graph == Lean-spec mirror (30 graphs)
python3 symmetry_check.py | tail -1                        # D6 automorphisms: 120 starts -> 10 at cone 0
python3 prove_regions.py cert-main.json main               # regions A-F (r>=3)
python3 prove_regions.py cert-w1-9.json wedges 1 9         # W1..W9 (r>=3, r+2 <= s <= 10r+1)
python3 cylinders.py cylinders-cert.json                   # s >= 10r, r>=3: congruence starts, necessity
python3 positivity.py cylinders-cert.json positivity-cert.json   # ... and sufficiency with full history
python3 cylinders_check.py cylinders-cert.json             # numeric cross-check of the cylinder leaves
python3 arith_check.py cylinders-cert.json                 # exit window <-> congruence (brute force)
D12_PIN_R=2 python3 cylinders.py cylinders-cert-r2.json    # r=2, s>=20
D12_PIN_R=2 python3 positivity.py cylinders-cert-r2.json positivity-cert-r2.json
python3 -c "import sys; sys.path.insert(0,'.'); from prove_regions import region_result; from symwalk import F; import json; json.dump([region_result([F(1,0,-p),F(-1,0,p),F(0,1,-2)],'G%d: r=%d, s>=2 (6 non-cylinder starts)'%(p,p),starts=[1,2,5,6,7,9],max_runs=60) for p in (1,2)], open('cert-rows12.json','w'), indent=0)"
# finite part: all (r,s) with r,s<=40 decided exhaustively (all 120 starts) -> discovery-r1-40-s1-40.jsonl.gz
# (python3 sweep.py OUT.jsonl 1 40 1 40 4 ; ~100 s with 4 workers)
D12_PIN_R=2 python3 -c "import sys; sys.path.insert(0,'.'); from cylinders_check import main; print(main('cylinders-cert-r2.json', [(2, s) for s in range(20, 61)]))"
D12_PIN_R=2 python3 -c "import sys; sys.path.insert(0,'.'); from arith_check import main; print(main('cylinders-cert-r2.json', [(2, s) for s in range(20, 400)]))"
