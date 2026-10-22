import Formal.Claude2AlignedSpec

/-!
# Specification of Graver's D12(r,s) in the aligned-family style

Written by Claude (statement writer) on 2026-10-21, before any proof.

The D12 data `d12Lab`, `d12Poly`, `d12Sig`, `d12Graph` (namespace `Claude2Aligned`) already
exist in `Claude2AlignedSpec.lean` (written 2026-10-19), so this file does not define them again
(a second definition under the same names would clash with every file importing both). Importing
`Formal.Claude7D12Spec` gives exactly those definitions. They were re-derived on 2026-10-21 from
the verification team's independent construction (R004 `d12.py`, read-only) and agree with it
literally:
- labels: cell 0 carries `0, 1, …, 11`, cell 1 carries `0, 11, 10, …, 1`;
- cell 0: side `j` (from label `j` to `j + 1`) has length `s` for even `j` and `r + s` for odd
  `j`, direction `rotN ((j + 1) / 2) (1, 0)` (R004 `k = (j+1)//2`);
- cell 1: side `j` has length `r + s` for even `j` and `s` for odd `j`, direction
  `rotN (j / 2) (1, 0)` (R004 `k = j//2`).
So each cell is a regular hexagon of side `L = r + 2s`, each side cut at a label into `s` and
`r + s` (in opposite orders on the two cells).

Parameters: `r, s` are the second paper's D12 parameters (`sec:d12-classification`, `L = r + 2s`)
and R004's names. Check: twice the total area is `2 · 6 (r + 2s)² = 12r² + 48rs + 48s²`, the
paper's appendix row `D12 & s,r+s & 12r²+48rs+48s²` (not symmetric in `r, s`, so the order is
fixed). The paper's chart description (`H_L`, corners `(0,0),(L,0),(L,L),(0,2L),(-L,2L),(-L,L)`,
marks at distance `r + s` from each initial corner, labels `(11,0,1,…,10)` and `(0,11,…,1)`)
is cell 1 literally and cell 0 translated by `(r + s, 0)`.

The mirror `studies/R002/analysis/2026-10-22-claude-d12-bridge/d12_mirror.py` checks this
Lean-literal surface against R004's construction and the paper's classification.
-/
