import Formal.Claude2AlignedSpec

/-!
# Specification of Graver's D14(r,s) in the aligned-family style

Written by Claude (statement writer) on 2026-10-20, before any proof. The cell data are
re-derived from the verification team's independent construction (R004 `d14.py`, read-only):
two hexagons with sides `s, 2r + s`, whose long sides are cut `r, s, r` by straight-angle
corners. Parameters: `r, s` are the second paper's D14 parameters and also R004's names. Check:
twice the total area is `2 (4r² + 6s² + 12rs) = 8r² + 24rs + 12s²`, the paper's D14 carbon order.

The mirror `studies/R002/analysis/2026-10-20-claude-d14-bridge/d14_mirror.py` checks this
Lean-literal surface against R004's construction.
-/

namespace Claude2Aligned

open ClaudeChallenge

/-- D14 labels: the two 12-gons share all twelve labels, in opposite orders (as for D12). -/
def d14Lab : Fin 2 → List ℕ :=
  ![[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [0, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1]]

/-- D14 polygons: the side between labels `j` and `j + 1` has length `s` for even `j` and `r`
for odd `j`. In cell 0 the corners `2, 3, 6, 7, 10, 11` are straight, in cell 1 the corners
`0, 1, 4, 5, 8, 9`; so each cell is a hexagon with sides `s, 2r + s`. -/
def d14Poly (r s : ℤ) (f : Fin 2) : List (ℤ × ℤ) :=
  if f.val = 0 then
    walk (0, 0) [(s, 0), (r, 1), (s, 1), (r, 1), (s, 2), (r, 3),
      (s, 3), (r, 3), (s, 4), (r, 5), (s, 5), (r, 5)]
  else
    walk (0, 0) [(r, 0), (s, 1), (r, 2), (s, 2), (r, 2), (s, 3),
      (r, 4), (s, 4), (r, 4), (s, 5), (r, 0), (s, 0)]

def d14Sig (r s : ℤ) : Sig := ⟨2, d14Lab, d14Poly r s⟩

/-- The dual graph of Graver's D14(r,s). -/
def d14Graph (r s : ℤ) : SimpleGraph (d14Sig r s).Vertex := (d14Sig r s).graph

end Claude2Aligned
