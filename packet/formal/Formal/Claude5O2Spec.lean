import Formal.Claude2AlignedSpec

/-!
# Specification of Graver's O2(t,d) in the aligned-family style

Written by Claude (statement writer) on 2026-10-20, before any proof. The cell data are
re-derived from the verification team's independent construction (R004 `o2.py`, read-only):
two hexagons and six triangles. Parameters: `t, d` are the second paper's O2 parameters; R004's
`o2.py` calls them `r, s` (`t = r`, `d = s`). Check: twice the total area is
`2 (4t² + 8td + d²) + 6t² = 14t² + 16td + 2d²`, the paper's O2 carbon order.

Labels: the twelve signature corners `Aᵢ, Bᵢ, Cᵢ, Dᵢ` (`i = 0, 1, 2`) are encoded as
`4i + 0, 4i + 1, 4i + 2, 4i + 3`. The mirror `studies/R002/analysis/2026-10-20-claude-o2-bridge/
o2_mirror.py` checks this Lean-literal surface against R004's construction.
-/

namespace Claude2Aligned

open ClaudeChallenge

/-- Corner labels of the eight O2 cells (`Aᵢ = 4i`, `Bᵢ = 4i + 1`, `Cᵢ = 4i + 2`, `Dᵢ = 4i + 3`):
cell 0 is `A0 B0 C0 A1 B1 C1 A2 B2 C2`, cell 1 is `C2 D2 A2 C1 D1 A1 C0 D0 A0`, and cells
`2 + 2i`, `3 + 2i` are the triangles `Cᵢ Bᵢ Dᵢ` and `Bᵢ Aᵢ Dᵢ`. -/
def o2Lab : Fin 8 → List ℕ :=
  ![[0, 1, 2, 4, 5, 6, 8, 9, 10], [10, 11, 8, 6, 7, 4, 2, 3, 0],
    [2, 1, 3], [1, 0, 3], [6, 5, 7], [5, 4, 7], [10, 9, 11], [9, 8, 11]]

/-- O2 cell polygons: cells 0 and 1 are the hexagon with sides `2t, d, 2t, d, 2t, d`, each
`2t`-side carrying a straight-angle corner at its midpoint (`Bᵢ` resp. `Dᵢ`); cells 2–7 are
triangles of side `t`. -/
def o2Poly (t d : ℤ) (f : Fin 8) : List (ℤ × ℤ) :=
  if f.val < 2 then
    walk (0, 0) [(t, 0), (t, 0), (d, 1), (t, 2), (t, 2), (d, 3), (t, 4), (t, 4), (d, 5)]
  else walk (0, 0) [(t, 0), (t, 2), (t, 4)]

def o2Sig (t d : ℤ) : Sig := ⟨8, o2Lab, o2Poly t d⟩

/-- The dual graph of Graver's O2(t,d). -/
def o2Graph (t d : ℤ) : SimpleGraph (o2Sig t d).Vertex := (o2Sig t d).graph

end Claude2Aligned
