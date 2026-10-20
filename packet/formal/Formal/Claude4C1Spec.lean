import Formal.Claude2AlignedSpec

/-!
# Specification of Graver's C1(r,s) in the aligned-family style

Written by Claude (coordinator) on 2026-10-20, before any proof. C1 is the truncated
tetrahedron: one hexagon per face of a tetrahedron and one triangle per vertex. The corner label
`4a + b` names the corner of the truncation triangle at tetrahedron vertex `a` that points
towards vertex `b`. The cell data are re-derived from the verification team's independent
construction (R004 `c1.py`); the mirror `studies/R002/analysis/2026-10-20-claude-c1-bridge/
c1_mirror.py` checks this Lean-literal surface against it (36 cases, vertex and edge counts and
degree sequences agree, twelve degree-5 vertices, literal path iff `s = 1`).
-/

namespace Claude2Aligned

open ClaudeChallenge

/-- Corner labels of the eight C1 cells: cells `0..3` are the hexagons (tetrahedron faces),
cells `4..7` the triangles (tetrahedron vertices). Label `4a + b`: vertex `a`, towards `b`. -/
def c1Lab : Fin 8 → List ℕ :=
  ![[2, 8, 9, 6, 4, 1], [1, 4, 7, 13, 12, 3], [3, 12, 14, 11, 8, 2], [6, 9, 11, 14, 13, 7],
    [1, 3, 2], [4, 6, 7], [8, 11, 9], [12, 13, 14]]

/-- C1 cell polygons: hexagons with sides `s, r, s, r, s, r` and triangles of side `r`. -/
def c1Poly (r s : ℤ) (f : Fin 8) : List (ℤ × ℤ) :=
  if f.val < 4 then walk (0, 0) [(s, 0), (r, 1), (s, 2), (r, 3), (s, 4), (r, 5)]
  else walk (0, 0) [(r, 0), (r, 2), (r, 4)]

def c1Sig (r s : ℤ) : Sig := ⟨8, c1Lab, c1Poly r s⟩

/-- The dual graph of Graver's C1(r,s). -/
def c1Graph (r s : ℤ) : SimpleGraph (c1Sig r s).Vertex := (c1Sig r s).graph

end Claude2Aligned
