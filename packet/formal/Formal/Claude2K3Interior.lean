import Formal.Claude2K3Corners

/-!
# K3 aligned surface, part 7: interior points of hexagons and corner triangles have degree 6

Written by a Claude worker (2026-10-19).  A lattice point strictly inside one of the three
hexagons, or one of the six corner triangles of the caps, is the only site of its vertex, and its
six lattice neighbours are six distinct vertices; so its degree is 6 (all `r, s ≥ 2`).
-/

set_option linter.unusedSimpArgs false

namespace Claude2K3
open ClaudeChallenge Claude2Aligned
variable {r s : ℤ}

/-- Strict interior of the chart hexagon. -/
def HexInt (r s : ℤ) (z : ℤ × ℤ) : Prop :=
  0 < z.2 ∧ z.1 < r ∧ z.1 + z.2 < 2 * r ∧ z.2 < r + s ∧ -s < z.1 ∧ 0 < z.1 + z.2

set_option maxHeartbeats 4000000 in
theorem deg_hex_interior (hr : 2 ≤ r) (hs : 2 ≤ s) (c : Fin 11) (hc : c = 8 ∨ c = 9 ∨ c = 10)
    (z : ℤ × ℤ) (hz : HexInt r s z) : deg (k3Graph r s) (V r s c z) = 6 := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  obtain ⟨x, y⟩ := z
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hz
  simp only at h1 h2 h3 h4 h5 h6
  rw [deg_eq hr0 hs0 (V r s c (x, y)) [(c, (x, y))]
    ([(c, (x + 1, y)), (c, (x, y + 1)), (c, (x + -1, y + 1)), (c, (x + -1, y)), (c, (x, y + -1)),
      (c, (x + 1, y + -1))].map (fun p => V r s p.1 p.2)) ?_ ?_ ?_ ?_]
  · rfl
  · intro g w hw hV
    have hi := V_inv hr0 hs0 hw (by rcases hc with rfl | rfl | rfl <;>
      simp [CellIn, HexIn] <;> omega) hV
    rcases hc with rfl | rfl | rfl <;>
    fin_cases g <;> simp [inv, hgt, ang, nrm, CellIn, TriIn, HexIn, Prod.ext_iff] at hw hi ⊢ <;>
      (try split_ifs at hi) <;> omega
  · intro c' hc' u hu hcell
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    subst hc'
    simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hu
    right
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] <;>
      simp
  · intro w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    have hcz : CellIn r s c (x, y) := by
      rcases hc with rfl | rfl | rfl <;> simp [CellIn, HexIn] <;> omega
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · refine V_adj hr0 hs0 (z := (x, y)) rfl hcz (by rcases hc with rfl | rfl | rfl <;>
        simp [CellIn, HexIn] <;> omega) (1, 0) (by simp [unitVec]) (by ext <;> simp) ?_
      rcases hc with rfl | rfl | rfl <;>
        simp [inv, hgt, ang, nrm, Prod.ext_iff] <;> (try split_ifs) <;> omega
    · refine V_adj hr0 hs0 (z := (x, y)) rfl hcz (by rcases hc with rfl | rfl | rfl <;>
        simp [CellIn, HexIn] <;> omega) (0, 1) (by simp [unitVec]) (by ext <;> simp) ?_
      rcases hc with rfl | rfl | rfl <;>
        simp [inv, hgt, ang, nrm, Prod.ext_iff] <;> (try split_ifs) <;> omega
    · refine V_adj hr0 hs0 (z := (x, y)) rfl hcz (by rcases hc with rfl | rfl | rfl <;>
        simp [CellIn, HexIn] <;> omega) (-1, 1) (by simp [unitVec]) (by ext <;> simp) ?_
      rcases hc with rfl | rfl | rfl <;>
        simp [inv, hgt, ang, nrm, Prod.ext_iff] <;> (try split_ifs) <;> omega
    · refine V_adj hr0 hs0 (z := (x, y)) rfl hcz (by rcases hc with rfl | rfl | rfl <;>
        simp [CellIn, HexIn] <;> omega) (-1, 0) (by simp [unitVec]) (by ext <;> simp) ?_
      rcases hc with rfl | rfl | rfl <;>
        simp [inv, hgt, ang, nrm, Prod.ext_iff] <;> (try split_ifs) <;> omega
    · refine V_adj hr0 hs0 (z := (x, y)) rfl hcz (by rcases hc with rfl | rfl | rfl <;>
        simp [CellIn, HexIn] <;> omega) (0, -1) (by simp [unitVec]) (by ext <;> simp) ?_
      rcases hc with rfl | rfl | rfl <;>
        simp [inv, hgt, ang, nrm, Prod.ext_iff] <;> (try split_ifs) <;> omega
    · refine V_adj hr0 hs0 (z := (x, y)) rfl hcz (by rcases hc with rfl | rfl | rfl <;>
        simp [CellIn, HexIn] <;> omega) (1, -1) (by simp [unitVec]) (by ext <;> simp) ?_
      rcases hc with rfl | rfl | rfl <;>
        simp [inv, hgt, ang, nrm, Prod.ext_iff] <;> (try split_ifs) <;> omega
  · apply nodup_V hr0 hs0
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl | rfl | rfl) <;> rcases hc with rfl | rfl | rfl <;>
        simp [CellIn, HexIn] <;> omega
    · simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
        or_false, not_or, List.nodup_nil, and_true]
      repeat' apply And.intro
      all_goals (rcases hc with rfl | rfl | rfl <;>
        simp [inv, hgt, ang, nrm, Prod.ext_iff] <;> (try split_ifs) <;> omega)

/-- Strict interior of the chart triangle. -/
def TriInt (r : ℤ) (z : ℤ × ℤ) : Prop := 0 < z.2 ∧ z.1 + z.2 < r ∧ 0 < z.1

set_option maxHeartbeats 8000000 in
/-- Lattice points strictly inside one of the six corner triangles of the two caps (cells
`0, 1, 2, 4, 5, 6`) have degree 6.  (The middle triangles `3, 7` are not covered: there `inv`
does not separate points.) -/
theorem deg_tri_interior (hr : 2 ≤ r) (hs : 2 ≤ s) (c : Fin 11) (hc : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 4 ∨ c = 5 ∨ c = 6)
    (z : ℤ × ℤ) (hz : TriInt r z) : deg (k3Graph r s) (V r s c z) = 6 := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  obtain ⟨x, y⟩ := z
  obtain ⟨h1, h2, h3⟩ := hz
  simp only at h1 h2 h3
  rw [deg_eq hr0 hs0 (V r s c (x, y)) [(c, (x, y))]
    ([(c, (x + 1, y)), (c, (x, y + 1)), (c, (x + -1, y + 1)), (c, (x + -1, y)), (c, (x, y + -1)),
      (c, (x + 1, y + -1))].map (fun p => V r s p.1 p.2)) ?_ ?_ ?_ ?_]
  · rfl
  · intro g w hw hV
    have hi := V_inv hr0 hs0 hw (by rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [CellIn, TriIn] <;> omega) hV
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases g <;> simp [inv, hgt, ang, nrm, CellIn, TriIn, HexIn, Prod.ext_iff] at hw hi ⊢ <;>
      (try split_ifs at hi) <;> omega
  · intro c' hc' u hu hcell
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    subst hc'
    simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hu
    right
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] <;>
      simp
  · intro w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    have hcz : CellIn r s c (x, y) := by
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [CellIn, TriIn] <;> omega
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · refine V_adj hr0 hs0 (z := (x, y)) rfl hcz (by rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [CellIn, TriIn] <;> omega) (1, 0) (by simp [unitVec]) (by ext <;> simp) ?_
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [inv, hgt, ang, nrm, Prod.ext_iff] <;> (try split_ifs) <;> omega
    · refine V_adj hr0 hs0 (z := (x, y)) rfl hcz (by rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [CellIn, TriIn] <;> omega) (0, 1) (by simp [unitVec]) (by ext <;> simp) ?_
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [inv, hgt, ang, nrm, Prod.ext_iff] <;> (try split_ifs) <;> omega
    · refine V_adj hr0 hs0 (z := (x, y)) rfl hcz (by rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [CellIn, TriIn] <;> omega) (-1, 1) (by simp [unitVec]) (by ext <;> simp) ?_
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [inv, hgt, ang, nrm, Prod.ext_iff] <;> (try split_ifs) <;> omega
    · refine V_adj hr0 hs0 (z := (x, y)) rfl hcz (by rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [CellIn, TriIn] <;> omega) (-1, 0) (by simp [unitVec]) (by ext <;> simp) ?_
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [inv, hgt, ang, nrm, Prod.ext_iff] <;> (try split_ifs) <;> omega
    · refine V_adj hr0 hs0 (z := (x, y)) rfl hcz (by rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [CellIn, TriIn] <;> omega) (0, -1) (by simp [unitVec]) (by ext <;> simp) ?_
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [inv, hgt, ang, nrm, Prod.ext_iff] <;> (try split_ifs) <;> omega
    · refine V_adj hr0 hs0 (z := (x, y)) rfl hcz (by rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [CellIn, TriIn] <;> omega) (1, -1) (by simp [unitVec]) (by ext <;> simp) ?_
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [inv, hgt, ang, nrm, Prod.ext_iff] <;> (try split_ifs) <;> omega
  · apply nodup_V hr0 hs0
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl | rfl | rfl) <;> rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [CellIn, TriIn] <;> omega
    · simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
        or_false, not_or, List.nodup_nil, and_true]
      repeat' apply And.intro
      all_goals (rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [inv, hgt, ang, nrm, Prod.ext_iff] <;> (try split_ifs) <;> omega)

end Claude2K3

#print axioms Claude2K3.deg_hex_interior
#print axioms Claude2K3.deg_tri_interior
