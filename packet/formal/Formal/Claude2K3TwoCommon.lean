import Formal.Claude2K3Necessity

/-!
# K3: every edge has two distinct common neighbours; the remaining hypothesis

Written by a Claude worker (2026-10-19, K3 necessity session).

* `edge_two_apexes`   : every edge of K3(r,s) (`r, s ≥ 2`) has two distinct common neighbours
                        (the third vertices of its two faces, from `apex_left`);
* `two_common_iff`    : hence `R002.TwoCommonNeighbors (k3Graph r s)` is equivalent to: no edge
                        has three distinct common neighbours (every triangle of the graph is a
                        face);
* `k3_statement_of_no_three` : `K3Statement` follows from that single combinatorial property.
-/

namespace Claude2K3
open ClaudeChallenge Claude2Aligned
variable {r s : ℤ}

/-- Two common neighbours of a vertex pair. -/
def Common (r s : ℤ) (b c v : (k3Sig r s).Vertex) : Prop :=
  (k3Graph r s).Adj b v ∧ (k3Graph r s).Adj c v

theorem edge_two_apexes (hr : 2 ≤ r) (hs : 2 ≤ s) {b c : (k3Sig r s).Vertex}
    (h : (k3Graph r s).Adj b c) : ∃ x y, x ≠ y ∧ Common r s b c x ∧ Common r s b c y := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  obtain ⟨f, w0, u, hu, hw0, hw1, e0, e1⟩ := first_edge hr0 hs0 h
  have hm1 : CellIn r s f (w0 + u + -u) := by simpa using hw0
  obtain ⟨f2, m2, τ2, -, l1, l2, l3, x1, x2, hne2, hin2, -⟩ :=
    apex_left hr hs f (w0 + u) (-u) (unitVec_neg hu) hw1 hm1
  obtain ⟨f1, m1, τ1, -, j1, j2, j3, y1, y2, hne1, hin1, -⟩ := apex_left hr hs f w0 u hu hw0 hw1
  have ew : w0 + u + -u = w0 := by abel
  rw [ew] at l2 x2
  have er : w0 + u + -u - rot (-u) = w0 + rot u := by rw [rot_neg', ew]; abel
  rw [er] at hne2
  have er2 : w0 + u + rot (-u) = w0 + u - rot u := by rw [rot_neg']; abel
  rw [er2] at l3 hne2 hin2
  refine ⟨V r s f1 (gmap m1 τ1 (w0 + rot u)), V r s f2 (gmap m2 τ2 (w0 + u - rot u)), ?_,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rcases apex_some_in hr hs f w0 u hu hw0 hw1 with hin | hin
    · rw [hin1 hin]; exact fun h => hne2 hin h.symm
    · rw [hin2 hin]; exact hne1 hin
  · rw [← e0, y1]; refine adj_of_unit hr0 hs0 j1 j3 ?_
    rw [gmap_sub, show w0 + rot u - w0 = rot u by abel]; exact rotN_unit m1 (rot_unit hu)
  · rw [← e1, y2]; refine adj_of_unit hr0 hs0 j2 j3 ?_
    rw [gmap_sub, show w0 + rot u - (w0 + u) = rot u - u by abel]
    exact rotN_unit m1 (rot_sub_unit hu)
  · rw [← e0, x2]; refine adj_of_unit hr0 hs0 l2 l3 ?_
    rw [gmap_sub, show w0 + u - rot u - w0 = u - rot u by abel]
    exact rotN_unit m2 (sub_rot_unit hu)
  · rw [← e1, x1]; refine adj_of_unit hr0 hs0 l1 l3 ?_
    rw [gmap_sub, show w0 + u - rot u - (w0 + u) = -rot u by abel]
    exact rotN_unit m2 (unitVec_neg (rot_unit hu))

/-- No edge has three distinct common neighbours. -/
def NoThreeCommon (r s : ℤ) : Prop :=
  ∀ b c x y z : (k3Sig r s).Vertex, (k3Graph r s).Adj b c →
    Common r s b c x → Common r s b c y → Common r s b c z → x ≠ y → x ≠ z → y ≠ z → False

theorem two_common_iff (hr : 2 ≤ r) (hs : 2 ≤ s) :
    R002.TwoCommonNeighbors (k3Graph r s) ↔ NoThreeCommon r s := by
  constructor
  · intro hT b c x y z hbc hx hy hz hxy hxz hyz
    obtain ⟨X, Y, -, h⟩ := hT b c hbc
    rcases (h x).1 hx with rfl | rfl <;> rcases (h y).1 hy with rfl | rfl <;>
      rcases (h z).1 hz with rfl | rfl <;> simp_all
  · intro hN b c hbc
    obtain ⟨x, y, hxy, hx, hy⟩ := edge_two_apexes hr hs hbc
    refine ⟨x, y, hxy, fun v => ⟨fun hv => ?_, ?_⟩⟩
    · by_contra hne
      rw [not_or] at hne
      exact hN b c x y v hbc hx hy hv hxy (Ne.symm hne.1) (Ne.symm hne.2)
    · rintro (rfl | rfl)
      · exact hx
      · exact hy

/-- **The K3 classification from one combinatorial property**: if no edge of K3(r,s) has three
distinct common neighbours (for all `r, s ≥ 2`), then `K3Statement` holds. -/
theorem k3_statement_of_no_three
    (hN : ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → NoThreeCommon r s) : K3Statement :=
  k3_statement_of_two_common fun r s hr hs =>
    (two_common_iff (by exact_mod_cast hr) (by exact_mod_cast hs)).2 (hN r s hr hs)

end Claude2K3

#print axioms Claude2K3.edge_two_apexes
#print axioms Claude2K3.two_common_iff
#print axioms Claude2K3.k3_statement_of_no_three
