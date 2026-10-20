import Formal.Claude3GeoRows

/-!
# Theorem 1a, geometric foundation (5): interior degrees, unmarked degrees, seam continuation

Written by a Claude worker (2026-10-20, Theorem 1a geometric session).

* `common_iff_of_two`      : under `TwoCommonNeighbors`, two distinct known common neighbours
                             of an edge are all of them (abstract graphs).
* `valid_interior_adj_iff`, `valid_interior_deg` : under `Valid`, a chart point whose six lattice
                             neighbours lie in the same chart has exactly those six neighbours in
                             the surface graph, hence degree 6 (it is never a path end).
* `valid_deg_six_of_not_marked` : an unmarked vertex has degree 6.
* `valid_seam_next_iff`    : the forced continuation across a seam. If the unit edge `P Q` of
                             chart `f` has apex `A` in `f`, and the same two vertices are a unit
                             edge `P' Q'` of chart `f'` with apex `B'` in `f'`, and
                             `vtx A ≠ vtx B'` (**stated hypothesis**), then the continuation of
                             `(A, P, Q)` is `B'`.
-/

namespace ClaudeChallenge2.Geo

open ClaudeChallenge2

variable {S : Sig} {t : ℕ}

/-- Under `TwoCommonNeighbors`, two distinct common neighbours of an edge are all of them. -/
theorem common_iff_of_two {V : Type} {G : SimpleGraph V} (hT : TwoCommonNeighbors G)
    {b c x y : V} (hbc : G.Adj b c) (hxy : x ≠ y) (hx : G.Adj b x ∧ G.Adj c x)
    (hy : G.Adj b y ∧ G.Adj c y) : ∀ v, (G.Adj b v ∧ G.Adj c v) ↔ (v = x ∨ v = y) := by
  obtain ⟨x', y', hxy', hiff⟩ := hT b c hbc
  have ex := (hiff x).1 hx
  have ey := (hiff y).1 hy
  intro v
  rw [hiff v]
  rcases ex with rfl | rfl <;> rcases ey with rfl | rfl
  · exact absurd rfl hxy
  · exact Iff.rfl
  · exact or_comm
  · exact absurd rfl hxy

/-! ## Interior points -/

/-- The six lattice neighbours of an interior point give six distinct neighbours. -/
theorem valid_interior_finset (hV : Valid S t) {f : Fin S.C} {z : ℤ × ℤ}
    (hz : (S.chart f).Mem t z) (hnb : ∀ u ∈ unitVec, (S.chart f).Mem t (z + u)) :
    ∃ T : Finset (Vertex S t), T.card = 6 ∧
      (T : Set (Vertex S t)) ⊆ (graph S t).neighborSet (pt S t f z hz) ∧
      ∀ w, w ∈ T ↔ ∃ u, ∃ hu : u ∈ unitVec, w = pt S t f (z + u) (hnb u hu) := by
  classical
  let g : ℤ × ℤ → Vertex S t := fun u =>
    if h : (S.chart f).Mem t (z + u) then pt S t f (z + u) h else pt S t f z hz
  have hg : ∀ u (hu : u ∈ unitVec), g u = pt S t f (z + u) (hnb u hu) := fun u hu => by
    simp [g, hnb u hu]
  have hmemT : ∀ w, w ∈ unitVec.toFinset.image g ↔
      ∃ u, ∃ hu : u ∈ unitVec, w = pt S t f (z + u) (hnb u hu) := by
    intro w
    simp only [Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, hg u hu⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, hg u hu⟩
  refine ⟨unitVec.toFinset.image g, ?_, ?_, hmemT⟩
  · rw [Finset.card_image_of_injOn]
    · decide
    · intro u hu u' hu' e
      simp only [List.coe_toFinset, Set.mem_ofPred_eq] at hu hu'
      rw [hg u hu, hg u' hu'] at e
      simpa using valid_pt_inj hV _ _ e
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := (hmemT w).1 hw
    rw [SimpleGraph.mem_neighborSet]
    exact valid_adj_of_unit hV hz _ (by simpa using hu)

/-- Under `Valid`, a chart point all of whose six lattice neighbours lie in the chart is adjacent
exactly to the vertices of those six points. -/
theorem valid_interior_adj_iff (hV : Valid S t) {f : Fin S.C} {z : ℤ × ℤ}
    (hz : (S.chart f).Mem t z) (hnb : ∀ u ∈ unitVec, (S.chart f).Mem t (z + u))
    (w : Vertex S t) :
    (graph S t).Adj (pt S t f z hz) w ↔
      ∃ u, ∃ hu : u ∈ unitVec, w = pt S t f (z + u) (hnb u hu) := by
  obtain ⟨T, hTcard, hsub, hmemT⟩ := valid_interior_finset hV hz hnb
  have hdeg : ((graph S t).neighborSet (pt S t f z hz)).ncard ≤
      (T : Set (Vertex S t)).ncard := by
    rw [Set.ncard_coe_finset, hTcard]
    rcases hV.2.2.1 (pt S t f z hz) with h | h <;> (unfold deg at h; omega)
  have heq := Set.eq_of_subset_of_ncard_le hsub hdeg (Set.toFinite _)
  rw [← SimpleGraph.mem_neighborSet, ← heq, Finset.mem_coe, hmemT]

/-- Under `Valid`, such an interior point has degree exactly 6. -/
theorem valid_interior_deg (hV : Valid S t) {f : Fin S.C} {z : ℤ × ℤ}
    (hz : (S.chart f).Mem t z) (hnb : ∀ u ∈ unitVec, (S.chart f).Mem t (z + u)) :
    deg (graph S t) (pt S t f z hz) = 6 := by
  obtain ⟨T, hTcard, hsub, -⟩ := valid_interior_finset hV hz hnb
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hTcard] at this
  rcases hV.2.2.1 (pt S t f z hz) with h | h
  · unfold deg at h; omega
  · exact h

/-- Under `Valid`, an unmarked vertex has degree 6. -/
theorem valid_deg_six_of_not_marked (hV : Valid S t) {v : Vertex S t} (hv : ¬ IsMarked S t v) :
    deg (graph S t) v = 6 := by
  rcases hV.2.2.1 v with h | h
  · exact absurd (hV.2.2.2 v h) hv
  · exact h

/-- Under `Valid`, both ends of a literal path are marked corners. -/
theorem valid_literalPath_ends_marked (hV : Valid S t) {n : ℕ} {p : ℕ → Vertex S t}
    (hp : LiteralPath (graph S t) n p) : IsMarked S t (p 0) ∧ IsMarked S t (p (n - 1)) :=
  ⟨hV.2.2.2 _ hp.2.2.2.2.2.1, hV.2.2.2 _ hp.2.2.2.2.2.2.1⟩

/-! ## Seam continuation -/

/-- **Seam continuation.** Under `Valid`, let `P Q` be a unit edge of chart `f` with apex `A` in
`f`, and let `P' Q'` be a unit edge of chart `f'` representing the same two vertices, with apex
`B'` in `f'`. If `vtx A ≠ vtx B'`, the forced continuation of `(A, P, Q)` is `B'`.
(When `f = f'` and `P = P'`, `Q = Q'`, the hypothesis `vtx A ≠ vtx B'` is automatic for
`A ≠ B'`; see `valid_next_iff`.) -/
theorem valid_seam_next_iff (hV : Valid S t) {f f' : Fin S.C} {P Q A P' Q' B' : ℤ × ℤ}
    (hP : (S.chart f).Mem t P) (hQ : (S.chart f).Mem t Q) (hA : (S.chart f).Mem t A)
    (hP' : (S.chart f').Mem t P') (hQ' : (S.chart f').Mem t Q') (hB' : (S.chart f').Mem t B')
    (hPQ : Q - P ∈ unitVec) (hAP : P - A ∈ unitVec) (hAQ : Q - A ∈ unitVec)
    (hPB : B' - P' ∈ unitVec) (hQB : B' - Q' ∈ unitVec)
    (eP : pt S t f' P' hP' = pt S t f P hP) (eQ : pt S t f' Q' hQ' = pt S t f Q hQ)
    (hAB : pt S t f A hA ≠ pt S t f' B' hB') (e : Vertex S t) :
    Next (graph S t) (pt S t f A hA) (pt S t f P hP) (pt S t f Q hQ) e ↔ e = pt S t f' B' hB' := by
  have cA : (graph S t).Adj (pt S t f P hP) (pt S t f A hA) ∧
      (graph S t).Adj (pt S t f Q hQ) (pt S t f A hA) :=
    ⟨(valid_adj_of_unit hV hA hP hAP).symm, (valid_adj_of_unit hV hA hQ hAQ).symm⟩
  have cB : (graph S t).Adj (pt S t f P hP) (pt S t f' B' hB') ∧
      (graph S t).Adj (pt S t f Q hQ) (pt S t f' B' hB') := by
    rw [← eP, ← eQ]
    exact ⟨valid_adj_of_unit hV hP' hB' hPB, valid_adj_of_unit hV hQ' hB' hQB⟩
  exact next_iff_of_common hAB
    (common_iff_of_two hV.1 (valid_adj_of_unit hV hP hQ hPQ) hAB cA cB) e

end ClaudeChallenge2.Geo
