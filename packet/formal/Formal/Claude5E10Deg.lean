import Formal.Claude5E10Kill2

/-!
# E10 model: the degrees

Written by a Claude worker (2026-10-20, E10 bridge session).

The neighbours of a vertex are the images of the unit steps from its chart points.  An
interior point (of a cap or of the tube) has six; a seam point has four in the tube (two along
the seam, two above or below it) and, in the cap, the two seam neighbours again and its inner
neighbours: two on a side, one at a corner.  Hence every vertex has degree 6, except the twelve
corners, which have degree 5 (`deg_six`, `deg_corner`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

/-- The six unit vectors as a finset. -/
def U6 : Finset (ℤ × ℤ) := {(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)}

theorem mem_U6 {e : ℤ × ℤ} : e ∈ U6 ↔ e ∈ unitVec := by
  simp [U6, unit_iff]

/-- The degree is the size of an explicit set of valid vertices with the same adjacency. -/
theorem deg_eq_card (v : MS p r s) (S : Finset MV) (hS : ∀ y ∈ S, Valid p r s y)
    (h : ∀ x : MS p r s, AdjM p r s w v.1 x.1 ↔ x.1 ∈ S) : deg (GM p r s w) v = S.card := by
  unfold deg
  have e : (GM p r s w).neighborSet v = Subtype.val ⁻¹' (S : Set MV) := by
    ext x; simp only [SimpleGraph.mem_neighborSet, gm_adj, Set.mem_preimage, Finset.mem_coe]
    exact h x
  rw [e, Set.ncard_preimage_of_injective_subset_range Subtype.val_injective]
  · exact Set.ncard_coe_finset S
  · intro y hy; exact ⟨⟨y, hS y hy⟩, rfl⟩

/-- Adjacency read from the chart points of the first vertex. -/
theorem adj_rep {v x : MV} (h : AdjM p r s w v x) :
    ∃ c ρ e, InC p r s w c v ρ ∧ e ∈ unitVec ∧ Dom p r s c (ρ + e) ∧ x = ch p r s w c (ρ + e) :=
  by
  obtain ⟨-, c, hc, z, u, h1, h2, hu, rfl, rfl⟩ := h
  exact ⟨c, z, u, ⟨hc, h1, rfl⟩, hu, h2, rfl⟩

theorem unit_ne_zero' {u : ℤ × ℤ} (h : u ∈ unitVec) : u ≠ 0 := by
  rw [unit_iff] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Prod.ext_iff]

theorem adj_of_rep (H : Hyp p r s w) {c : ℕ} {v : MV} {ρ e : ℤ × ℤ} (h : InC p r s w c v ρ)
    (he : e ∈ unitVec) (hd : Dom p r s c (ρ + e)) : AdjM p r s w v (ch p r s w c (ρ + e)) := by
  refine ⟨?_, c, h.1, ρ, e, h.2.1, hd, he, h.2.2, rfl⟩
  have hx : InC p r s w c (ch p r s w c (ρ + e)) (ρ + e) := ⟨h.1, hd, rfl⟩
  refine ne_of_chart H h hx (fun q => unit_ne_zero' he ?_) ?_ ?_
  · have : ρ + e - ρ = ρ - ρ := by rw [← q]
    simpa using this
  · have := unit_small he; simp only [Prod.fst_add]; omega
  · have := unit_small he; simp only [Prod.fst_add]; omega

/-! ## Chart points of the vertices -/

theorem rep_L (H : Hyp p r s w) {c : ℕ} {z ρ : ℤ × ℤ} (h : InC p r s w c (0, z) ρ) :
    c = 0 ∧ ρ = z := by
  obtain ⟨hc, hd, e⟩ := h
  rcases c_cases hc with rfl | rfl | rfl
  · by_cases hI : IL r s ρ
    · rw [chL_I hI] at e; exact ⟨rfl, (Prod.mk.inj e).2⟩
    · rw [chL_B hI] at e; simp at e
  · by_cases hI : IU r s ρ
    · rw [chU_I hI] at e; simp at e
    · rw [chU_B hI] at e; simp at e
  · rw [chT] at e; simp at e

theorem rep_U (H : Hyp p r s w) {c : ℕ} {z ρ : ℤ × ℤ} (h : InC p r s w c (1, z) ρ) :
    c = 1 ∧ ρ = z := by
  obtain ⟨hc, hd, e⟩ := h
  rcases c_cases hc with rfl | rfl | rfl
  · by_cases hI : IL r s ρ
    · rw [chL_I hI] at e; simp at e
    · rw [chL_B hI] at e; simp at e
  · by_cases hI : IU r s ρ
    · rw [chU_I hI] at e; exact ⟨rfl, (Prod.mk.inj e).2⟩
    · rw [chU_B hI] at e; simp at e
  · rw [chT] at e; simp at e

theorem rep_T (H : Hyp p r s w) {c : ℕ} {u h : ℤ} {ρ : ℤ × ℤ} (h0 : 0 < h) (h1 : h < 2 * p)
    (hu0 : 0 ≤ u) (hu1 : u < 3 * (2 * r + s)) (hρ : InC p r s w c (2, (u, h)) ρ) :
    c = 2 ∧ ∃ t : ℤ, ρ = (u, h - u) + t • per r s := by
  obtain ⟨hc, hd, e⟩ := hρ
  rcases c_cases hc with rfl | rfl | rfl
  · by_cases hI : IL r s ρ
    · rw [chL_I hI] at e; simp at e
    · rw [chL_B hI] at e; simp only [Prod.mk.injEq, true_and] at e; omega
  · by_cases hI : IU r s ρ
    · rw [chU_I hI] at e; simp at e
    · rw [chU_B hI] at e; simp only [Prod.mk.injEq, true_and] at e; omega
  · refine ⟨rfl, ?_⟩
    have := chT_rep (p := p) (w := w) H.hr H.hs (z := (u, h - u)) (z' := ρ) (by
      rw [e, chT]; simp only [add_sub_cancel, Prod.mk.injEq, true_and, and_true]
      exact Int.emod_eq_of_lt hu0 hu1)
    exact this

theorem rep_low (H : Hyp p r s w) {c : ℕ} {u : ℤ} {ρ : ℤ × ℤ} (hu0 : 0 ≤ u)
    (hu1 : u < 3 * (2 * r + s)) (hρ : InC p r s w c (2, (u, 0)) ρ) :
    (c = 2 ∧ ∃ t : ℤ, ρ = (u, -u) + t • per r s) ∨ (c = 0 ∧ ρ = PL r s u) := by
  have hp := H.hp
  obtain ⟨hc, hd, e⟩ := hρ
  rcases c_cases hc with rfl | rfl | rfl
  · right
    by_cases hI : IL r s ρ
    · rw [chL_I hI] at e; simp at e
    · rw [chL_B hI] at e; simp only [Prod.mk.injEq, true_and, and_true] at e
      exact ⟨rfl, by rw [eq_PL H.hr H.hs hd hI, e]⟩
  · by_cases hI : IU r s ρ
    · rw [chU_I hI] at e; simp at e
    · rw [chU_B hI] at e; simp only [Prod.mk.injEq, true_and] at e; omega
  · left
    refine ⟨rfl, ?_⟩
    exact chT_rep (p := p) (w := w) H.hr H.hs (z := (u, -u)) (z' := ρ) (by
      rw [e, chT]; simp only [Prod.mk.injEq, true_and]
      exact ⟨Int.emod_eq_of_lt hu0 hu1, by ring⟩)

theorem rep_up (H : Hyp p r s w) {c : ℕ} {u : ℤ} {ρ : ℤ × ℤ} (hu0 : 0 ≤ u)
    (hu1 : u < 3 * (2 * r + s)) (hρ : InC p r s w c (2, (u, 2 * p)) ρ) :
    (c = 2 ∧ ∃ t : ℤ, ρ = (u, 2 * p - u) + t • per r s) ∨
      (c = 1 ∧ ρ = PU r s (unwrapU r s w u)) := by
  have hp := H.hp
  obtain ⟨hc, hd, e⟩ := hρ
  rcases c_cases hc with rfl | rfl | rfl
  · by_cases hI : IL r s ρ
    · rw [chL_I hI] at e; simp at e
    · rw [chL_B hI] at e; simp only [Prod.mk.injEq, true_and] at e; omega
  · right
    by_cases hI : IU r s ρ
    · rw [chU_I hI] at e; simp at e
    · rw [chU_B hI] at e; simp only [Prod.mk.injEq, true_and, and_true] at e
      refine ⟨rfl, ?_⟩
      rw [eq_PU H.hr H.hs hd hI]
      congr 1
      have l1 := aU_range H.hr H.hs hd hI
      have := H.hw0; have := H.hw1
      unfold unwrapU; unfold wrap at e; split_ifs at e ⊢ <;> omega
  · left
    refine ⟨rfl, ?_⟩
    exact chT_rep (p := p) (w := w) H.hr H.hs (z := (u, 2 * p - u)) (z' := ρ) (by
      rw [e, chT]; simp only [Prod.mk.injEq, true_and]
      exact ⟨Int.emod_eq_of_lt hu0 hu1, by ring⟩)

end Claude5E10
