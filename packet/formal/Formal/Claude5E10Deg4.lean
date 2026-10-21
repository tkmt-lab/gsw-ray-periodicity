import Formal.Claude5E10Deg3

/-!
# E10 model: the degree of every vertex (`deg_corner`, `deg_noncorner`, `deg_five_corner`)

Written by a Claude worker (2026-10-20, E10 bridge session).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

theorem card_A6 : A6.card = 4 := by decide
theorem card_B6 : B6.card = 4 := by decide
theorem card_U6 : U6.card = 6 := by decide

theorem tag_chT (z : ℤ × ℤ) : (ch p r s w 2 z).1 = 2 := rfl

theorem card_SL (H : Hyp p r s w) {u : ℤ} (hu0 : 0 ≤ u) (hu1 : u < 3 * (2 * r + s)) :
    (SL p r s w u).card = 4 + (if IsArc r s u then 1 else 2) := by
  rw [SL, Finset.card_union_of_disjoint, Finset.card_image_of_injOn,
    Finset.card_image_of_injective, inL_card H.hr H.hs hu0 hu1, card_A6]
  · intro e e' h; simpa using congrArg (fun x : MV => x.2) h
  · intro e he e' he' h
    exact tube_img_inj H _ (mem_A6.1 he).1 (mem_A6.1 he').1 h
  · rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨e', -, h⟩ := Finset.mem_image.1 hx'
    have := congrArg Prod.fst h
    simp [tag_chT] at this

theorem card_SU (H : Hyp p r s w) {u : ℤ} (hu0 : 0 ≤ u) (hu1 : u < 3 * (2 * r + s)) :
    (SU p r s w u).card = 4 + (if IsArc r s (unwrapU r s w u) then 1 else 2) := by
  obtain ⟨x0, x1, -⟩ := unwrapU_spec H hu0 hu1
  rw [SU, Finset.card_union_of_disjoint, Finset.card_image_of_injOn,
    Finset.card_image_of_injective, inU_card H.hr H.hs x0 x1, card_B6]
  · intro e e' h; simpa using congrArg (fun x : MV => x.2) h
  · intro e he e' he' h
    exact tube_img_inj H _ (mem_B6.1 he).1 (mem_B6.1 he').1 h
  · rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨e', -, h⟩ := Finset.mem_image.1 hx'
    have := congrArg Prod.fst h
    simp [tag_chT] at this

/-- Degree of a vertex given an explicit neighbour set. -/
theorem deg_of_set (H : Hyp p r s w) (v : MS p r s) (S : Finset MV)
    (h : ∀ x : MV, AdjM p r s w v.1 x ↔ x ∈ S) : deg (GM p r s w) v = S.card := by
  apply deg_eq_card v S
  · intro y hy
    obtain ⟨c, ρ, e, hρ, -, hd, rfl⟩ := adj_rep ((h y).2 hy)
    exact ch_valid H.hp H.hr H.hs H.hw0 H.hw1 hρ.1 hd
  · intro x; exact h x.1

/-- An interior point of a chart: six neighbours. -/
theorem deg_int (H : Hyp p r s w) (v : MS p r s) {c : ℕ} {z : ℤ × ℤ}
    (hz : InC p r s w c v.1 z) (hall : ∀ e ∈ unitVec, Dom p r s c (z + e))
    (hrep : ∀ c' ρ, InC p r s w c' v.1 ρ → c' = c ∧ ∃ t : ℤ, (c = 2 ∧ ρ = z + t • per r s) ∨ ρ = z) :
    deg (GM p r s w) v = 6 := by
  rw [deg_of_set H v (U6.image (fun e => ch p r s w c (z + e)))]
  · rw [Finset.card_image_of_injOn, card_U6]
    intro e he e' he' hq
    have h1 : InC p r s w c (ch p r s w c (z + e)) (z + e) := ⟨hz.1, hall e (mem_U6.1 he), rfl⟩
    have h2 : InC p r s w c (ch p r s w c (z + e')) (z + e') := ⟨hz.1, hall e' (mem_U6.1 he'), rfl⟩
    by_contra hne
    have s1 := unit_small (mem_U6.1 he); have s2 := unit_small (mem_U6.1 he')
    exact ne_of_chart H h1 h2 (fun q => hne (by simpa using q)) (by simp only [Prod.fst_add]; omega)
      (by simp only [Prod.fst_add]; omega) hq
  · intro x
    constructor
    · intro h
      obtain ⟨c', ρ, e, hρ, he, hd, rfl⟩ := adj_rep h
      obtain ⟨rfl, t, ht⟩ := hrep c' ρ hρ
      refine Finset.mem_image.2 ⟨e, mem_U6.2 he, ?_⟩
      rcases ht with ⟨rfl, rfl⟩ | rfl
      · rw [show z + t • per r s + e = z + e + t • per r s by abel, chT_shift]
      · rfl
    · intro h
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
      exact adj_of_rep H hz (mem_U6.1 he) (hall e (mem_U6.1 he))

theorem corner_low (H : Hyp p r s w) {u : ℤ} :
    IsCornerV p r s w (2, (u, 0)) ↔ IsArc r s u := by
  have hp := H.hp
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨a, ha, h⟩)
    · simp only [Prod.mk.injEq, true_and, and_true] at h; rwa [h]
    · simp only [Prod.mk.injEq, true_and] at h; omega
  · intro h; exact Or.inl ⟨u, h, rfl⟩

theorem corner_up (H : Hyp p r s w) {u : ℤ} (hu0 : 0 ≤ u) (hu1 : u < 3 * (2 * r + s)) :
    IsCornerV p r s w (2, (u, 2 * p)) ↔ IsArc r s (unwrapU r s w u) := by
  have hp := H.hp
  obtain ⟨x0, x1, xw⟩ := unwrapU_spec H hu0 hu1
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨a, ha, h⟩)
    · simp only [Prod.mk.injEq, true_and] at h; omega
    · simp only [Prod.mk.injEq, true_and, and_true] at h
      have l2 := arc_range H.hr H.hs ha
      have := H.hw0; have := H.hw1
      have : unwrapU r s w u = a := by
        rw [h]; unfold unwrapU wrap; split_ifs <;> omega
      rwa [this]
  · intro h; exact Or.inr ⟨_, h, by rw [xw]⟩

/-- **Degrees.** -/
theorem deg_cases (H : Hyp p r s w) (v : MS p r s) :
    (IsCornerV p r s w v.1 ∧ deg (GM p r s w) v = 5) ∨
      (¬ IsCornerV p r s w v.1 ∧ deg (GM p r s w) v = 6) := by
  have hp := H.hp; have hr := H.hr; have hs := H.hs
  obtain ⟨⟨k, z⟩, hv⟩ := v
  rcases hv with ⟨hk, hz⟩ | ⟨hk, hz⟩ | ⟨hk, h0, h1, h2, h3⟩ <;> simp only at hk
  · subst hk
    right
    refine ⟨by rintro (⟨a, -, h⟩ | ⟨a, -, h⟩) <;> simp at h, ?_⟩
    apply deg_int H _ (c := 0) (z := z) ⟨by norm_num, by simp only [Dom]; simp only [IL, HL] at hz ⊢; omega, chL_I hz⟩
    · intro e he; rw [unit_iff] at he; simp only [IL] at hz
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Dom, HL, Prod.fst_add, Prod.snd_add] <;> omega
    · intro c' ρ hρ; obtain ⟨a, b⟩ := rep_L H hρ; exact ⟨a, 0, Or.inr b⟩
  · subst hk
    right
    refine ⟨by rintro (⟨a, -, h⟩ | ⟨a, -, h⟩) <;> simp at h, ?_⟩
    apply deg_int H _ (c := 1) (z := z) ⟨by norm_num, by simp only [Dom]; simp only [IU, HU] at hz ⊢; omega, chU_I hz⟩
    · intro e he; rw [unit_iff] at he; simp only [IU] at hz
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Dom, HU, Prod.fst_add, Prod.snd_add] <;> omega
    · intro c' ρ hρ; obtain ⟨a, b⟩ := rep_U H hρ; exact ⟨a, 0, Or.inr b⟩
  · subst hk
    obtain ⟨u, h⟩ := z
    simp only at h0 h1 h2 h3
    by_cases hl : h = 0
    · subst hl
      have hd := deg_of_set H ⟨(2, (u, 0)), Or.inr (Or.inr ⟨rfl, h0, h1, h2, h3⟩)⟩ (SL p r s w u)
        (adj_low H h0 h1)
      rw [card_SL H h0 h1] at hd
      by_cases ha : IsArc r s u
      · left; exact ⟨(corner_low H).2 ha, by rw [hd, if_pos ha]⟩
      · right; exact ⟨fun c => ha ((corner_low H).1 c), by rw [hd, if_neg ha]⟩
    by_cases hu : h = 2 * p
    · subst hu
      have hd := deg_of_set H ⟨(2, (u, 2 * p)), Or.inr (Or.inr ⟨rfl, h0, h1, h2, h3⟩)⟩ (SU p r s w u)
        (adj_up H h0 h1)
      rw [card_SU H h0 h1] at hd
      by_cases ha : IsArc r s (unwrapU r s w u)
      · left; exact ⟨(corner_up H h0 h1).2 ha, by rw [hd, if_pos ha]⟩
      · right; exact ⟨fun c => ha ((corner_up H h0 h1).1 c), by rw [hd, if_neg ha]⟩
    right
    refine ⟨by rintro (⟨a, -, e⟩ | ⟨a, -, e⟩) <;> simp only [Prod.mk.injEq] at e <;> omega, ?_⟩
    have iT : InC p r s w 2 (2, (u, h)) (u, h - u) :=
      ⟨by norm_num, by simp only [Dom, HT]; omega, by
        rw [chT]; simp only [Prod.mk.injEq, true_and]; exact ⟨Int.emod_eq_of_lt h0 h1, by ring⟩⟩
    apply deg_int H _ iT
    · intro e he; have := ht_unit he; simp only [ht] at this
      simp only [Dom, HT, Prod.fst_add, Prod.snd_add]; omega
    · intro c' ρ hρ
      obtain ⟨a, t, b⟩ := rep_T H (by omega) (by omega) h0 h1 hρ
      exact ⟨a, t, Or.inl ⟨rfl, b⟩⟩

/-- **Degree five means corner.** -/
theorem deg_five_corner (H : Hyp p r s w) (v : MS p r s) (h : deg (GM p r s w) v = 5) :
    IsCornerV p r s w v.1 := by
  rcases deg_cases H v with ⟨c, -⟩ | ⟨-, e⟩
  · exact c
  · omega

end Claude5E10
