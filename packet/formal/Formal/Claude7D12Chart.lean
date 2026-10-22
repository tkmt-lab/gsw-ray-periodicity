import Formal.Claude7D12Model

/-!
# D14 model: charts are injective, and how the two charts meet

Written by a Claude worker (2026-10-22, D12 bridge session), adapting `Claude5D14Chart.lean`.

* `ch_valid` : chart points are model vertices;
* `a0_inj`, `a1_inj`, `ch_inj` : the arclength is injective on each boundary, so each chart is
  injective;
* `ch_eq01` : a vertex in both charts is a seam point: boundary in both, equal arclengths;
* `unit_arc0`, `unit_arc1` : two boundary points of a chart are a unit apart exactly when their
  arclengths are neighbours on the seam circle.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Claude7D12

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

theorem ch_valid (hr : 1 ≤ r) (hs : 1 ≤ s) {c : ℕ} (hc : c < 2) {z : ℤ × ℤ}
    (hz : Dom r s c z) : Valid r s (ch r s c z) := by
  rcases c_cases hc with rfl | rfl
  · by_cases h : I0 r s z
    · rw [ch0_I h]; exact Or.inl ⟨rfl, h⟩
    · rw [ch0_B h]
      have := a0_range hr hs hz h
      exact Or.inr (Or.inr ⟨rfl, rfl, this.1, this.2⟩)
  · by_cases h : I1 r s z
    · rw [ch1_I h]; exact Or.inr (Or.inl ⟨rfl, h⟩)
    · rw [ch1_B h]
      have := a1_range hr hs hz h
      exact Or.inr (Or.inr ⟨rfl, rfl, this.1, this.2⟩)

theorem a0_inj (hr : 1 ≤ r) (hs : 1 ≤ s) {z z' : ℤ × ℤ} (h : H0 r s z) (hb : ¬ I0 r s z)
    (h' : H0 r s z') (hb' : ¬ I0 r s z') (e : a0 r s z = a0 r s z') : z = z' := by
  have c1 := bd0_cases h hb
  have c2 := bd0_cases h' hb'
  simp only [H0] at h h'
  obtain ⟨x, y⟩ := z
  obtain ⟨x', y'⟩ := z'
  simp only at c1 c2 h h' ⊢
  unfold a0 at e
  simp only at e
  split_ifs at e <;> (simp only [Prod.mk.injEq]; omega)

theorem a1_inj (hr : 1 ≤ r) (hs : 1 ≤ s) {z z' : ℤ × ℤ} (h : H1 r s z) (hb : ¬ I1 r s z)
    (h' : H1 r s z') (hb' : ¬ I1 r s z') (e : a1 r s z = a1 r s z') : z = z' := by
  have c1 := bd1_cases h hb
  have c2 := bd1_cases h' hb'
  simp only [H1] at h h'
  obtain ⟨x, y⟩ := z
  obtain ⟨x', y'⟩ := z'
  simp only at c1 c2 h h' ⊢
  unfold a1 at e
  simp only at e
  split_ifs at e <;> (simp only [Prod.mk.injEq]; omega)

theorem ch_inj (hr : 1 ≤ r) (hs : 1 ≤ s) {c : ℕ} (hc : c < 2) {z z' : ℤ × ℤ}
    (hz : Dom r s c z) (hz' : Dom r s c z') (h : ch r s c z = ch r s c z') : z = z' := by
  rcases c_cases hc with rfl | rfl
  · simp only [Dom] at hz hz'
    by_cases h1 : I0 r s z <;> by_cases h1' : I0 r s z'
    · rw [ch0_I h1, ch0_I h1'] at h; exact congrArg Prod.snd h
    · rw [ch0_I h1, ch0_B h1'] at h; simp at h
    · rw [ch0_B h1, ch0_I h1'] at h; simp at h
    · rw [ch0_B h1, ch0_B h1'] at h
      simp only [Prod.mk.injEq, true_and, and_true] at h
      exact a0_inj hr hs hz h1 hz' h1' h
  · simp only [Dom] at hz hz'
    by_cases h1 : I1 r s z <;> by_cases h1' : I1 r s z'
    · rw [ch1_I h1, ch1_I h1'] at h; exact congrArg Prod.snd h
    · rw [ch1_I h1, ch1_B h1'] at h; simp at h
    · rw [ch1_B h1, ch1_I h1'] at h; simp at h
    · rw [ch1_B h1, ch1_B h1'] at h
      simp only [Prod.mk.injEq, true_and, and_true] at h
      exact a1_inj hr hs hz h1 hz' h1' h

/-- A vertex in both charts: a boundary point of each, with equal arclengths. -/
theorem ch_eq01 {z z' : ℤ × ℤ} (h : ch r s 0 z = ch r s 1 z') :
    ¬ I0 r s z ∧ ¬ I1 r s z' ∧ a0 r s z = a1 r s z' := by
  by_cases h1 : I0 r s z <;> by_cases h1' : I1 r s z'
  · rw [ch0_I h1, ch1_I h1'] at h; simp at h
  · rw [ch0_I h1, ch1_B h1'] at h; simp at h
  · rw [ch0_B h1, ch1_I h1'] at h; simp at h
  · rw [ch0_B h1, ch1_B h1'] at h
    simp only [Prod.mk.injEq, true_and, and_true] at h
    exact ⟨h1, h1', h⟩

theorem ch01_of {z z' : ℤ × ℤ} (h1 : ¬ I0 r s z) (h2 : ¬ I1 r s z')
    (h3 : a0 r s z = a1 r s z') : ch r s 0 z = ch r s 1 z' := by
  rw [ch0_B h1, ch1_B h2, h3]

theorem ch_eq (hr : 1 ≤ r) (hs : 1 ≤ s) {c c' : ℕ} (hc : c < 2) (hc' : c' < 2)
    {z z' : ℤ × ℤ} (hz : Dom r s c z) (hz' : Dom r s c' z') (h : ch r s c z = ch r s c' z') :
    (c = c' ∧ z = z') ∨ (c = 0 ∧ c' = 1 ∧ ¬ I0 r s z ∧ ¬ I1 r s z' ∧ a0 r s z = a1 r s z') ∨
      (c = 1 ∧ c' = 0 ∧ ¬ I1 r s z ∧ ¬ I0 r s z' ∧ a1 r s z = a0 r s z') := by
  rcases c_cases hc with rfl | rfl <;> rcases c_cases hc' with rfl | rfl
  · exact Or.inl ⟨rfl, ch_inj hr hs hc hz hz' h⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl, ch_eq01 h⟩)
  · obtain ⟨a, b, e⟩ := ch_eq01 h.symm
    exact Or.inr (Or.inr ⟨rfl, rfl, b, a, e.symm⟩)
  · exact Or.inl ⟨rfl, ch_inj hr hs hc hz hz' h⟩

/-! ## The seam circle parametrised -/

/-- The boundary point of cell 0 at arclength `l`. -/
def P0 (r s l : ℤ) : ℤ × ℤ :=
  if l ≤ s then (l, 0) else if l ≤ r + 3 * s then (s, l - s)
  else if l ≤ 2 * r + 5 * s then (r + 4 * s - l, l - s)
  else if l ≤ 3 * r + 7 * s then (r + 4 * s - l, 2 * r + 4 * s)
  else if l ≤ 4 * r + 9 * s then (-2 * r - 3 * s, 5 * r + 11 * s - l)
  else if l ≤ 5 * r + 11 * s then (l - 6 * r - 12 * s, 5 * r + 11 * s - l)
  else (l - 6 * r - 12 * s, 0)

/-- The boundary point of cell 1 at arclength `l`. -/
def P1 (r s l : ℤ) : ℤ × ℤ :=
  if l ≤ r + 2 * s then (-l, l) else if l ≤ 2 * r + 4 * s then (-r - 2 * s, l)
  else if l ≤ 3 * r + 6 * s then (l - 3 * r - 6 * s, 2 * r + 4 * s)
  else if l ≤ 4 * r + 8 * s then (l - 3 * r - 6 * s, 5 * r + 10 * s - l)
  else if l ≤ 5 * r + 10 * s then (r + 2 * s, 5 * r + 10 * s - l)
  else (6 * r + 12 * s - l, 0)

theorem P0_spec (hr : 1 ≤ r) (hs : 1 ≤ s) {l : ℤ} (h0 : 0 ≤ l) (h1 : l < 6 * r + 12 * s) :
    H0 r s (P0 r s l) ∧ ¬ I0 r s (P0 r s l) ∧ a0 r s (P0 r s l) = l := by
  unfold P0
  split_ifs <;> simp only [H0, I0, a0] <;> refine ⟨by omega, by omega, ?_⟩ <;> split_ifs <;> d12om

theorem P1_spec (hr : 1 ≤ r) (hs : 1 ≤ s) {l : ℤ} (h0 : 0 ≤ l) (h1 : l < 6 * r + 12 * s) :
    H1 r s (P1 r s l) ∧ ¬ I1 r s (P1 r s l) ∧ a1 r s (P1 r s l) = l := by
  unfold P1
  split_ifs <;> simp only [H1, I1, a1] <;> refine ⟨by omega, by omega, ?_⟩ <;> split_ifs <;> d12om

theorem eq_P0 (hr : 1 ≤ r) (hs : 1 ≤ s) {z : ℤ × ℤ} (h : H0 r s z) (hb : ¬ I0 r s z) :
    z = P0 r s (a0 r s z) := by
  have hl := a0_range hr hs h hb
  have := P0_spec hr hs hl.1 hl.2
  exact a0_inj hr hs h hb this.1 this.2.1 this.2.2.symm

theorem eq_P1 (hr : 1 ≤ r) (hs : 1 ≤ s) {z : ℤ × ℤ} (h : H1 r s z) (hb : ¬ I1 r s z) :
    z = P1 r s (a1 r s z) := by
  have hl := a1_range hr hs h hb
  have := P1_spec hr hs hl.1 hl.2
  exact a1_inj hr hs h hb this.1 this.2.1 this.2.2.symm

/-! ## Unit steps along the boundaries -/

set_option maxHeartbeats 1000000 in
theorem unit_P0 (hr : 1 ≤ r) (hs : 1 ≤ s) {l l' : ℤ} (h0 : 0 ≤ l) (h1 : l < 6 * r + 12 * s)
    (h0' : 0 ≤ l') (h1' : l' < 6 * r + 12 * s) :
    P0 r s l' - P0 r s l ∈ unitVec ↔ ArcAdj r s l l' := by
  rw [unit_sub]
  simp only [ArcAdj, U2]
  unfold P0
  split_ifs <;> simp only <;> omega

set_option maxHeartbeats 1000000 in
theorem unit_P1 (hr : 1 ≤ r) (hs : 1 ≤ s) {l l' : ℤ} (h0 : 0 ≤ l) (h1 : l < 6 * r + 12 * s)
    (h0' : 0 ≤ l') (h1' : l' < 6 * r + 12 * s) :
    P1 r s l' - P1 r s l ∈ unitVec ↔ ArcAdj r s l l' := by
  rw [unit_sub]
  simp only [ArcAdj, U2]
  unfold P1
  split_ifs <;> simp only <;> omega

theorem unit_arc0 (hr : 1 ≤ r) (hs : 1 ≤ s) {z z' : ℤ × ℤ} (h : H0 r s z) (hb : ¬ I0 r s z)
    (h' : H0 r s z') (hb' : ¬ I0 r s z') :
    z' - z ∈ unitVec ↔ ArcAdj r s (a0 r s z) (a0 r s z') := by
  have l1 := a0_range hr hs h hb
  have l2 := a0_range hr hs h' hb'
  conv_lhs => rw [eq_P0 hr hs h hb, eq_P0 hr hs h' hb']
  exact unit_P0 hr hs l1.1 l1.2 l2.1 l2.2

theorem unit_arc1 (hr : 1 ≤ r) (hs : 1 ≤ s) {z z' : ℤ × ℤ} (h : H1 r s z) (hb : ¬ I1 r s z)
    (h' : H1 r s z') (hb' : ¬ I1 r s z') :
    z' - z ∈ unitVec ↔ ArcAdj r s (a1 r s z) (a1 r s z') := by
  have l1 := a1_range hr hs h hb
  have l2 := a1_range hr hs h' hb'
  conv_lhs => rw [eq_P1 hr hs h hb, eq_P1 hr hs h' hb']
  exact unit_P1 hr hs l1.1 l1.2 l2.1 l2.2

end Claude7D12
