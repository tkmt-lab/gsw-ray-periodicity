import Formal.Claude5O2Model

/-!
# O2 model: charts are injective, and how two charts meet

Written by a Claude worker (2026-10-20, O2 bridge session).

* `ch_valid` : chart points are model vertices;
* `ch_inj`   : each chart is injective;
* `Tr`, `ch_eq` : a vertex in two different charts lies on their seam: a `d`-side (charts 0, 1,
  same point), or the `2t`-side `j` at parameter `l` (charts 0 or 1 and rhombus `j`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

variable {t d : ℤ}

/-- The seam relation between two different charts (listed with the smaller chart first). -/
def Tr (t d : ℤ) : ℕ → ℕ → ℤ × ℤ → ℤ × ℤ → Prop
  | 0, 1, z, z' => z' = z ∧ OnD t d z
  | 0, j + 2, z, z' => ∃ l, 0 ≤ l ∧ l ≤ 2 * t ∧ z = sp t d j l ∧ z' = (max (l - t) 0, min l t)
  | 1, j + 2, z, z' => ∃ l, 0 ≤ l ∧ l ≤ 2 * t ∧ z = sp t d j l ∧ z' = (min l t, max (l - t) 0)
  | _, _, _, _ => False

theorem rk_le (z : ℤ × ℤ) : 0 ≤ rk t z ∧ rk t z ≤ 1 := by
  unfold rk; split_ifs <;> omega

theorem sp_inj {i : ℕ} (hi : i < 3) {l l' : ℤ} (h : sp t d i l = sp t d i l') : l = l' := by
  interval_cases i <;> simp [sp, Prod.ext_iff] at h <;> omega

theorem c_cases {c : ℕ} : c = 0 ∨ c = 1 ∨ ∃ i, c = i + 2 := by
  rcases c with _ | _ | i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨i, rfl⟩)

theorem ch_valid (ht : 1 ≤ t) (hd : 1 ≤ d) {c : ℕ} (hc : c < 5) {z : ℤ × ℤ}
    (hz : Dom t d c z) : Valid t d (ch t d c z) := by
  rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩
  · exact Or.inl ⟨rfl, hz⟩
  · by_cases h : OnD t d z
    · rw [ch1_onD h]; exact Or.inl ⟨rfl, hz⟩
    · rw [ch1_nD h]; exact Or.inr (Or.inl ⟨rfl, hz, h⟩)
  · have hi : i < 3 := by omega
    simp only [Dom, Rh] at hz
    by_cases h : RhI t z
    · rw [chR_int i h]
      refine Or.inr (Or.inr ⟨?_, h⟩)
      simp only
      omega
    · have hz' : z.1 = 0 ∨ (z.2 = t ∧ 0 ≤ z.1) ∨ (z.2 = 0 ∧ 0 ≤ z.1) ∨ z.1 = t := by
        simp only [RhI] at h; omega
      rcases hz' with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
      · rw [chR_AB ht i h1]; exact Or.inl ⟨rfl, sp_hx ht hd hi (by omega) (by omega)⟩
      · rw [chR_BC ht i h1 h2]; exact Or.inl ⟨rfl, sp_hx ht hd hi (by omega) (by omega)⟩
      · rw [chR_AD ht hd hi h1 h2 (by omega)]
        have hx := sp_hx (d := d) (l := z.1) ht hd hi (by omega) (by omega)
        by_cases h' : OnD t d (sp t d i z.1)
        · rw [ch1_onD h']; exact Or.inl ⟨rfl, hx⟩
        · rw [ch1_nD h']; exact Or.inr (Or.inl ⟨rfl, hx, h'⟩)
      · rw [chR_DC ht hd hi h1 (by omega) (by omega)]
        have hx := sp_hx (d := d) (l := t + z.2) ht hd hi (by omega) (by omega)
        by_cases h' : OnD t d (sp t d i (t + z.2))
        · rw [ch1_onD h']; exact Or.inl ⟨rfl, hx⟩
        · rw [ch1_nD h']; exact Or.inr (Or.inl ⟨rfl, hx, h'⟩)

/-- Rhombus boundary points are determined by sheet and parameter. -/
theorem rb_inj {z z' : ℤ × ℤ} (hz : Rh t z) (hz' : Rh t z') (h1 : ¬ RhI t z) (h1' : ¬ RhI t z')
    (hk : rk t z = rk t z') (hl : rl t z = rl t z') : z = z' := by
  simp only [Rh, RhI] at hz hz' h1 h1'
  unfold rk at hk; unfold rl at hl
  ext <;> split_ifs at hk hl <;> omega

theorem ch_inj (ht : 1 ≤ t) {c : ℕ} (hc : c < 5) {z z' : ℤ × ℤ} (hz : Dom t d c z)
    (hz' : Dom t d c z') (h : ch t d c z = ch t d c z') : z = z' := by
  rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩
  · simpa [ch0] using h
  · exact congrArg Prod.snd h
  · have hi : i < 3 := by omega
    simp only [Dom] at hz hz'
    by_cases h1 : RhI t z <;> by_cases h1' : RhI t z'
    · rw [chR_int i h1, chR_int i h1'] at h; exact congrArg Prod.snd h
    · rw [chR_int i h1, chR_bd i h1'] at h
      have := congrArg Prod.fst h; have := rk_le (t := t) z'; simp at *; omega
    · rw [chR_bd i h1, chR_int i h1'] at h
      have := congrArg Prod.fst h; have := rk_le (t := t) z; simp at *; omega
    · rw [chR_bd i h1, chR_bd i h1'] at h
      simp only [Prod.mk.injEq] at h
      exact rb_inj hz hz' h1 h1' h.1 (sp_inj hi h.2)

theorem sides_disj (ht : 1 ≤ t) (hd : 1 ≤ d) {i j : ℕ} (hi : i < 3) (hj : j < 3) {l l' : ℤ}
    (h0 : 0 ≤ l) (h1 : l ≤ 2 * t) (h0' : 0 ≤ l') (h1' : l' ≤ 2 * t)
    (h : sp t d i l = sp t d j l') : i = j := by
  interval_cases i <;> interval_cases j <;> simp [sp, Prod.ext_iff] at h <;> omega

/-- The parameter of a rhombus boundary point. -/
theorem rl_range {z : ℤ × ℤ} (hz : Rh t z) (h1 : ¬ RhI t z) : 0 ≤ rl t z ∧ rl t z ≤ 2 * t := by
  simp only [Rh, RhI] at hz h1
  unfold rl; split_ifs <;> omega

theorem ch_eq (ht : 1 ≤ t) (hd : 1 ≤ d) {c c' : ℕ} (hc : c < 5) (hc' : c' < 5)
    {z z' : ℤ × ℤ} (hz : Dom t d c z) (hz' : Dom t d c' z') (h : ch t d c z = ch t d c' z') :
    (c = c' ∧ z = z') ∨ Tr t d c c' z z' ∨ Tr t d c' c z' z := by
  rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩ <;>
    rcases c_cases (c := c') with rfl | rfl | ⟨j, rfl⟩
  · exact Or.inl ⟨rfl, ch_inj ht hc hz hz' h⟩
  · right; left
    by_cases h' : OnD t d z'
    · rw [ch1_onD h', ch0] at h
      simp only [Prod.mk.injEq] at h
      refine ⟨h.2.symm, ?_⟩
      rw [h.2]; exact h'
    · rw [ch1_nD h', ch0] at h; simp at h
  · -- 0, rhombus
    right; left
    have hj : j < 3 := by omega
    simp only [Dom] at hz'
    by_cases h1 : RhI t z'
    · rw [chR_int j h1, ch0] at h; simp at h; omega
    · rw [chR_bd j h1, ch0] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨hk, hl⟩ := h
      have hr := rl_range hz' h1
      refine ⟨rl t z', hr.1, hr.2, hl, ?_⟩
      simp only [Rh, RhI] at hz' h1
      unfold rk at hk; unfold rl
      ext <;> simp only <;> split_ifs at hk ⊢ <;> omega
  · right; right
    by_cases h' : OnD t d z
    · rw [ch1_onD h', ch0] at h
      simp only [Prod.mk.injEq] at h
      refine ⟨h.2, ?_⟩
      rw [← h.2]; exact h'
    · rw [ch1_nD h', ch0] at h; simp at h
  · exact Or.inl ⟨rfl, ch_inj ht hc hz hz' h⟩
  · -- 1, rhombus
    right; left
    have hj : j < 3 := by omega
    simp only [Dom] at hz'
    by_cases h1 : RhI t z'
    · rw [chR_int j h1] at h
      by_cases hO : OnD t d z
      · rw [ch1_onD hO] at h; simp at h; omega
      · rw [ch1_nD hO] at h; simp at h; omega
    · rw [chR_bd j h1] at h
      have hr := rl_range hz' h1
      have hl : z = sp t d j (rl t z') := congrArg Prod.snd h
      have hk : (if OnD t d z then (0 : ℤ) else 1) = rk t z' := congrArg Prod.fst h
      refine ⟨rl t z', hr.1, hr.2, hl, ?_⟩
      have hD := sp_onD (d := d) ht hd hj hr.1 hr.2
      rw [← hl] at hD
      simp only [Rh, RhI] at hz' h1
      by_cases hO : OnD t d z
      · simp only [hO, ↓reduceIte] at hk
        have hl2 := hD.1 hO
        unfold rk at hk; unfold rl at hl2 ⊢
        ext <;> simp only <;> split_ifs at hk hl2 ⊢ <;> omega
      · simp only [hO, ↓reduceIte] at hk
        unfold rk at hk; unfold rl
        ext <;> simp only <;> split_ifs at hk ⊢ <;> omega
  · -- rhombus, 0
    right; right
    have hi : i < 3 := by omega
    simp only [Dom] at hz
    by_cases h1 : RhI t z
    · rw [chR_int i h1, ch0] at h; simp at h; omega
    · rw [chR_bd i h1, ch0] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨hk, hl⟩ := h
      have hr := rl_range hz h1
      refine ⟨rl t z, hr.1, hr.2, hl.symm, ?_⟩
      simp only [Rh, RhI] at hz h1
      unfold rk at hk; unfold rl
      ext <;> simp only <;> split_ifs at hk ⊢ <;> omega
  · -- rhombus, 1
    right; right
    have hi : i < 3 := by omega
    simp only [Dom] at hz
    by_cases h1 : RhI t z
    · rw [chR_int i h1] at h
      by_cases hO : OnD t d z'
      · rw [ch1_onD hO] at h; simp at h; omega
      · rw [ch1_nD hO] at h; simp at h; omega
    · rw [chR_bd i h1] at h
      have hr := rl_range hz h1
      have hl : z' = sp t d i (rl t z) := (congrArg Prod.snd h).symm
      have hk : (if OnD t d z' then (0 : ℤ) else 1) = rk t z := (congrArg Prod.fst h).symm
      refine ⟨rl t z, hr.1, hr.2, hl, ?_⟩
      have hD := sp_onD (d := d) ht hd hi hr.1 hr.2
      rw [← hl] at hD
      simp only [Rh, RhI] at hz h1
      by_cases hO : OnD t d z'
      · simp only [hO, ↓reduceIte] at hk
        have hl2 := hD.1 hO
        unfold rk at hk; unfold rl at hl2 ⊢
        ext <;> simp only <;> split_ifs at hk hl2 ⊢ <;> omega
      · simp only [hO, ↓reduceIte] at hk
        unfold rk at hk; unfold rl
        ext <;> simp only <;> split_ifs at hk ⊢ <;> omega
  · -- two rhombi
    have hi : i < 3 := by omega
    have hj : j < 3 := by omega
    simp only [Dom] at hz hz'
    by_cases h1 : RhI t z <;> by_cases h1' : RhI t z'
    · rw [chR_int i h1, chR_int j h1'] at h
      simp only [Prod.mk.injEq] at h
      have : i = j := by omega
      subst this
      exact Or.inl ⟨rfl, h.2⟩
    · rw [chR_int i h1, chR_bd j h1'] at h
      have := congrArg Prod.fst h; have := rk_le (t := t) z'; simp at *; omega
    · rw [chR_bd i h1, chR_int j h1'] at h
      have := congrArg Prod.fst h; have := rk_le (t := t) z; simp at *; omega
    · rw [chR_bd i h1, chR_bd j h1'] at h
      simp only [Prod.mk.injEq] at h
      have hr := rl_range hz h1
      have hr' := rl_range hz' h1'
      have := sides_disj ht hd hi hj hr.1 hr.2 hr'.1 hr'.2 h.2
      subst this
      exact Or.inl ⟨rfl, rb_inj hz hz' h1 h1' h.1 (sp_inj hi h.2)⟩

end Claude5O2
