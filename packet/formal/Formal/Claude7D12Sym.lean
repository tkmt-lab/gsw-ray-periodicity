import Formal.Claude7D12Help
import Formal.Claude4C1G4

/-!
# D12 model: two automorphisms, and every corner is moved to the label-0 point

Written by a Claude worker (2026-10-22, D12 bridge session).

* `sg1` : rotate cell 0 clockwise and cell 1 counterclockwise by 60° about their centres; on the
          seam circle this is `l ↦ l - L` (`L = r + 2s`), so the label-`j` point goes to the
          label-`(j - 2)` point;
* `sg2` : exchange the two cells (`(x, y) ↦ (x + y - s, s - x)` from cell 0 to cell 1 and the
          inverse map back); on the seam circle `l ↦ s - l`, so labels `0` and `1` are exchanged;
* `lit_sg1`, `lit_sg2` : literal paths are carried along (both are graph automorphisms);
* `to_label0` : a literal path starting at any of the twelve corners gives one starting at the
                label-0 point `(2, (0, 0))`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude7D12

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

/-! ## The maps -/

/-- Rotation of cell 0 (clockwise, about `(-(r+s), r+2s)`). -/
def ro0 (r s : ℤ) (z : ℤ × ℤ) : ℤ × ℤ := (z.1 + z.2 - r - 2 * s, s - z.1)
/-- Its inverse. -/
def ro0' (r s : ℤ) (z : ℤ × ℤ) : ℤ × ℤ := (s - z.2, z.1 + z.2 + r + s)
/-- Rotation of cell 1 (counterclockwise, about `(0, r+2s)`). -/
def ro1 (r s : ℤ) (z : ℤ × ℤ) : ℤ × ℤ := (r + 2 * s - z.2, z.1 + z.2)
/-- Its inverse. -/
def ro1' (r s : ℤ) (z : ℤ × ℤ) : ℤ × ℤ := (z.1 + z.2 - r - 2 * s, r + 2 * s - z.1)
/-- Cell 0 to cell 1. -/
def fi (r s : ℤ) (z : ℤ × ℤ) : ℤ × ℤ := (z.1 + z.2 - s, s - z.1)
/-- Cell 1 to cell 0. -/
def ps (r s : ℤ) (z : ℤ × ℤ) : ℤ × ℤ := (s - z.2, z.1 + z.2)

def sh1 (r s l : ℤ) : ℤ := if r + 2 * s ≤ l then l - r - 2 * s else l + 5 * r + 10 * s
def sh1' (r s l : ℤ) : ℤ := if l < 5 * r + 10 * s then l + r + 2 * s else l - 5 * r - 10 * s
def sh2 (r s l : ℤ) : ℤ := if l ≤ s then s - l else 6 * r + 12 * s + s - l

/-- The rotation. -/
def sg1 (r s : ℤ) (v : MV) : MV :=
  if v.1 = 0 then ch r s 0 (ro0 r s v.2) else if v.1 = 1 then ch r s 1 (ro1 r s v.2)
  else (2, (sh1 r s v.2.1, 0))
/-- Its inverse. -/
def sg1' (r s : ℤ) (v : MV) : MV :=
  if v.1 = 0 then ch r s 0 (ro0' r s v.2) else if v.1 = 1 then ch r s 1 (ro1' r s v.2)
  else (2, (sh1' r s v.2.1, 0))
/-- The exchange of the cells (an involution). -/
def sg2 (r s : ℤ) (v : MV) : MV :=
  if v.1 = 0 then ch r s 1 (fi r s v.2) else if v.1 = 1 then ch r s 0 (ps r s v.2)
  else (2, (sh2 r s v.2.1, 0))

/-! ## Charts -/

theorem sg1_ch0 (hr : 1 ≤ r) (hs : 1 ≤ s) {z : ℤ × ℤ} (hz : H0 r s z) :
    sg1 r s (ch r s 0 z) = ch r s 0 (ro0 r s z) := by
  by_cases h : I0 r s z
  · rw [ch0_I h]; simp [sg1]
  · rw [ch0_B h]
    have h' : ¬ I0 r s (ro0 r s z) := by
      obtain ⟨x, y⟩ := z; simp only [I0, ro0, H0] at h hz ⊢; omega
    rw [ch0_B h']
    simp only [sg1, show ((2 : ℤ) = 0) = False by decide, show ((2 : ℤ) = 1) = False by decide,
      if_false, Prod.mk.injEq, true_and, and_true]
    have := bd0_cases hz h
    obtain ⟨x, y⟩ := z
    simp only [H0, ro0, sh1, a0] at hz this ⊢
    split_ifs <;> d12om

theorem sg1_ch1 (hr : 1 ≤ r) (hs : 1 ≤ s) {z : ℤ × ℤ} (hz : H1 r s z) :
    sg1 r s (ch r s 1 z) = ch r s 1 (ro1 r s z) := by
  by_cases h : I1 r s z
  · rw [ch1_I h]; simp [sg1]
  · rw [ch1_B h]
    have h' : ¬ I1 r s (ro1 r s z) := by
      obtain ⟨x, y⟩ := z; simp only [I1, ro1, H1] at h hz ⊢; omega
    rw [ch1_B h']
    simp only [sg1, show ((2 : ℤ) = 0) = False by decide, show ((2 : ℤ) = 1) = False by decide,
      if_false, Prod.mk.injEq, true_and, and_true]
    have := bd1_cases hz h
    obtain ⟨x, y⟩ := z
    simp only [H1, ro1, sh1, a1] at hz this ⊢
    split_ifs <;> d12om

theorem sg1'_ch0 (hr : 1 ≤ r) (hs : 1 ≤ s) {z : ℤ × ℤ} (hz : H0 r s z) :
    sg1' r s (ch r s 0 z) = ch r s 0 (ro0' r s z) := by
  by_cases h : I0 r s z
  · rw [ch0_I h]; simp [sg1']
  · rw [ch0_B h]
    have h' : ¬ I0 r s (ro0' r s z) := by
      obtain ⟨x, y⟩ := z; simp only [I0, ro0', H0] at h hz ⊢; omega
    rw [ch0_B h']
    simp only [sg1', show ((2 : ℤ) = 0) = False by decide, show ((2 : ℤ) = 1) = False by decide,
      if_false, Prod.mk.injEq, true_and, and_true]
    have := bd0_cases hz h
    obtain ⟨x, y⟩ := z
    simp only [H0, ro0', sh1', a0] at hz this ⊢
    split_ifs <;> d12om

theorem sg1'_ch1 (hr : 1 ≤ r) (hs : 1 ≤ s) {z : ℤ × ℤ} (hz : H1 r s z) :
    sg1' r s (ch r s 1 z) = ch r s 1 (ro1' r s z) := by
  by_cases h : I1 r s z
  · rw [ch1_I h]; simp [sg1']
  · rw [ch1_B h]
    have h' : ¬ I1 r s (ro1' r s z) := by
      obtain ⟨x, y⟩ := z; simp only [I1, ro1', H1] at h hz ⊢; omega
    rw [ch1_B h']
    simp only [sg1', show ((2 : ℤ) = 0) = False by decide, show ((2 : ℤ) = 1) = False by decide,
      if_false, Prod.mk.injEq, true_and, and_true]
    have := bd1_cases hz h
    obtain ⟨x, y⟩ := z
    simp only [H1, ro1', sh1', a1] at hz this ⊢
    split_ifs <;> d12om

theorem sg2_ch0 (hr : 1 ≤ r) (hs : 1 ≤ s) {z : ℤ × ℤ} (hz : H0 r s z) :
    sg2 r s (ch r s 0 z) = ch r s 1 (fi r s z) := by
  by_cases h : I0 r s z
  · rw [ch0_I h]; simp [sg2]
  · rw [ch0_B h]
    have h' : ¬ I1 r s (fi r s z) := by
      obtain ⟨x, y⟩ := z; simp only [I0, I1, fi, H0] at h hz ⊢; omega
    rw [ch1_B h']
    simp only [sg2, show ((2 : ℤ) = 0) = False by decide, show ((2 : ℤ) = 1) = False by decide,
      if_false, Prod.mk.injEq, true_and, and_true]
    have := bd0_cases hz h
    obtain ⟨x, y⟩ := z
    simp only [H0, fi, sh2, a0, a1] at hz this ⊢
    split_ifs <;> d12om

theorem sg2_ch1 (hr : 1 ≤ r) (hs : 1 ≤ s) {z : ℤ × ℤ} (hz : H1 r s z) :
    sg2 r s (ch r s 1 z) = ch r s 0 (ps r s z) := by
  by_cases h : I1 r s z
  · rw [ch1_I h]; simp [sg2]
  · rw [ch1_B h]
    have h' : ¬ I0 r s (ps r s z) := by
      obtain ⟨x, y⟩ := z; simp only [I0, I1, ps, H1] at h hz ⊢; omega
    rw [ch0_B h']
    simp only [sg2, show ((2 : ℤ) = 0) = False by decide, show ((2 : ℤ) = 1) = False by decide,
      if_false, Prod.mk.injEq, true_and, and_true]
    have := bd1_cases hz h
    obtain ⟨x, y⟩ := z
    simp only [H1, ps, sh2, a0, a1] at hz this ⊢
    split_ifs <;> d12om

/-! ## Validity, inverses, adjacency -/

theorem ro0_I {z : ℤ × ℤ} (h : I0 r s z) : I0 r s (ro0 r s z) := by
  obtain ⟨x, y⟩ := z; simp only [I0, ro0] at h ⊢; omega
theorem ro0'_I {z : ℤ × ℤ} (h : I0 r s z) : I0 r s (ro0' r s z) := by
  obtain ⟨x, y⟩ := z; simp only [I0, ro0'] at h ⊢; omega
theorem ro1_I {z : ℤ × ℤ} (h : I1 r s z) : I1 r s (ro1 r s z) := by
  obtain ⟨x, y⟩ := z; simp only [I1, ro1] at h ⊢; omega
theorem ro1'_I {z : ℤ × ℤ} (h : I1 r s z) : I1 r s (ro1' r s z) := by
  obtain ⟨x, y⟩ := z; simp only [I1, ro1'] at h ⊢; omega
theorem fi_I {z : ℤ × ℤ} (h : I0 r s z) : I1 r s (fi r s z) := by
  obtain ⟨x, y⟩ := z; simp only [I0, I1, fi] at h ⊢; omega
theorem ps_I {z : ℤ × ℤ} (h : I1 r s z) : I0 r s (ps r s z) := by
  obtain ⟨x, y⟩ := z; simp only [I0, I1, ps] at h ⊢; omega
theorem ro0_H {z : ℤ × ℤ} (h : H0 r s z) : H0 r s (ro0 r s z) := by
  obtain ⟨x, y⟩ := z; simp only [H0, ro0] at h ⊢; omega
theorem ro0'_H {z : ℤ × ℤ} (h : H0 r s z) : H0 r s (ro0' r s z) := by
  obtain ⟨x, y⟩ := z; simp only [H0, ro0'] at h ⊢; omega
theorem ro1_H {z : ℤ × ℤ} (h : H1 r s z) : H1 r s (ro1 r s z) := by
  obtain ⟨x, y⟩ := z; simp only [H1, ro1] at h ⊢; omega
theorem ro1'_H {z : ℤ × ℤ} (h : H1 r s z) : H1 r s (ro1' r s z) := by
  obtain ⟨x, y⟩ := z; simp only [H1, ro1'] at h ⊢; omega
theorem fi_H {z : ℤ × ℤ} (h : H0 r s z) : H1 r s (fi r s z) := by
  obtain ⟨x, y⟩ := z; simp only [H0, H1, fi] at h ⊢; omega
theorem ps_H {z : ℤ × ℤ} (h : H1 r s z) : H0 r s (ps r s z) := by
  obtain ⟨x, y⟩ := z; simp only [H0, H1, ps] at h ⊢; omega

theorem sg1_valid (hr : 1 ≤ r) (hs : 1 ≤ s) {v : MV} (h : Valid r s v) : Valid r s (sg1 r s v) := by
  obtain ⟨k, z⟩ := v
  rcases h with ⟨hk, hz⟩ | ⟨hk, hz⟩ | ⟨hk, h2, h0, h1⟩ <;> simp only at hk <;> subst hk
  · simp only [sg1, if_true]; rw [ch0_I (ro0_I hz)]; exact Or.inl ⟨rfl, ro0_I hz⟩
  · simp only [sg1, show ((1 : ℤ) = 0) = False by decide, if_false, if_true]
    rw [ch1_I (ro1_I hz)]; exact Or.inr (Or.inl ⟨rfl, ro1_I hz⟩)
  · simp only [sg1, show ((2 : ℤ) = 0) = False by decide, show ((2 : ℤ) = 1) = False by decide, if_false]
    obtain ⟨l, z2⟩ := z; simp only at h2 h0 h1 ⊢
    refine Or.inr (Or.inr ⟨rfl, rfl, ?_, ?_⟩) <;> simp only [sh1] <;> split_ifs <;> omega

theorem sg1'_valid (hr : 1 ≤ r) (hs : 1 ≤ s) {v : MV} (h : Valid r s v) : Valid r s (sg1' r s v) := by
  obtain ⟨k, z⟩ := v
  rcases h with ⟨hk, hz⟩ | ⟨hk, hz⟩ | ⟨hk, h2, h0, h1⟩ <;> simp only at hk <;> subst hk
  · simp only [sg1', if_true]; rw [ch0_I (ro0'_I hz)]; exact Or.inl ⟨rfl, ro0'_I hz⟩
  · simp only [sg1', show ((1 : ℤ) = 0) = False by decide, if_false, if_true]
    rw [ch1_I (ro1'_I hz)]; exact Or.inr (Or.inl ⟨rfl, ro1'_I hz⟩)
  · simp only [sg1', show ((2 : ℤ) = 0) = False by decide, show ((2 : ℤ) = 1) = False by decide, if_false]
    obtain ⟨l, z2⟩ := z; simp only at h2 h0 h1 ⊢
    refine Or.inr (Or.inr ⟨rfl, rfl, ?_, ?_⟩) <;> simp only [sh1'] <;> split_ifs <;> omega

theorem sg2_valid (hr : 1 ≤ r) (hs : 1 ≤ s) {v : MV} (h : Valid r s v) : Valid r s (sg2 r s v) := by
  obtain ⟨k, z⟩ := v
  rcases h with ⟨hk, hz⟩ | ⟨hk, hz⟩ | ⟨hk, h2, h0, h1⟩ <;> simp only at hk <;> subst hk
  · simp only [sg2, if_true]; rw [ch1_I (fi_I hz)]; exact Or.inr (Or.inl ⟨rfl, fi_I hz⟩)
  · simp only [sg2, show ((1 : ℤ) = 0) = False by decide, if_false, if_true]
    rw [ch0_I (ps_I hz)]; exact Or.inl ⟨rfl, ps_I hz⟩
  · simp only [sg2, show ((2 : ℤ) = 0) = False by decide, show ((2 : ℤ) = 1) = False by decide, if_false]
    obtain ⟨l, z2⟩ := z; simp only at h2 h0 h1 ⊢
    refine Or.inr (Or.inr ⟨rfl, rfl, ?_, ?_⟩) <;> simp only [sh2] <;> split_ifs <;> omega

theorem sg1'_sg1 (hr : 1 ≤ r) (hs : 1 ≤ s) {v : MV} (h : Valid r s v) : sg1' r s (sg1 r s v) = v := by
  obtain ⟨k, z⟩ := v
  rcases h with ⟨hk, hz⟩ | ⟨hk, hz⟩ | ⟨hk, h2, h0, h1⟩ <;> simp only at hk <;> subst hk
  · simp only [sg1, if_true]; rw [ch0_I (ro0_I hz)]; simp only [sg1', if_true]
    rw [show ro0' r s (ro0 r s z) = z by obtain ⟨x, y⟩ := z; simp only [ro0, ro0', Prod.mk.injEq]; omega, ch0_I hz]
  · simp only [sg1, show ((1 : ℤ) = 0) = False by decide, if_false, if_true]; rw [ch1_I (ro1_I hz)]
    simp only [sg1', show ((1 : ℤ) = 0) = False by decide, if_false, if_true]
    rw [show ro1' r s (ro1 r s z) = z by obtain ⟨x, y⟩ := z; simp only [ro1, ro1', Prod.mk.injEq]; omega, ch1_I hz]
  · obtain ⟨l, z2⟩ := z; simp only at h2 h0 h1; subst h2
    simp only [sg1, sg1', show ((2 : ℤ) = 0) = False by decide, show ((2 : ℤ) = 1) = False by decide, if_false,
      Prod.mk.injEq, true_and, and_true]
    simp only [sh1, sh1']; split_ifs <;> omega

theorem sg1_sg1' (hr : 1 ≤ r) (hs : 1 ≤ s) {v : MV} (h : Valid r s v) : sg1 r s (sg1' r s v) = v := by
  obtain ⟨k, z⟩ := v
  rcases h with ⟨hk, hz⟩ | ⟨hk, hz⟩ | ⟨hk, h2, h0, h1⟩ <;> simp only at hk <;> subst hk
  · simp only [sg1', if_true]; rw [ch0_I (ro0'_I hz)]; simp only [sg1, if_true]
    rw [show ro0 r s (ro0' r s z) = z by obtain ⟨x, y⟩ := z; simp only [ro0, ro0', Prod.mk.injEq]; omega, ch0_I hz]
  · simp only [sg1', show ((1 : ℤ) = 0) = False by decide, if_false, if_true]; rw [ch1_I (ro1'_I hz)]
    simp only [sg1, show ((1 : ℤ) = 0) = False by decide, if_false, if_true]
    rw [show ro1 r s (ro1' r s z) = z by obtain ⟨x, y⟩ := z; simp only [ro1, ro1', Prod.mk.injEq]; omega, ch1_I hz]
  · obtain ⟨l, z2⟩ := z; simp only at h2 h0 h1; subst h2
    simp only [sg1, sg1', show ((2 : ℤ) = 0) = False by decide, show ((2 : ℤ) = 1) = False by decide, if_false,
      Prod.mk.injEq, true_and, and_true]
    simp only [sh1, sh1']; split_ifs <;> omega

theorem sg2_sg2 (hr : 1 ≤ r) (hs : 1 ≤ s) {v : MV} (h : Valid r s v) : sg2 r s (sg2 r s v) = v := by
  obtain ⟨k, z⟩ := v
  rcases h with ⟨hk, hz⟩ | ⟨hk, hz⟩ | ⟨hk, h2, h0, h1⟩ <;> simp only at hk <;> subst hk
  · simp only [sg2, if_true]; rw [ch1_I (fi_I hz)]
    simp only [show ((1 : ℤ) = 0) = False by decide, if_false, if_true]
    rw [show ps r s (fi r s z) = z by obtain ⟨x, y⟩ := z; simp only [fi, ps, Prod.mk.injEq]; omega, ch0_I hz]
  · simp only [sg2, show ((1 : ℤ) = 0) = False by decide, if_false, if_true]; rw [ch0_I (ps_I hz)]
    simp only [if_true]
    rw [show fi r s (ps r s z) = z by obtain ⟨x, y⟩ := z; simp only [fi, ps, Prod.mk.injEq]; omega, ch1_I hz]
  · obtain ⟨l, z2⟩ := z; simp only at h2 h0 h1; subst h2
    simp only [sg2, show ((2 : ℤ) = 0) = False by decide, show ((2 : ℤ) = 1) = False by decide, if_false,
      Prod.mk.injEq, true_and, and_true]
    simp only [sh2]; split_ifs <;> omega

/-- A map that sends every chart point to a chart point by a lattice isometry preserves `AdjM`. -/
theorem adjM_map (f : MV → MV) (ρ : ℕ → ℤ × ℤ → ℤ × ℤ) (hinj : ∀ v w, Valid r s v → Valid r s w → f v = f w → v = w)
    (hval : ∀ v, Valid r s v → Valid r s (f v)) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hch : ∀ c, c < 2 → ∀ z, Dom r s c z → ∃ c', c' < 2 ∧ Dom r s c' (ρ c z) ∧ f (ch r s c z) = ch r s c' (ρ c z) ∧
      ∀ u ∈ unitVec, Dom r s c (z + u) → ρ c (z + u) - ρ c z ∈ unitVec ∧ Dom r s c' (ρ c (z + u)) ∧
        f (ch r s c (z + u)) = ch r s c' (ρ c (z + u)))
    {v w : MV} (hv : Valid r s v) (hw : Valid r s w) (h : AdjM r s v w) : AdjM r s (f v) (f w) := by
  obtain ⟨hne, c, hc, z, u, h1, h2, hu, rfl, rfl⟩ := h
  obtain ⟨c', hc', hd, e1, hrest⟩ := hch c hc z h1
  obtain ⟨hu', hd', e2⟩ := hrest u hu h2
  refine ⟨fun e => hne (hinj _ _ hv hw e), c', hc', ρ c z, ρ c (z + u) - ρ c z, hd, by simpa using hd', hu', e1.symm, ?_⟩
  rw [e2]; simp

end Claude7D12
