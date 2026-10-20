import Formal.Claude5O2DegGenB
import Formal.Claude5O2Iso

/-!
# O2 model: a vertex of degree five is one of the twelve corners (`t, d ≥ 2`)

Written by a Claude worker (2026-10-20, O2 bridge session).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

variable {t d : ℤ}

theorem hx_all {ρ : ℤ × ℤ}
    (hI : 0 < ρ.2 ∧ ρ.1 < 2 * t ∧ ρ.1 + ρ.2 < 2 * t + d ∧ ρ.2 < 2 * t + d ∧ -d < ρ.1 ∧
      0 < ρ.1 + ρ.2) : ∀ u ∈ unitVec, Hx t d (ρ + u) := by
  intro u hu
  rw [unit_iff] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Hx] <;> omega

theorem deg_hex0 (ht : 2 ≤ t) (hd : 2 ≤ d) (v : MS t d) {ρ : ℤ × ℤ} (hρ : Hx t d ρ)
    (hv : v.1 = ch t d 0 ρ) (hnc : ¬ IsCorner t d v.1) : deg (GM t d) v ≠ 5 := by
  have ht1 : (1 : ℤ) ≤ t := by omega
  have hd1 : (1 : ℤ) ≤ d := by omega
  by_cases hI : 0 < ρ.2 ∧ ρ.1 < 2 * t ∧ ρ.1 + ρ.2 < 2 * t + d ∧ ρ.2 < 2 * t + d ∧ -d < ρ.1 ∧
      0 < ρ.1 + ρ.2
  · exact deg_interior ht1 hd1 (c := 0) (by norm_num) v hρ hv (hx_all hI)
  have hρ' := hρ
  simp only [Hx] at hρ'
  have corner : ∀ a b : ℤ, ρ = (a, b) → IsCorner t d (0, (a, b)) → False := by
    intro a b e hc; apply hnc; rw [hv, ch0, e]; exact hc
  have hs : ρ.2 = 0 ∨ ρ.1 = 2 * t ∨ ρ.1 + ρ.2 = 2 * t + d ∨ ρ.2 = 2 * t + d ∨ ρ.1 = -d ∨
      ρ.1 + ρ.2 = 0 := by omega
  obtain ⟨ρ1, ρ2⟩ := ρ
  simp only at hs hρ' hI
  rcases hs with h | h | h | h | h | h
  · rcases (show ρ1 = 0 ∨ (0 < ρ1 ∧ ρ1 < t) ∨ ρ1 = t ∨ (t < ρ1 ∧ ρ1 < 2 * t) ∨ ρ1 = 2 * t by omega)
      with h' | h' | h' | h' | h'
    · exact (corner _ _ rfl (by rw [h', h]; simp [IsCorner, corners, sp])).elim
    · exact deg_S0_0_0 ht hd v hρ ⟨h, h'⟩ hv
    · exact (corner _ _ rfl (by rw [h', h]; simp [IsCorner, corners, sp])).elim
    · exact deg_S0_0_1 ht hd v hρ ⟨h, h'⟩ hv
    · exact (corner _ _ rfl (by rw [h', h]; simp [IsCorner, corners, sp])).elim
  · rcases (show ρ2 = 0 ∨ (0 < ρ2 ∧ ρ2 < d) ∨ ρ2 = d by omega) with h' | h' | h'
    · exact (corner _ _ rfl (by rw [h', h]; simp [IsCorner, corners, sp])).elim
    · exact deg_D0 ht hd v hρ ⟨h, h'⟩ hv
    · exact (corner _ _ rfl (by rw [h', h]; simp [IsCorner, corners, sp]; try (ring_nf; simp))).elim
  · have e : ρ1 = 2 * t + d - ρ2 := by omega
    rcases (show ρ2 - d = 0 ∨ (0 < ρ2 - d ∧ ρ2 - d < t) ∨ ρ2 - d = t ∨
        (t < ρ2 - d ∧ ρ2 - d < 2 * t) ∨ ρ2 - d = 2 * t by omega) with h' | h' | h' | h' | h'
    · exact (corner _ _ rfl (by rw [e, show ρ2 = d by omega]; simp [IsCorner, corners, sp]; try (ring_nf; simp))).elim
    · exact deg_S0_1_0 ht hd v hρ ⟨h, h'⟩ hv
    · exact (corner _ _ rfl (by rw [e, show ρ2 = t + d by omega]; simp [IsCorner, corners, sp]; try (ring_nf; simp))).elim
    · exact deg_S0_1_1 ht hd v hρ ⟨h, h'⟩ hv
    · exact (corner _ _ rfl (by rw [e, show ρ2 = 2 * t + d by omega]; simp [IsCorner, corners, sp]; try (ring_nf; simp))).elim
  · rcases (show ρ1 = 0 ∨ (-d < ρ1 ∧ ρ1 < 0) ∨ ρ1 = -d by omega) with h' | h' | h'
    · exact (corner _ _ rfl (by rw [h', h]; simp [IsCorner, corners, sp])).elim
    · exact deg_D1 ht hd v hρ ⟨h, h'⟩ hv
    · exact (corner _ _ rfl (by rw [h', h]; simp [IsCorner, corners, sp])).elim
  · rcases (show 2 * t + d - ρ2 = 0 ∨ (0 < 2 * t + d - ρ2 ∧ 2 * t + d - ρ2 < t) ∨
        2 * t + d - ρ2 = t ∨ (t < 2 * t + d - ρ2 ∧ 2 * t + d - ρ2 < 2 * t) ∨
        2 * t + d - ρ2 = 2 * t by omega) with h' | h' | h' | h' | h'
    · exact (corner _ _ rfl (by rw [h, show ρ2 = 2 * t + d by omega]; simp [IsCorner, corners, sp])).elim
    · exact deg_S0_2_0 ht hd v hρ ⟨h, h'⟩ hv
    · exact (corner _ _ rfl (by rw [h, show ρ2 = t + d by omega]; simp [IsCorner, corners, sp]; try (ring_nf; simp))).elim
    · exact deg_S0_2_1 ht hd v hρ ⟨h, h'⟩ hv
    · exact (corner _ _ rfl (by rw [h, show ρ2 = d by omega]; simp [IsCorner, corners, sp]; try (ring_nf; simp))).elim
  · rcases (show ρ1 = 0 ∨ (-d < ρ1 ∧ ρ1 < 0) ∨ ρ1 = -d by omega) with h' | h' | h'
    · exact (corner _ _ rfl (by rw [h', show ρ2 = 0 by omega]; simp [IsCorner, corners, sp])).elim
    · exact deg_D2 ht hd v hρ ⟨h, h'⟩ hv
    · exact (corner _ _ rfl (by rw [h', show ρ2 = d by omega]; simp [IsCorner, corners, sp])).elim

theorem deg_hex1 (ht : 2 ≤ t) (hd : 2 ≤ d) (v : MS t d) {ρ : ℤ × ℤ} (hρ : Hx t d ρ)
    (hv : v.1 = ch t d 1 ρ) (hnc : ¬ IsCorner t d v.1) : deg (GM t d) v ≠ 5 := by
  have ht1 : (1 : ℤ) ≤ t := by omega
  have hd1 : (1 : ℤ) ≤ d := by omega
  by_cases hD : OnD t d ρ
  · exact deg_hex0 ht hd v hρ (by rw [hv, ch1_onD hD]; rfl) hnc
  by_cases hI : 0 < ρ.2 ∧ ρ.1 < 2 * t ∧ ρ.1 + ρ.2 < 2 * t + d ∧ ρ.2 < 2 * t + d ∧ -d < ρ.1 ∧
      0 < ρ.1 + ρ.2
  · exact deg_interior ht1 hd1 (c := 1) (by norm_num) v hρ hv (hx_all hI)
  have hρ' := hρ
  simp only [Hx, OnD] at hρ' hD
  have corner : ∀ a b : ℤ, ρ = (a, b) → IsCorner t d (1, (a, b)) → False := by
    intro a b e hc; apply hnc; rw [hv, ch1_nD (by simp only [OnD]; exact hD), e]; exact hc
  have hs : ρ.2 = 0 ∨ ρ.1 + ρ.2 = 2 * t + d ∨ ρ.1 = -d := by omega
  obtain ⟨ρ1, ρ2⟩ := ρ
  simp only at hs hρ' hI hD
  rcases hs with h | h | h
  · rcases (show (0 < ρ1 ∧ ρ1 < t) ∨ ρ1 = t ∨ (t < ρ1 ∧ ρ1 < 2 * t) by omega) with h' | h' | h'
    · exact deg_S1_0_0 ht hd v hρ ⟨h, h'⟩ hv
    · exact (corner _ _ rfl (by rw [h', h]; simp [IsCorner, corners, sp])).elim
    · exact deg_S1_0_1 ht hd v hρ ⟨h, h'⟩ hv
  · have e : ρ1 = 2 * t + d - ρ2 := by omega
    rcases (show (0 < ρ2 - d ∧ ρ2 - d < t) ∨ ρ2 - d = t ∨ (t < ρ2 - d ∧ ρ2 - d < 2 * t) by omega)
      with h' | h' | h'
    · exact deg_S1_1_0 ht hd v hρ ⟨h, h'⟩ hv
    · exact (corner _ _ rfl (by rw [e, show ρ2 = t + d by omega]; simp [IsCorner, corners, sp]; try (ring_nf; simp))).elim
    · exact deg_S1_1_1 ht hd v hρ ⟨h, h'⟩ hv
  · rcases (show (0 < 2 * t + d - ρ2 ∧ 2 * t + d - ρ2 < t) ∨ 2 * t + d - ρ2 = t ∨
        (t < 2 * t + d - ρ2 ∧ 2 * t + d - ρ2 < 2 * t) by omega) with h' | h' | h'
    · exact deg_S1_2_0 ht hd v hρ ⟨h, h'⟩ hv
    · exact (corner _ _ rfl (by rw [h, show ρ2 = t + d by omega]; simp [IsCorner, corners, sp]; try (ring_nf; simp))).elim
    · exact deg_S1_2_1 ht hd v hρ ⟨h, h'⟩ hv

/-- **Degree five means corner** (`t, d ≥ 2`). -/
theorem deg_five (ht : 2 ≤ t) (hd : 2 ≤ d) (v : MS t d) (h : deg (GM t d) v = 5) :
    IsCorner t d v.1 := by
  have ht1 : (1 : ℤ) ≤ t := by omega
  have hd1 : (1 : ℤ) ≤ d := by omega
  by_contra hnc
  obtain ⟨c, hc, ρ, hρ, hv⟩ := valid_rep v.2
  rcases c_cases (c := c) with rfl | rfl | ⟨j, rfl⟩
  · exact deg_hex0 ht hd v hρ hv.symm hnc h
  · exact deg_hex1 ht hd v hρ hv.symm hnc h
  · have hj : j < 3 := by omega
    by_cases hI : RhI t ρ
    · refine deg_interior ht1 hd1 hc v hρ hv.symm (fun u hu => ?_) h
      rw [unit_iff] at hu
      simp only [RhI] at hI
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Dom, Rh] <;> omega
    · simp only [Dom, Rh] at hρ
      have hz : ρ.1 = 0 ∨ (ρ.2 = t ∧ 0 ≤ ρ.1) ∨ (ρ.2 = 0 ∧ 0 ≤ ρ.1) ∨ ρ.1 = t := by
        simp only [RhI] at hI; omega
      rcases hz with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
      · exact deg_hex0 ht hd v (sp_hx (l := ρ.2) ht1 hd1 hj (by omega) (by omega))
          (by rw [← hv, chR_AB ht1 j h1]) hnc h
      · exact deg_hex0 ht hd v (sp_hx (l := t + ρ.1) ht1 hd1 hj (by omega) (by omega))
          (by rw [← hv, chR_BC ht1 j h1 h2]) hnc h
      · exact deg_hex1 ht hd v (sp_hx (l := ρ.1) ht1 hd1 hj (by omega) (by omega))
          (by rw [← hv, chR_AD ht1 hd1 hj h1 h2 (by omega)]) hnc h
      · exact deg_hex1 ht hd v (sp_hx (l := t + ρ.2) ht1 hd1 hj (by omega) (by omega))
          (by rw [← hv, chR_DC ht1 hd1 hj h1 (by omega) (by omega)]) hnc h

end Claude5O2
