import Formal.Claude5E10Assemble4

/-!
# E10 model: arithmetic helpers for the generated region tables

Written by a Claude worker (2026-10-20, E10 bridge session).
-/

set_option linter.unusedVariables false

namespace Claude5E10

/-- An integer of the form `A + m Q` in a window of width `2m` around `A + m Q₀` has `Q = Q₀`. -/
theorem qfix {m X A QQ Q₀ : ℤ} (hm : 0 < m) (h : X = A + m * QQ) (h1 : A + m * (Q₀ - 1) < X)
    (h2 : X < A + m * (Q₀ + 1)) : QQ = Q₀ := by
  rcases lt_trichotomy QQ Q₀ with hq | hq | hq
  · exfalso
    have : m * QQ ≤ m * (Q₀ - 1) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  · exact hq
  · exfalso
    have : m * (Q₀ + 1) ≤ m * QQ := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega

/-- Non-divisibility from a window. -/
theorem not_dvd_of {m X Q₀ : ℤ} (hm : 0 < m) (h1 : 0 < X + m * Q₀) (h2 : X + m * Q₀ < m) :
    ¬ m ∣ X := by
  rintro ⟨c, rfl⟩
  have e : m * c + m * Q₀ = m * (c + Q₀) := by ring
  rw [e] at h1 h2
  rcases lt_trichotomy (c + Q₀) 0 with hq | hq | hq
  · have : m * (c + Q₀) ≤ m * (-1) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  · rw [hq] at h1; simp at h1
  · have : m * 1 ≤ m * (c + Q₀) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega

end Claude5E10
