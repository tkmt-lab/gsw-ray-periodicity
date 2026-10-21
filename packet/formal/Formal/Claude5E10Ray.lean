import Formal.Claude5E10Model
import Mathlib.Tactic.Ring

/-!
# E10: eventual periodicity of divisibility along integer rays

Written by a Claude worker (2026-10-20, E10 bridge session).

* `EvPer P` : `P` is eventually periodic;
* `evper_or`, `evper_congr` : closure properties;
* `evper_dvd` : `n ↦ (m₀ + μ n ∣ l₀ + λ n)` is eventually periodic when `m₀ + μ n > 0`
  (for `μ = 0` it is periodic; for `μ > 0` eventually constant, since `m ∣ L` forces
  `m ∣ μ L − λ m`, a constant).
-/

namespace Claude5E10

/-- Eventual periodicity of a predicate on `ℕ`. -/
def EvPer (P : ℕ → Prop) : Prop := ∃ n₀ T : ℕ, 0 < T ∧ ∀ n, n₀ ≤ n → (P n ↔ P (n + T))

theorem evper_mul {P : ℕ → Prop} {n₀ T : ℕ} (h : ∀ n, n₀ ≤ n → (P n ↔ P (n + T))) (k : ℕ) :
    ∀ n, n₀ ≤ n → (P n ↔ P (n + T * k)) := by
  induction k with
  | zero => intro n _; simp
  | succ k ih =>
    intro n hn
    rw [ih n hn, show n + T * (k + 1) = (n + T * k) + T by ring]
    exact h _ (by omega)

theorem evper_or {P Q : ℕ → Prop} (hP : EvPer P) (hQ : EvPer Q) : EvPer (fun n => P n ∨ Q n) := by
  obtain ⟨n₁, T₁, h₁, e₁⟩ := hP
  obtain ⟨n₂, T₂, h₂, e₂⟩ := hQ
  refine ⟨max n₁ n₂, T₁ * T₂, Nat.mul_pos h₁ h₂, fun n hn => ?_⟩
  have a := evper_mul e₁ T₂ n (by omega)
  have b := evper_mul e₂ T₁ n (by omega)
  rw [mul_comm T₂ T₁] at b
  simp only
  rw [a, b]

theorem evper_congr {P Q : ℕ → Prop} (hP : EvPer P) (N : ℕ) (h : ∀ n, N ≤ n → (P n ↔ Q n)) :
    EvPer Q := by
  obtain ⟨n₀, T, hT, e⟩ := hP
  refine ⟨max n₀ N, T, hT, fun n hn => ?_⟩
  rw [← h n (by omega), ← h (n + T) (by omega)]
  exact e n (by omega)

theorem evper_const (P : Prop) : EvPer (fun _ => P) := ⟨0, 1, by norm_num, fun _ _ => Iff.rfl⟩

theorem evper_eventually_const {P : ℕ → Prop} (Q : Prop) (N : ℕ) (h : ∀ n, N ≤ n → (P n ↔ Q)) :
    EvPer P := by
  refine evper_congr (evper_const Q) N (fun n hn => (h n hn).symm)

/-- **Divisibility along rays.** -/
theorem evper_dvd (m₀ μ l₀ lam : ℤ) (hμ : 0 ≤ μ) (hm : ∀ n : ℕ, 0 < m₀ + μ * n) :
    EvPer (fun n : ℕ => (m₀ + μ * n) ∣ (l₀ + lam * n)) := by
  rcases eq_or_lt_of_le hμ with h0 | hpos
  · -- constant modulus: periodic
    subst h0
    simp only [zero_mul, add_zero] at hm ⊢
    have hM := hm 0
    refine ⟨0, m₀.toNat, by omega, fun n _ => ?_⟩
    have : l₀ + lam * ((n + m₀.toNat : ℕ) : ℤ) = (l₀ + lam * n) + m₀ * lam := by
      push_cast; rw [show (m₀.toNat : ℤ) = m₀ by omega]; ring
    simp only
    rw [this]
    exact (dvd_add_left (dvd_mul_right m₀ lam)).symm
  · set C := μ * l₀ - lam * m₀
    have key : ∀ n : ℕ, μ * (l₀ + lam * n) - lam * (m₀ + μ * n) = C := by intro n; ring
    by_cases hC : C = 0
    · by_cases hd : μ ∣ lam
      · obtain ⟨t, ht⟩ := hd
        refine evper_eventually_const True 0 (fun n _ => ⟨fun _ => trivial, fun _ => ⟨t, ?_⟩⟩)
        have := key n
        rw [hC, ht] at this
        have : μ * ((l₀ + μ * t * n) - t * (m₀ + μ * n)) = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · omega
        · subst ht; linarith
      · refine evper_eventually_const False 0 (fun n _ => ⟨fun ⟨t, ht⟩ => hd ?_, False.elim⟩)
        refine ⟨t, ?_⟩
        have := key n
        rw [hC, ht] at this
        have h2 : (m₀ + μ * n) * (μ * t - lam) = 0 := by linarith
        rcases mul_eq_zero.1 h2 with h | h
        · have := hm n; omega
        · linarith
    · -- eventually the modulus exceeds |C|
      refine evper_eventually_const False (C.natAbs + 1) (fun n hn => ⟨fun hdvd => ?_, False.elim⟩)
      have h1 : (m₀ + μ * n) ∣ C := by
        rw [← key n]
        exact dvd_sub (dvd_mul_of_dvd_right hdvd _) (dvd_mul_left _ _)
      have h2 := Int.le_of_dvd (by positivity) (show (m₀ + μ * n) ∣ C.natAbs by
        exact (Int.dvd_natAbs).2 h1)
      have h3 : (n : ℤ) ≥ C.natAbs + 1 := by exact_mod_cast hn
      have h4 : μ * n ≥ n := by nlinarith
      have h5 := hm 0
      simp at h5
      have : (0 : ℤ) < C.natAbs := by
        have := Int.natAbs_pos.2 hC; exact_mod_cast this
      nlinarith

end Claude5E10
