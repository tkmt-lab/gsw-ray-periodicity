import Formal.Claude7D12Spec
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# D12: eventual periodicity of the condition along integer rays

Written by a Claude worker (2026-10-22, D12 bridge session).  The first part is
`Claude5E10Ray.lean` (E10 bridge session) restated in this namespace:

* `EvPer P` : `P` is eventually periodic; `evper_or`, `evper_congr`;
* `evper_dvd` : divisibility along rays is eventually periodic;
* `evper_abs_one` : `|α + β n| = 1` is eventually constant;
* `evper_cond` : the D12 condition along a ray `(r₀ + a n, s₀ + b n)`, `r₀ ≥ 1`.
-/

namespace Claude7D12

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

theorem evper_abs_one (α β : ℤ) : EvPer (fun n : ℕ => |α + β * n| = 1) := by
  by_cases hβ : β = 0
  · subst hβ; simp only [zero_mul, add_zero]; exact evper_const _
  · refine evper_eventually_const False (α.natAbs + 2) (fun n hn => ⟨fun h => ?_, False.elim⟩)
    have h3 : (n : ℤ) ≥ α.natAbs + 2 := by exact_mod_cast hn
    have hb : 1 ≤ |β| := Int.one_le_abs hβ
    have e1 : |β * n| = |β| * n := by rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ n)]
    have e2 : |β * (n : ℤ)| ≤ |α + β * n| + |α| := by
      have := abs_sub_abs_le_abs_sub (β * (n : ℤ)) (-α)
      have h' : β * (n : ℤ) - -α = α + β * n := by ring
      rw [h', abs_neg] at this; linarith
    have e3 : (|α| : ℤ) = α.natAbs := Int.abs_eq_natAbs α
    rw [h, e1, e3] at e2
    nlinarith

/-- **The D12 condition along a ray.** -/
theorem evper_cond (r₀ s₀ a b : ℕ) (hr : 1 ≤ r₀) :
    EvPer (fun n : ℕ => ((r₀ + a * n : ℕ) : ℤ) ∣ ((s₀ + b * n : ℕ) : ℤ) - 1 ∨
      ((r₀ + a * n : ℕ) : ℤ) ∣ ((s₀ + b * n : ℕ) : ℤ) + 1 ∨
      |((r₀ + a * n : ℕ) : ℤ) - 3 * ((s₀ + b * n : ℕ) : ℤ)| = 1) := by
  have hm : ∀ n : ℕ, 0 < (r₀ : ℤ) + (a : ℤ) * n := fun n => by positivity
  have d1 := evper_dvd r₀ a ((s₀ : ℤ) - 1) b (by positivity) hm
  have d2 := evper_dvd r₀ a ((s₀ : ℤ) + 1) b (by positivity) hm
  have d3 := evper_abs_one ((r₀ : ℤ) - 3 * s₀) ((a : ℤ) - 3 * b)
  refine evper_congr (evper_or d1 (evper_or d2 d3)) 0 (fun n _ => ?_)
  push_cast
  have e1 : (s₀ : ℤ) - 1 + b * n = s₀ + b * n - 1 := by ring
  have e2 : (s₀ : ℤ) + 1 + b * n = s₀ + b * n + 1 := by ring
  have e3 : (r₀ : ℤ) - 3 * s₀ + (a - 3 * b) * n = r₀ + a * n - 3 * (s₀ + b * n) := by ring
  rw [e1, e2, e3]

end Claude7D12
