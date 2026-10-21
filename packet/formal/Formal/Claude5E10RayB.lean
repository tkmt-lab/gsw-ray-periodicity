import Formal.Claude5E10SigAdj
import Formal.Claude5E10MainA

/-!
# E10 on rays with `r = 1`, by Theorem 1a, and all rays

Written by a Claude worker (2026-10-21, E10 bridge session).

* `rp_evper` : if `p, r, s, w` are affine in `t` and eventually `p, r, s ≥ 1` and
  `w = p mod 3m`, path existence in E10 is eventually periodic in `t` (Theorem 1a,
  `ClaudeChallenge2.State.main_statement`, applied to `e10S Q`);
* `evper_classes` : eventual periodicity on each residue class gives it on `ℕ`;
* `eventual_quot` : `(p₀ + a n) div (m₀ + μ n)` is eventually constant (`μ ≥ 1`);
* `rays_B` : rays with `r = 1` (`r₀ = 1`, `b = 0`);
* `e10_rays` : all rays.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge2 (Aff Chart)

/-- **Affine families** (from Theorem 1a in the form `T1aGM`). -/
theorem rp_evper (hT : T1aGM) (Q : RP) (t₁ : ℕ)
    (hQ' : ∀ t, t₁ ≤ t → 1 ≤ Q.p t ∧ 1 ≤ Q.r t ∧ 1 ≤ Q.s t ∧ 0 ≤ Q.w t ∧
      Q.w t < 3 * (2 * Q.r t + Q.s t) ∧ ∃ k : ℤ, Q.p t = 3 * (2 * Q.r t + Q.s t) * k + Q.w t) :
    EvPer (fun t => ∃ n q, ClaudeChallenge.LiteralPath
      (Claude2Aligned.e10Graph (Q.p t) (Q.r t) (Q.s t)) n q) := by
  have hQ : ∀ t, t₁ ≤ t → 1 ≤ Q.p t ∧ 1 ≤ Q.r t ∧ 1 ≤ Q.s t ∧
      Q.w t = Q.p t % (3 * (2 * Q.r t + Q.s t)) := by
    intro t ht
    obtain ⟨a, b, c, d0, d1, k, hk⟩ := hQ' t ht
    exact ⟨a, b, c, (emod_eq_of (by omega) hk d0 d1).symm⟩
  have hH : ∀ t, t₁ ≤ t → Hyp (Q.p t) (Q.r t) (Q.s t) (Q.w t) := by
    intro t ht
    obtain ⟨a, b, c, d0, d1, -⟩ := hQ' t ht
    exact ⟨a, b, c, d0, d1⟩
  refine evper_congr (hT Q t₁ hH) t₁ (fun t ht => ?_)
  obtain ⟨a, b, c, d⟩ := hQ t ht
  beta_reduce
  rw [e10_iff_gm a b c, ← d]

/-- Finite product and sum (by recursion). -/
def prodT (T : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => prodT T k * T k

def sumN (T : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => sumN T k + T k

theorem prodT_pos {T : ℕ → ℕ} (h : ∀ i, 0 < T i) (k : ℕ) : 0 < prodT T k := by
  induction k with
  | zero => simp [prodT]
  | succ k ih => simp only [prodT]; exact Nat.mul_pos ih (h k)

theorem dvd_prodT (T : ℕ → ℕ) {i k : ℕ} (hi : i < k) : T i ∣ prodT T k := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [prodT]
    rcases (show i < k ∨ i = k by omega) with h | rfl
    · exact Dvd.dvd.mul_right (ih h) _
    · exact Dvd.intro_left _ rfl

theorem le_sumN (T : ℕ → ℕ) {i k : ℕ} (hi : i < k) : T i ≤ sumN T k := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [sumN]
    rcases (show i < k ∨ i = k by omega) with h | rfl
    · have := ih h; omega
    · omega

/-- **Residue classes.** -/
theorem evper_classes {P : ℕ → Prop} (N L : ℕ) (hL : 0 < L)
    (h : ∀ i, i < L → EvPer (fun t => P (N + i + L * t))) : EvPer P := by
  have h' : ∀ i, ∃ n₀ T : ℕ, 0 < T ∧
      (i < L → ∀ t, n₀ ≤ t → (P (N + i + L * t) ↔ P (N + i + L * (t + T)))) := by
    intro i
    by_cases hi : i < L
    · obtain ⟨n₀, T, hT, e⟩ := h i hi
      exact ⟨n₀, T, hT, fun _ t ht => e t ht⟩
    · exact ⟨0, 1, Nat.one_pos, fun h => absurd h hi⟩
  choose n₀ T hT e using h'
  have hTT : 0 < prodT T L := prodT_pos hT L
  refine ⟨N + L * sumN n₀ L, L * prodT T L, Nat.mul_pos hL hTT, fun n hn => ?_⟩
  set S := sumN n₀ L
  set TT := prodT T L
  have hi : (n - N) % L < L := Nat.mod_lt _ hL
  have hn' : n = N + (n - N) % L + L * ((n - N) / L) := by
    have := Nat.mod_add_div (n - N) L; omega
  have hq : S ≤ (n - N) / L := by
    rw [Nat.le_div_iff_mul_le hL, mul_comm]; omega
  obtain ⟨k, hk⟩ := dvd_prodT T hi
  have hle : n₀ ((n - N) % L) ≤ S := le_sumN n₀ hi
  have := evper_mul (P := fun t => P (N + (n - N) % L + L * t)) (e _ hi) k ((n - N) / L)
    (le_trans hle hq)
  rw [hn', show N + (n - N) % L + L * ((n - N) / L) + L * TT =
    N + (n - N) % L + L * ((n - N) / L + T ((n - N) % L) * k) by rw [← hk]; ring]
  exact this

/-- **Eventually constant quotients.** -/
theorem eventual_quot (p₀ a M₀ μ : ℤ) (hμ : 1 ≤ μ) (hM : 1 ≤ M₀) (ha : 0 ≤ a) :
    ∃ (Qq : ℤ) (N : ℕ), ∀ n : ℕ, N ≤ n →
      0 ≤ (p₀ + a * n) - Qq * (M₀ + μ * n) ∧ (p₀ + a * n) - Qq * (M₀ + μ * n) < M₀ + μ * n := by
  have hd := Int.mul_ediv_add_emod a μ
  have h0 := Int.emod_nonneg a (show μ ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos a (show 0 < μ by omega)
  set q := a / μ
  set ρ := a % μ
  set K := p₀ - q * M₀
  by_cases hρ : 0 < ρ
  · refine ⟨q, (|K| + |K - M₀|).toNat + 1, fun n hn => ?_⟩
    have hn' : (|K| + |K - M₀| : ℤ) + 1 ≤ n := by
      have := Int.toNat_of_nonneg (show (0 : ℤ) ≤ |K| + |K - M₀| by positivity); omega
    have e : (p₀ + a * n) - q * (M₀ + μ * n) = K + ρ * n := by
      rw [← hd]; simp only [K]; ring
    rw [e]
    have a1 := le_abs_self K; have a2 := neg_abs_le K
    have b1 := le_abs_self (K - M₀); have b2 := neg_abs_le (K - M₀)
    have hn0 : (0 : ℤ) ≤ n := by positivity
    constructor
    · nlinarith
    · nlinarith
  · have hρ0 : ρ = 0 := by omega
    by_cases hK : 0 ≤ K
    · refine ⟨q, K.toNat + 1, fun n hn => ?_⟩
      have hn' : K + 1 ≤ n := by have := Int.toNat_of_nonneg hK; omega
      have e : (p₀ + a * n) - q * (M₀ + μ * n) = K := by
        rw [← hd, hρ0]; simp only [K]; ring
      rw [e]
      have hn0 : (0 : ℤ) ≤ n := by positivity
      constructor
      · exact hK
      · nlinarith
    · refine ⟨q - 1, (-K).toNat + 1, fun n hn => ?_⟩
      have hn' : -K + 1 ≤ n := by have := Int.toNat_of_nonneg (show 0 ≤ -K by omega); omega
      have e : (p₀ + a * n) - (q - 1) * (M₀ + μ * n) = K + (M₀ + μ * n) := by
        rw [← hd, hρ0]; simp only [K]; ring
      rw [e]
      have hn0 : (0 : ℤ) ≤ n := by positivity
      constructor
      · nlinarith
      · omega

/-- The path predicate along a ray. -/
def PR (p₀ r₀ s₀ a b c : ℕ) (n : ℕ) : Prop :=
  ∃ k q, ClaudeChallenge.LiteralPath (Claude2Aligned.e10Graph ((p₀ + a * n : ℕ) : ℤ)
    ((r₀ + b * n : ℕ) : ℤ) ((s₀ + c * n : ℕ) : ℤ)) k q

theorem pr_congr {p₀ r₀ s₀ a b c n : ℕ} {Q : RP} {t : ℕ}
    (e1 : Q.p t = ((p₀ + a * n : ℕ) : ℤ)) (e2 : Q.r t = ((r₀ + b * n : ℕ) : ℤ))
    (e3 : Q.s t = ((s₀ + c * n : ℕ) : ℤ)) :
    (∃ n q, ClaudeChallenge.LiteralPath (Claude2Aligned.e10Graph (Q.p t) (Q.r t) (Q.s t)) n q) ↔
      PR p₀ r₀ s₀ a b c n := by
  rw [e1, e2, e3]; rfl

/-- **Rays with `r = 1`.** -/
theorem rays_B (hT : T1aGM) (p₀ s₀ a c : ℕ) (hp : 1 ≤ p₀) (hs : 1 ≤ s₀) : EvPer (PR p₀ 1 s₀ a 0 c) := by
  rcases Nat.eq_zero_or_pos c with hc | hc
  · -- constant tube: classes modulo `3m`
    subst hc
    have hL : 0 < 3 * (2 + s₀) := by omega
    refine evper_classes 0 (3 * (2 + s₀)) hL (fun i hi => ?_)
    obtain ⟨X, hX⟩ : ∃ X : ℤ, X = p₀ + a * i := ⟨_, rfl⟩
    have hX1 : 1 ≤ X := by rw [hX]; have : (0 : ℤ) ≤ a * i := by positivity
                           omega
    obtain ⟨hd, h0, h1⟩ := emod_decomp (show (0 : ℤ) < 3 * (2 + s₀) by omega) X
    generalize X / (3 * (2 + s₀)) = qX at hd
    generalize X % (3 * (2 + s₀)) = W0 at hd h0 h1
    let Q : RP := ⟨⟨a * (3 * (2 + s₀)), X⟩, ⟨0, 1⟩, ⟨0, s₀⟩, ⟨0, W0⟩⟩
    refine evper_congr (rp_evper hT Q 0 (fun t _ => ?_)) 0 (fun t _ => pr_congr ?_ ?_ ?_)
    · simp only [Q, RP.p, RP.r, RP.s, RP.w, Aff.eval]
      have : (0 : ℤ) ≤ a * (3 * (2 + s₀)) * t := by positivity
      refine ⟨by linarith, by omega, by omega, by linarith, by linarith, qX + a * t, ?_⟩
      rw [hd]; ring
    · simp only [Q, RP.p, Aff.eval]; rw [hX]; push_cast; ring
    · simp only [Q, RP.r, Aff.eval]; push_cast; ring
    · simp only [Q, RP.s, Aff.eval]; push_cast; ring
  · -- growing tube: the quotient by `3m` is eventually constant
    obtain ⟨Qq, N, hN⟩ := eventual_quot (p₀ : ℤ) a (3 * (2 + s₀)) (3 * c) (by omega) (by omega)
      (by positivity)
    refine evper_classes N 1 Nat.one_pos (fun i hi => ?_)
    have hi0 : i = 0 := by omega
    subst hi0
    let Q : RP := ⟨⟨a, p₀ + a * N⟩, ⟨0, 1⟩, ⟨c, s₀ + c * N⟩,
      ⟨a - Qq * (3 * c), (p₀ + a * N) - Qq * (3 * (2 + s₀) + 3 * c * N)⟩⟩
    refine evper_congr (rp_evper hT Q 0 (fun t _ => ?_)) 0 (fun t _ => pr_congr ?_ ?_ ?_)
    · obtain ⟨b0, b1⟩ := hN (N + t) (by omega)
      push_cast at b0 b1
      simp only [Q, RP.p, RP.r, RP.s, RP.w, Aff.eval]
      have e1 : (0 : ℤ) ≤ a * t := by positivity
      have e2 : (0 : ℤ) ≤ a * N := by positivity
      have e3 : (0 : ℤ) ≤ c * t := by positivity
      have e4 : (0 : ℤ) ≤ c * N := by positivity
      refine ⟨by linarith, by omega, by linarith, by linarith, by linarith, Qq, by ring⟩
    · simp only [Q, RP.p, Aff.eval]; push_cast; ring
    · simp only [Q, RP.r, Aff.eval]; push_cast; ring
    · simp only [Q, RP.s, Aff.eval]; push_cast; ring

/-- **All rays.** -/
theorem e10_rays (hT : T1aGM) (p₀ r₀ s₀ a b c : ℕ) (hp : 1 ≤ p₀) (hr : 1 ≤ r₀) (hs : 1 ≤ s₀) :
    EvPer (PR p₀ r₀ s₀ a b c) := by
  by_cases hb : 1 ≤ b ∨ 2 ≤ r₀
  · exact rays_A p₀ r₀ s₀ a b c hp hr hs hb
  · have h1 : b = 0 := by omega
    have h2 : r₀ = 1 := by omega
    subst h1 h2
    exact rays_B hT p₀ s₀ a c hp hs

end Claude5E10
