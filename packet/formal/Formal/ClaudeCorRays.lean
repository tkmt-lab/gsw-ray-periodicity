import Formal.ClaudeMainPrimitive

/-!
# Corollary 4 of the A3 paper (`cor:rays`): eventual periodicity on integer affine rays

Let `k(t) = a t + b`, `l(t) = c t + d` with integer coefficients and `k(t) > l(t) > 0` for all
large `t`.

* `ClaudeCor.criterion_ray` (arithmetic, all rays, no primitivity assumption): the predicate
  `t ↦ criterion (k t) (l t)` on `ℕ` is eventually periodic. (`criterion` contains `gcd = 1`,
  so this covers the `Δ = ad - bc = 0` rays as well.)
* `ClaudeCor.path_ray_primitive` (graph): `t ↦ (gcd (k t) (l t) = 1 ∧ a literal path exists in
  gcGraph (k t) (l t))` is eventually periodic. This uses only `ClaudeMain.main_primitive`.
* `ClaudeCor.path_ray_of_primitive` (graph): if moreover `gcd (k t) (l t) = 1` for all large `t`,
  then `t ↦ ∃ literal path in gcGraph (k t) (l t)` is eventually periodic.

The general graph statement at nonprimitive points depends on the nonprimitive case of the
classification, which is not used here.

Method (a closure argument instead of the paper's case list): eventually periodic predicates are
closed under `∧ ∨ ¬` and under eventual equivalence; the atoms are affine sign tests, affine
divisibility `A(t) ∣ B(t)` and affine coprimality `gcd(A(t), B(t)) = 1`; eventually
`min(l, k - l)` is one affine function `M`, and `criterion k l` is then a boolean combination of
such atoms in `k` and `M` (`crit2_iff`).
-/

namespace ClaudeCor

open ClaudeChallenge

/-! ## Eventually true and eventually periodic predicates on `ℕ` -/

/-- `p t` holds for all sufficiently large `t`. -/
def Ev (p : ℕ → Prop) : Prop := ∃ T : ℕ, ∀ t, T ≤ t → p t

/-- `p` is eventually periodic: from `t₀` on, `p t ↔ p (t + P)` with `P > 0`. -/
def EvPer (p : ℕ → Prop) : Prop := ∃ t₀ P : ℕ, 0 < P ∧ ∀ t, t₀ ≤ t → (p t ↔ p (t + P))

theorem Ev.of_forall {p : ℕ → Prop} (h : ∀ t, p t) : Ev p := ⟨0, fun t _ => h t⟩

theorem Ev.mono {p q : ℕ → Prop} (hp : Ev p) (h : ∀ t, p t → q t) : Ev q := by
  obtain ⟨T, hT⟩ := hp
  exact ⟨T, fun t ht => h t (hT t ht)⟩

theorem Ev.and {p q : ℕ → Prop} (hp : Ev p) (hq : Ev q) : Ev (fun t => p t ∧ q t) := by
  obtain ⟨T, hT⟩ := hp
  obtain ⟨S, hS⟩ := hq
  exact ⟨max T S, fun t ht => ⟨hT t (le_of_max_le_left ht), hS t (le_of_max_le_right ht)⟩⟩

theorem EvPer.iter {p : ℕ → Prop} {t₀ P : ℕ} (h : ∀ t, t₀ ≤ t → (p t ↔ p (t + P))) :
    ∀ n t, t₀ ≤ t → (p t ↔ p (t + n * P)) := by
  intro n
  induction n with
  | zero => intro t _; simp
  | succ n ih =>
    intro t ht
    rw [ih t ht, h (t + n * P) (by omega), show t + n * P + P = t + (n + 1) * P by ring]

theorem EvPer.const (c : Prop) : EvPer (fun _ => c) := ⟨0, 1, one_pos, fun _ _ => Iff.rfl⟩

theorem EvPer.of_ev {p : ℕ → Prop} (h : Ev p) : EvPer p := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, 1, one_pos, fun t ht => iff_of_true (hT t ht) (hT (t + 1) (by omega))⟩

theorem EvPer.of_ev_not {p : ℕ → Prop} (h : Ev (fun t => ¬ p t)) : EvPer p := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, 1, one_pos, fun t ht => iff_of_false (hT t ht) (hT (t + 1) (by omega))⟩

theorem EvPer.congr {p q : ℕ → Prop} (hq : EvPer q) (h : Ev (fun t => p t ↔ q t)) :
    EvPer p := by
  obtain ⟨t₀, P, hP, hq⟩ := hq
  obtain ⟨T, hT⟩ := h
  refine ⟨max t₀ T, P, hP, fun t ht => ?_⟩
  have h1 := le_of_max_le_left ht
  have h2 := le_of_max_le_right ht
  rw [show p t ↔ q t from hT t h2, show p (t + P) ↔ q (t + P) from hT (t + P) (by omega),
    hq t h1]

theorem EvPer.and {p q : ℕ → Prop} (hp : EvPer p) (hq : EvPer q) :
    EvPer (fun t => p t ∧ q t) := by
  obtain ⟨t₁, P₁, h1, hp⟩ := hp
  obtain ⟨t₂, P₂, h2, hq⟩ := hq
  refine ⟨max t₁ t₂, P₂ * P₁, Nat.mul_pos h2 h1, fun t ht => ?_⟩
  exact and_congr (EvPer.iter hp P₂ t (le_of_max_le_left ht))
    (by rw [mul_comm]; exact EvPer.iter hq P₁ t (le_of_max_le_right ht))

theorem EvPer.or {p q : ℕ → Prop} (hp : EvPer p) (hq : EvPer q) :
    EvPer (fun t => p t ∨ q t) := by
  obtain ⟨t₁, P₁, h1, hp⟩ := hp
  obtain ⟨t₂, P₂, h2, hq⟩ := hq
  refine ⟨max t₁ t₂, P₂ * P₁, Nat.mul_pos h2 h1, fun t ht => ?_⟩
  exact or_congr (EvPer.iter hp P₂ t (le_of_max_le_left ht))
    (by rw [mul_comm]; exact EvPer.iter hq P₁ t (le_of_max_le_right ht))

theorem EvPer.not {p : ℕ → Prop} (hp : EvPer p) : EvPer (fun t => ¬ p t) := by
  obtain ⟨t₀, P, h0, hp⟩ := hp
  exact ⟨t₀, P, h0, fun t ht => not_congr (hp t ht)⟩

/-! ## Affine functions `ℕ → ℤ` -/

/-- `f t = α t + β` for some integers `α, β`. -/
def IsAff (f : ℕ → ℤ) : Prop := ∃ α β : ℤ, ∀ t : ℕ, f t = α * t + β

theorem IsAff.lin (a b : ℤ) : IsAff (fun t : ℕ => a * (t : ℤ) + b) := ⟨a, b, fun _ => rfl⟩

theorem IsAff.const (c : ℤ) : IsAff (fun _ => c) := ⟨0, c, fun t => by ring⟩

theorem IsAff.add {f g : ℕ → ℤ} (hf : IsAff f) (hg : IsAff g) :
    IsAff (fun t => f t + g t) := by
  obtain ⟨α, β, hf⟩ := hf
  obtain ⟨γ, δ, hg⟩ := hg
  exact ⟨α + γ, β + δ, fun t => by simp only [hf, hg]; ring⟩

theorem IsAff.sub {f g : ℕ → ℤ} (hf : IsAff f) (hg : IsAff g) :
    IsAff (fun t => f t - g t) := by
  obtain ⟨α, β, hf⟩ := hf
  obtain ⟨γ, δ, hg⟩ := hg
  exact ⟨α - γ, β - δ, fun t => by simp only [hf, hg]; ring⟩

theorem IsAff.smul {f : ℕ → ℤ} (c : ℤ) (hf : IsAff f) : IsAff (fun t => c * f t) := by
  obtain ⟨α, β, hf⟩ := hf
  exact ⟨c * α, c * β, fun t => by simp only [hf]; ring⟩

theorem ev_pos_of_slope_pos {α : ℤ} (β : ℤ) (hα : 0 < α) :
    Ev (fun t : ℕ => 0 < α * t + β) := by
  refine ⟨β.natAbs + 1, fun t ht => ?_⟩
  have h1 : ((β.natAbs : ℕ) : ℤ) + 1 ≤ (t : ℤ) := by exact_mod_cast ht
  have h2 : (t : ℤ) ≤ α * t := by nlinarith [Int.natCast_nonneg t]
  have h3 : -β ≤ (β.natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact neg_le_abs β
  linarith

/-- A nonconstant affine function eventually exceeds any bound in absolute value. -/
theorem ev_large {α : ℤ} (hα : α ≠ 0) (β C : ℤ) : Ev (fun t : ℕ => C < |α * t + β|) := by
  refine ⟨(C + |β|).toNat + 1, fun t ht => ?_⟩
  have h1 : C + |β| + 1 ≤ (t : ℤ) := by
    have := Int.self_le_toNat (C + |β|)
    have h' : (((C + |β|).toNat + 1 : ℕ) : ℤ) ≤ t := by exact_mod_cast ht
    push_cast at h'
    linarith
  have h2 : (t : ℤ) ≤ |α * t| := by
    rw [abs_mul, Nat.abs_cast]
    have := Int.one_le_abs hα
    nlinarith [Int.natCast_nonneg t]
  have h3 := abs_sub_abs_le_abs_sub (α * t) (-β)
  rw [abs_neg, sub_neg_eq_add] at h3
  linarith

/-- The sign of an affine function is eventually constant. -/
theorem ev_sign {f : ℕ → ℤ} (hf : IsAff f) :
    Ev (fun t => 0 < f t) ∨ Ev (fun t => f t = 0) ∨ Ev (fun t => f t < 0) := by
  obtain ⟨α, β, hf⟩ := hf
  rcases lt_trichotomy α 0 with h | h | h
  · right; right
    obtain ⟨T, hT⟩ := ev_pos_of_slope_pos (-β) (neg_pos.2 h)
    exact ⟨T, fun t ht => by have := hT t ht; simp only [hf] at this ⊢; linarith⟩
  · subst h
    rcases lt_trichotomy β 0 with h' | h' | h'
    · right; right; exact ⟨0, fun t _ => by simp only [hf, zero_mul, zero_add]; exact h'⟩
    · right; left; exact ⟨0, fun t _ => by simp only [hf, zero_mul, zero_add]; exact h'⟩
    · left; exact ⟨0, fun t _ => by simp only [hf, zero_mul, zero_add]; exact h'⟩
  · left
    obtain ⟨T, hT⟩ := ev_pos_of_slope_pos β h
    exact ⟨T, fun t ht => by simp only [hf]; exact hT t ht⟩

/-! ## Atoms -/

theorem evPer_pos {f : ℕ → ℤ} (hf : IsAff f) : EvPer (fun t => 0 < f t) := by
  rcases ev_sign hf with h | h | h
  · exact EvPer.of_ev h
  · exact EvPer.of_ev_not (h.mono fun t ht => by rw [ht]; exact lt_irrefl 0)
  · exact EvPer.of_ev_not (h.mono fun t ht => not_lt.2 ht.le)

theorem evPer_zero {f : ℕ → ℤ} (hf : IsAff f) : EvPer (fun t => f t = 0) := by
  rcases ev_sign hf with h | h | h
  · exact EvPer.of_ev_not (h.mono fun t ht => ht.ne')
  · exact EvPer.of_ev h
  · exact EvPer.of_ev_not (h.mono fun t ht => ht.ne)

theorem evPer_lt {f g : ℕ → ℤ} (hf : IsAff f) (hg : IsAff g) :
    EvPer (fun t => f t < g t) :=
  (evPer_pos (hg.sub hf)).congr (Ev.of_forall fun _ => sub_pos.symm)

theorem evPer_le {f g : ℕ → ℤ} (hf : IsAff f) (hg : IsAff g) :
    EvPer (fun t => f t ≤ g t) :=
  (evPer_lt hf (hg.add (IsAff.const 1))).congr
    (Ev.of_forall fun _ => Int.lt_add_one_iff.symm)

theorem evPer_eq {f g : ℕ → ℤ} (hf : IsAff f) (hg : IsAff g) :
    EvPer (fun t => f t = g t) :=
  (evPer_zero (hf.sub hg)).congr (Ev.of_forall fun _ => sub_eq_zero.symm)

/-- Affine divisibility `A(t) ∣ B(t)` is eventually periodic. -/
theorem evPer_dvd {A B : ℕ → ℤ} (hA : IsAff A) (hB : IsAff B) :
    EvPer (fun t => A t ∣ B t) := by
  obtain ⟨α, β, hA'⟩ := id hA
  obtain ⟨γ, δ, hB'⟩ := id hB
  by_cases hα : α = 0
  · subst hα
    by_cases hβ : β = 0
    · subst hβ
      refine (evPer_eq hB (IsAff.const 0)).congr (Ev.of_forall fun t => ?_)
      rw [hA', zero_mul, add_zero, zero_dvd_iff]
    · -- constant modulus `β`: period `|β|`
      refine ⟨0, β.natAbs, Int.natAbs_pos.2 hβ, fun t _ => ?_⟩
      show A t ∣ B t ↔ A (t + β.natAbs) ∣ B (t + β.natAbs)
      simp only [hA', hB', zero_mul, zero_add]
      push_cast
      have e : γ * ((t : ℤ) + |β|) + δ = (γ * t + δ) + γ * |β| := by ring
      rw [e]
      have hβd : β ∣ |β| := by rw [← Int.natCast_natAbs]; exact Int.dvd_natAbs.2 dvd_rfl
      exact (dvd_add_left (Dvd.dvd.mul_left hβd γ)).symm
  · set D := α * δ - γ * β with hDdef
    have hD : ∀ t, α * B t - γ * A t = D := fun t => by rw [hA', hB']; ring
    by_cases hD0 : D = 0
    · -- `α B = γ A`: eventually `A ∣ B ↔ α ∣ γ`
      refine (EvPer.const (α ∣ γ)).congr ((ev_large hα β 0).mono fun t ht => ?_)
      have hAt : A t ≠ 0 := by
        rw [hA']; intro h; rw [h, abs_zero] at ht; exact lt_irrefl 0 ht
      have hrel : α * B t = γ * A t := by have := hD t; rw [hD0] at this; linarith
      constructor
      · rintro ⟨s, hs⟩
        refine ⟨s, ?_⟩
        rw [hs] at hrel
        have : A t * (α * s) = A t * γ := by linear_combination hrel
        exact (mul_left_cancel₀ hAt this).symm
      · rintro ⟨q, hq⟩
        refine ⟨q, ?_⟩
        rw [hq] at hrel
        have : α * B t = α * (A t * q) := by rw [hrel]; ring
        exact mul_left_cancel₀ hα this
    · -- `A ∣ B` forces `A ∣ D ≠ 0`, impossible once `|A| > |D|`
      refine EvPer.of_ev_not ((ev_large hα β |D|).mono fun t ht hdvd => ?_)
      have h1 : A t ∣ D := by
        rw [← hD t]
        exact dvd_sub (dvd_mul_of_dvd_right hdvd α) (dvd_mul_left (A t) γ)
      have h2 := Int.le_of_dvd (abs_pos.2 hD0) ((abs_dvd_abs _ _).2 h1)
      rw [hA'] at h2
      linarith

theorem gcd_dvd_shift (X Y α γ D N : ℤ) (h : α * Y - γ * X = D) (hN : D ∣ N) :
    Int.gcd X Y ∣ Int.gcd (X + α * N) (Y + γ * N) := by
  have hX := Int.gcd_dvd_left X Y
  have hY := Int.gcd_dvd_right X Y
  have hD' : ((Int.gcd X Y : ℕ) : ℤ) ∣ N := by
    refine Dvd.dvd.trans ?_ hN
    rw [← h]
    exact dvd_sub (hY.mul_left α) (hX.mul_left γ)
  exact Int.dvd_gcd (dvd_add hX (hD'.mul_left α)) (dvd_add hY (hD'.mul_left γ))

theorem not_coprime_aux {X Y α γ : ℤ} (hα : α ≠ 0) (hrel : α * Y = γ * X)
    (hX : |α| < |X|) : Int.gcd X Y ≠ 1 := by
  intro h
  have hc : IsCoprime X Y := Int.isCoprime_iff_gcd_eq_one.2 h
  have h1 : X ∣ Y * α := ⟨γ, by linear_combination hrel⟩
  have h2 := hc.dvd_of_dvd_mul_left h1
  have h3 := Int.le_of_dvd (abs_pos.2 hα) ((abs_dvd_abs _ _).2 h2)
  linarith

/-- Affine coprimality `gcd(A(t), B(t)) = 1` is eventually periodic. -/
theorem evPer_gcd {A B : ℕ → ℤ} (hA : IsAff A) (hB : IsAff B) :
    EvPer (fun t => Int.gcd (A t) (B t) = 1) := by
  obtain ⟨α, β, hA'⟩ := id hA
  obtain ⟨γ, δ, hB'⟩ := id hB
  set D := α * δ - γ * β with hDdef
  have hD : ∀ t, α * B t - γ * A t = D := fun t => by rw [hA', hB']; ring
  by_cases hD0 : D = 0
  · have hrel : ∀ t, α * B t = γ * A t := fun t => by
      have := hD t; rw [hD0] at this; linarith
    by_cases hα : α = 0
    · by_cases hγ : γ = 0
      · -- both constant
        refine ⟨0, 1, one_pos, fun t _ => ?_⟩
        show Int.gcd (A t) (B t) = 1 ↔ Int.gcd (A (t + 1)) (B (t + 1)) = 1
        simp only [hA', hB', hα, hγ, zero_mul, zero_add]
      · refine EvPer.of_ev_not ((ev_large hγ δ |γ|).mono fun t ht hg => ?_)
        rw [← hB'] at ht
        exact not_coprime_aux hγ (hrel t).symm ht (by rw [Int.gcd_comm]; exact hg)
    · refine EvPer.of_ev_not ((ev_large hα β |α|).mono fun t ht hg => ?_)
      rw [← hA'] at ht
      exact not_coprime_aux hα (hrel t) ht hg
  · -- the gcd divides `D ≠ 0`, so it is periodic with period `|D|`
    refine ⟨0, D.natAbs, Int.natAbs_pos.2 hD0, fun t _ => ?_⟩
    show Int.gcd (A t) (B t) = 1 ↔ Int.gcd (A (t + D.natAbs)) (B (t + D.natAbs)) = 1
    have e1 : A (t + D.natAbs) = A t + α * (D.natAbs : ℤ) := by
      rw [hA', hA']; push_cast; ring
    have e2 : B (t + D.natAbs) = B t + γ * (D.natAbs : ℤ) := by
      rw [hB', hB']; push_cast; ring
    rw [e1, e2]
    have h1 := gcd_dvd_shift (A t) (B t) α γ D (D.natAbs) (hD t) (Int.dvd_natAbs.2 dvd_rfl)
    have h2 := gcd_dvd_shift (A t + α * (D.natAbs : ℤ)) (B t + γ * (D.natAbs : ℤ)) α γ D
      (-(D.natAbs : ℤ)) (by rw [← hD t]; ring) (dvd_neg.2 (Int.dvd_natAbs.2 dvd_rfl))
    rw [show A t + α * (D.natAbs : ℤ) + α * -(D.natAbs : ℤ) = A t by ring,
      show B t + γ * (D.natAbs : ℤ) + γ * -(D.natAbs : ℤ) = B t by ring] at h2
    rw [Nat.dvd_antisymm h1 h2]

/-! ## `criterion` as a boolean combination of atoms -/

/-- The part of `criterion` after `gcd = 1`, as a function of `k` and `m = min(l, k - l)`. -/
def crit2 (k m : ℕ) : Prop :=
  m = 1 ∨ (2 ≤ m ∧ 3 ≤ k / m ∧ (k % m = 1 ∨ k % m = m - 1)) ∨
    (2 ≤ m ∧ k / m = 2 ∧
      (k - 2 * m = 1 ∨ m % (k - 2 * m) = 1 ∨ m % (k - 2 * m) = k - 2 * m - 1))

theorem criterion_iff (k l : ℕ) :
    criterion k l ↔ Nat.gcd k l = 1 ∧ crit2 k (min l (k - l)) := Iff.rfl

/-- Integer form of `crit2`: affine inequalities and affine divisibilities in `K, M`. -/
def critZ (K M : ℤ) : Prop :=
  M = 1 ∨ (2 ≤ M ∧ 3 * M ≤ K ∧ (M ∣ K - 1 ∨ M ∣ K + 1)) ∨
    (2 ≤ M ∧ 2 * M ≤ K ∧ K < 3 * M ∧
      (K - 2 * M = 1 ∨ (1 < K - 2 * M ∧ K - 2 * M ∣ M - 1) ∨
        (0 < K - 2 * M ∧ K - 2 * M ∣ M + 1)))

theorem natmod_eq_iff (k m : ℕ) (c : ℤ) (hc0 : 0 ≤ c) (hcm : c < m) :
    ((k % m : ℕ) : ℤ) = c ↔ (m : ℤ) ∣ (k : ℤ) - c := by
  have hm : 0 < m := by omega
  have hk : (k : ℤ) = m * (k / m : ℕ) + (k % m : ℕ) := by
    exact_mod_cast (Nat.div_add_mod k m).symm
  have hlt : ((k % m : ℕ) : ℤ) < m := by exact_mod_cast Nat.mod_lt k hm
  have hnn := Int.natCast_nonneg (k % m)
  constructor
  · intro h
    exact ⟨(k / m : ℕ), by rw [hk, h]; ring⟩
  · intro h
    have h2 : (m : ℤ) ∣ ((k % m : ℕ) : ℤ) - c := by
      have e : ((k % m : ℕ) : ℤ) - c = ((k : ℤ) - c) - m * (k / m : ℕ) := by linarith
      rw [e]
      exact dvd_sub h (dvd_mul_right _ _)
    have := Int.eq_zero_of_abs_lt_dvd h2 (by rw [abs_lt]; constructor <;> linarith)
    linarith

theorem and_congr' {a b c d : Prop} (h1 : a ↔ c) (h2 : a → (b ↔ d)) : a ∧ b ↔ c ∧ d :=
  ⟨fun ⟨x, y⟩ => ⟨h1.1 x, (h2 x).1 y⟩, fun ⟨x, y⟩ => ⟨h1.2 x, (h2 (h1.2 x)).2 y⟩⟩

theorem mod_eq_one_iff (k m : ℕ) (hm : 2 ≤ m) : k % m = 1 ↔ (m : ℤ) ∣ (k : ℤ) - 1 := by
  rw [← natmod_eq_iff k m 1 (by norm_num) (by omega)]
  generalize k % m = ρ
  omega

theorem mod_eq_pred_iff (k m : ℕ) (hm : 1 ≤ m) : k % m = m - 1 ↔ (m : ℤ) ∣ (k : ℤ) + 1 := by
  have h := natmod_eq_iff k m ((m : ℤ) - 1) (by omega) (by omega)
  rw [show (k : ℤ) - ((m : ℤ) - 1) = ((k : ℤ) + 1) - m by ring, dvd_sub_self_right] at h
  rw [← h]
  generalize k % m = ρ
  omega

theorem mod_eq_one_iff' (m r : ℕ) (hm : 2 ≤ m) :
    m % r = 1 ↔ 1 < (r : ℤ) ∧ (r : ℤ) ∣ (m : ℤ) - 1 := by
  rcases Nat.lt_or_ge r 2 with hr | hr
  · constructor
    · intro h1
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · rw [Nat.mod_zero] at h1; omega
      · rw [Nat.mod_one] at h1; omega
    · rintro ⟨h1, -⟩; omega
  · rw [← natmod_eq_iff m r 1 (by norm_num) (by omega)]
    generalize m % r = ρ
    omega

theorem mod_eq_pred_iff' (m r : ℕ) (hm : 2 ≤ m) :
    m % r = r - 1 ↔ 0 < (r : ℤ) ∧ (r : ℤ) ∣ (m : ℤ) + 1 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · constructor
    · intro h1; rw [Nat.mod_zero] at h1; omega
    · rintro ⟨h1, -⟩; omega
  · have h := natmod_eq_iff m r ((r : ℤ) - 1) (by omega) (by omega)
    rw [show (m : ℤ) - ((r : ℤ) - 1) = ((m : ℤ) + 1) - r by ring, dvd_sub_self_right] at h
    rw [← h]
    generalize m % r = ρ
    omega

theorem crit2_iff (k m : ℕ) (hm : 0 < m) : crit2 k m ↔ critZ k m := by
  unfold crit2 critZ
  have L3 : 3 ≤ k / m ↔ 3 * (m : ℤ) ≤ k := by rw [Nat.le_div_iff_mul_le hm]; omega
  have L4 : k / m = 2 ↔ 2 * (m : ℤ) ≤ k ∧ (k : ℤ) < 3 * m := by
    have a : 2 ≤ k / m ↔ 2 * m ≤ k := Nat.le_div_iff_mul_le hm
    have b : k / m < 3 ↔ k < 3 * m := Nat.div_lt_iff_lt_mul hm
    generalize k / m = q at a b ⊢
    omega
  refine or_congr (by omega) (or_congr
    (and_congr' (by omega) fun h2 =>
      and_congr L3 (or_congr (mod_eq_one_iff k m h2) (mod_eq_pred_iff k m (by omega))))
    (and_congr' (by omega) fun h2 => ?_))
  rw [← and_assoc]
  refine and_congr' L4 fun h3 => ?_
  have hR : ((k - 2 * m : ℕ) : ℤ) = (k : ℤ) - 2 * m := by have := (L4.1 h3).1; omega
  rw [← hR]
  exact or_congr (by omega) (or_congr (mod_eq_one_iff' m _ h2) (mod_eq_pred_iff' m _ h2))

theorem evPer_critZ {K M : ℕ → ℤ} (hK : IsAff K) (hM : IsAff M) :
    EvPer (fun t => critZ (K t) (M t)) := by
  have hR : IsAff (fun t => K t - 2 * M t) := hK.sub (hM.smul 2)
  unfold critZ
  refine EvPer.or (evPer_eq hM (IsAff.const 1)) (EvPer.or ?_ ?_)
  · refine EvPer.and (evPer_le (IsAff.const 2) hM) (EvPer.and (evPer_le (hM.smul 3) hK) ?_)
    exact EvPer.or (evPer_dvd hM (hK.sub (IsAff.const 1))) (evPer_dvd hM (hK.add (IsAff.const 1)))
  · refine EvPer.and (evPer_le (IsAff.const 2) hM) (EvPer.and (evPer_le (hM.smul 2) hK)
      (EvPer.and (evPer_lt hK (hM.smul 3)) ?_))
    refine EvPer.or (evPer_eq hR (IsAff.const 1)) (EvPer.or ?_ ?_)
    · exact EvPer.and (evPer_lt (IsAff.const 1) hR) (evPer_dvd hR (hM.sub (IsAff.const 1)))
    · exact EvPer.and (evPer_lt (IsAff.const 0) hR) (evPer_dvd hR (hM.add (IsAff.const 1)))

/-- Generic form: if eventually `0 < L < K` and `M = min(L, K - L)`, with `K, L, M` affine,
then `criterion K L` is eventually periodic. -/
theorem evPer_criterion_aff {K L M : ℕ → ℤ} (hK : IsAff K) (hL : IsAff L) (hM : IsAff M)
    (h : Ev (fun t => 0 < L t ∧ L t < K t ∧
      ((M t = L t ∧ L t ≤ K t - L t) ∨ (M t = K t - L t ∧ K t - L t ≤ L t)))) :
    EvPer (fun t => criterion (K t).toNat (L t).toNat) := by
  refine (EvPer.and (evPer_gcd hK hL) (evPer_critZ hK hM)).congr (h.mono fun t ht => ?_)
  obtain ⟨h1, h2, h3⟩ := ht
  have ek : ((K t).toNat : ℤ) = K t := Int.toNat_of_nonneg (by linarith)
  have el : ((L t).toNat : ℤ) = L t := Int.toNat_of_nonneg h1.le
  have hMpos : 0 < M t := by rcases h3 with ⟨a, b⟩ | ⟨a, b⟩ <;> linarith
  have em : ((M t).toNat : ℤ) = M t := Int.toNat_of_nonneg hMpos.le
  show criterion (K t).toNat (L t).toNat ↔ Int.gcd (K t) (L t) = 1 ∧ critZ (K t) (M t)
  generalize (K t).toNat = k at ek ⊢
  generalize (L t).toNat = l at el ⊢
  rw [← ek, ← el, ← em]
  generalize (M t).toNat = m at em ⊢
  have hmin : min l (k - l) = m := by rcases h3 with ⟨a, b⟩ | ⟨a, b⟩ <;> omega
  rw [criterion_iff, hmin, Int.gcd_natCast_natCast, crit2_iff k m (by omega)]

/-! ## Corollary 4 -/

/-- **Corollary 4, arithmetic form.** For an integer affine ray `k(t) = a t + b`,
`l(t) = c t + d` with `0 < l(t) < k(t)` for all large `t`, the predicate
`criterion (k t) (l t)` is eventually periodic in `t ∈ ℕ`. -/
theorem criterion_ray (a b c d : ℤ)
    (h : Ev (fun t : ℕ => 0 < c * t + d ∧ c * t + d < a * t + b)) :
    EvPer (fun t : ℕ => criterion (a * t + b).toNat (c * t + d).toNat) := by
  have hK := IsAff.lin a b
  have hL := IsAff.lin c d
  rcases ev_sign ((hL.smul 2).sub hK) with hs | hs | hs
  · exact evPer_criterion_aff hK hL (hK.sub hL) ((h.and hs).mono
      fun t ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, Or.inr ⟨rfl, by linarith⟩⟩)
  · exact evPer_criterion_aff hK hL (hK.sub hL) ((h.and hs).mono
      fun t ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, Or.inr ⟨rfl, by linarith⟩⟩)
  · exact evPer_criterion_aff hK hL hL ((h.and hs).mono
      fun t ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, Or.inl ⟨rfl, by linarith⟩⟩)

/-- Corollary 4, arithmetic form, unfolded. -/
theorem criterion_ray' (a b c d : ℤ)
    (h : ∃ T : ℕ, ∀ t : ℕ, T ≤ t → 0 < c * t + d ∧ c * t + d < a * t + b) :
    ∃ t₀ P : ℕ, 0 < P ∧ ∀ t : ℕ, t₀ ≤ t →
      (criterion (a * t + b).toNat (c * t + d).toNat ↔
        criterion (a * (t + P : ℕ) + b).toNat (c * (t + P : ℕ) + d).toNat) :=
  criterion_ray a b c d h

/-- **Corollary 4, graph form at primitive points.** For an integer affine ray with
`0 < l(t) < k(t)` for large `t`, the predicate "`gcd(k(t), l(t)) = 1` and `gcGraph k(t) l(t)` has
a literal gSW path" is eventually periodic. Uses only the primitive classification. -/
theorem path_ray_primitive (a b c d : ℤ)
    (h : Ev (fun t : ℕ => 0 < c * t + d ∧ c * t + d < a * t + b)) :
    EvPer (fun t : ℕ => Int.gcd (a * t + b) (c * t + d) = 1 ∧
      ∃ n p, LiteralPath (gcGraph (a * t + b) (c * t + d)) n p) := by
  refine (criterion_ray a b c d h).congr (h.mono fun t ht => ?_)
  obtain ⟨h1, h2⟩ := ht
  have ek : ((a * t + b).toNat : ℤ) = a * t + b := Int.toNat_of_nonneg (by linarith)
  have el : ((c * t + d).toNat : ℤ) = c * t + d := Int.toNat_of_nonneg h1.le
  generalize (a * (t : ℤ) + b).toNat = k at ek ⊢
  generalize (c * (t : ℤ) + d).toNat = l at el ⊢
  rw [← ek, ← el, Int.gcd_natCast_natCast]
  have hl : 0 < l := by omega
  have hlk : l < k := by omega
  constructor
  · rintro ⟨hg, hp⟩
    exact (ClaudeMain.main_primitive k l hl hlk hg).1 hp
  · intro hc
    exact ⟨hc.1, (ClaudeMain.main_primitive k l hl hlk hc.1).2 hc⟩

/-- **Corollary 4, graph form on eventually primitive rays.** If moreover
`gcd(k(t), l(t)) = 1` for all large `t`, the existence of a literal gSW path in
`gcGraph k(t) l(t)` is eventually periodic. -/
theorem path_ray_of_primitive (a b c d : ℤ)
    (h : Ev (fun t : ℕ => 0 < c * t + d ∧ c * t + d < a * t + b))
    (hp : Ev (fun t : ℕ => Int.gcd (a * t + b) (c * t + d) = 1)) :
    EvPer (fun t : ℕ => ∃ n p, LiteralPath (gcGraph (a * t + b) (c * t + d)) n p) :=
  (path_ray_primitive a b c d h).congr (hp.mono fun _ hg => (and_iff_right hg).symm)

end ClaudeCor

#print axioms ClaudeCor.criterion_ray
#print axioms ClaudeCor.criterion_ray'
#print axioms ClaudeCor.path_ray_primitive
#print axioms ClaudeCor.path_ray_of_primitive
