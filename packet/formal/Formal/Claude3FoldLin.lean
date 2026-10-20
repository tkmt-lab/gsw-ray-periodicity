import Formal.Claude3FoldDef
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith

/-!
# Restricted linear atoms on folded positions

For position variables `x, y` (values `v, w < n`), signs `σ₁, σ₂ ∈ {-1, 0, 1}` and integers
`C, D`, the predicate `σ₁ v + σ₂ w ≤ C n + D` is eventually MSO-definable on unary words of
length `n`, **provided `C` is even whenever both signs are nonzero** (`EvDef.lin2`).
(Without that parity condition this fails: `v + w ≤ n` is not MSO-definable.)

Also: residues `A n + B + s v ≡ r [ZMOD q]` (`EvDef.modEq`) and `2n + η ≡ r [MOD q]`
(`EvDef.tmodEq`) are MSO-definable for every fixed `q`.
-/

namespace R002.Claude3Mso

open MSO

/-- `s ∈ {-1, 0, 1}` -/
def IsSgn (s : ℤ) : Prop := s = -1 ∨ s = 0 ∨ s = 1

namespace EvDef

variable {m k : ℕ}

theorem mul_le_of_le {C c : ℤ} (n : ℕ) (h : c ≤ C) : c * (n : ℤ) ≤ C * n :=
  mul_le_mul_of_nonneg_right h (Nat.cast_nonneg n)

/-- `0 ≤ C n + D` is eventually constant. -/
theorem affine_nonneg (C D : ℤ) :
    EvDef (fun n (_ : Fin m → ℕ) (_ : Fin k → Set ℕ) => 0 ≤ C * (n : ℤ) + D) := by
  rcases lt_trichotomy C 0 with hC | rfl | hC
  · refine of_eventually_iff False (D.toNat + 1) fun n hn _ _ _ => ?_
    have := mul_le_of_le n (show C ≤ -1 by omega)
    simp only [iff_false, not_le]; omega
  · exact of_eventually_iff (0 ≤ D) 0 fun _ _ _ _ _ => by simp
  · refine of_eventually_iff True (-D).toNat fun n hn _ _ _ => ?_
    have := mul_le_of_le n (show 1 ≤ C by omega)
    simp only [iff_true]; omega

/-- `v ≤ C n + D` -/
theorem lin1_pos (C D : ℤ) (x : Fin m) :
    EvDef (k := k) (fun n ν _ => (ν x : ℤ) ≤ C * n + D) := by
  by_cases h1 : C ≤ -1
  · refine of_eventually_iff False (D.toNat + 1) fun n hn ν hν _ => ?_
    have := mul_le_of_le n h1
    simp only [iff_false, not_le]; omega
  by_cases h2 : C = 0
  · subst h2
    by_cases hD : D < 0
    · exact of_eventually_iff False 0 fun n _ ν _ _ => by simp only [iff_false]; omega
    · refine of_exact (posLe D.toNat x) fun n ν hν V => ?_
      rw [sat_posLe _ _ (by simpa using hν x)]
      omega
  by_cases h3 : C = 1
  · subst h3
    by_cases hD : -1 ≤ D
    · refine of_eventually_iff True 0 fun n _ ν hν _ => ?_
      have := hν x
      simp only [iff_true]; omega
    · refine (of_exact (posLeR ((-D) - 2).toNat x) fun n ν hν V =>
        sat_posLeR _ _ (by simpa using hν x)).neg.congr 0 fun n _ ν hν _ => ?_
      simp only [uw_length]
      omega
  · refine of_eventually_iff True (-D).toNat fun n hn ν hν _ => ?_
    have := mul_le_of_le n (show 2 ≤ C by omega)
    have := hν x
    simp only [iff_true]; omega

/-- `σ v ≤ C n + D` for a sign `σ` -/
theorem lin1 {σ : ℤ} (hσ : IsSgn σ) (C D : ℤ) (x : Fin m) :
    EvDef (k := k) (fun n ν _ => σ * (ν x : ℤ) ≤ C * n + D) := by
  rcases hσ with rfl | rfl | rfl
  · refine (lin1_pos (-C) (-D - 1) x).neg.congr 0 fun n _ ν _ _ => ?_
    rw [neg_mul]; omega
  · exact (affine_nonneg C D).congr 0 fun n _ ν _ _ => by simp
  · exact (lin1_pos C D x).congr 0 fun n _ ν _ _ => by simp

/-- `v - w ≤ C n + D` for even `C` -/
theorem lin2_pm {C : ℤ} (hC : Even C) (D : ℤ) (x y : Fin m) :
    EvDef (k := k) (fun n ν _ => (ν x : ℤ) - ν y ≤ C * n + D) := by
  have hC2 := Int.even_iff.1 hC
  by_cases h1 : C ≤ -2
  · refine of_eventually_iff False (D.toNat + 1) fun n hn ν hν _ => ?_
    have := mul_le_of_le n h1
    have := hν x; have := hν y
    simp only [iff_false, not_le]; omega
  by_cases h2 : C = 0
  · subst h2
    by_cases hD : 0 ≤ D
    · refine of_exact (leAdd D.toNat x y) fun n ν hν V => ?_
      rw [sat_leAdd _ _ _ _ (by simpa using hν x)]
      omega
    · refine (of_exact (leAdd ((-D) - 1).toNat y x) fun n ν hν V =>
        sat_leAdd _ _ _ _ (by simpa using hν y)).neg.congr 0 fun n _ ν hν _ => ?_
      omega
  · refine of_eventually_iff True (-D).toNat fun n hn ν hν _ => ?_
    have := mul_le_of_le n (show 2 ≤ C by omega)
    have := hν x; have := hν y
    simp only [iff_true]; omega

/-- `v + w ≤ C n + D` for even `C` -/
theorem lin2_pp {C : ℤ} (hC : Even C) (D : ℤ) (x y : Fin m) :
    EvDef (k := k) (fun n ν _ => (ν x : ℤ) + ν y ≤ C * n + D) := by
  have hC2 := Int.even_iff.1 hC
  by_cases h1 : C ≤ -2
  · refine of_eventually_iff False (D.toNat + 1) fun n hn ν hν _ => ?_
    have := mul_le_of_le n h1
    simp only [iff_false, not_le]; omega
  by_cases h2 : C = 0
  · subst h2
    by_cases hD : D < 0
    · exact of_eventually_iff False 0 fun n _ ν _ _ => by simp only [iff_false]; omega
    · refine of_exact (sumLe D.toNat x y) fun n ν hν V => ?_
      rw [sat_sumLe _ _ _ _ (by simpa using hν x) (by simpa using hν y)]
      omega
  by_cases h3 : C = 2
  · subst h3
    by_cases hD : -2 ≤ D
    · refine of_eventually_iff True 0 fun n _ ν hν _ => ?_
      have := hν x; have := hν y
      simp only [iff_true]; omega
    · refine (of_exact (sumLeR ((-D) - 3).toNat x y) fun n ν hν V =>
        sat_sumLeR _ _ _ _ (by simpa using hν x) (by simpa using hν y)).neg.congr 0
        fun n _ ν hν _ => ?_
      simp only [uw_length]
      omega
  · refine of_eventually_iff True (-D).toNat fun n hn ν hν _ => ?_
    have := mul_le_of_le n (show 4 ≤ C by omega)
    have := hν x; have := hν y
    simp only [iff_true]; omega

/-- **Restricted two-variable atoms.** `σ₁ v + σ₂ w ≤ C n + D` is eventually MSO-definable
when `σ₁, σ₂` are signs and `C` is even whenever both signs are nonzero. -/
theorem lin2 {σ₁ σ₂ : ℤ} (h₁ : IsSgn σ₁) (h₂ : IsSgn σ₂) (C D : ℤ)
    (hC : σ₁ ≠ 0 → σ₂ ≠ 0 → Even C) (x y : Fin m) :
    EvDef (k := k) (fun n ν _ => σ₁ * (ν x : ℤ) + σ₂ * ν y ≤ C * n + D) := by
  rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl
  · refine (lin2_pp (hC (by norm_num) (by norm_num)).neg (-D - 1) x y).neg.congr 0
      fun n _ ν _ _ => ?_
    rw [neg_mul]; omega
  · exact (lin1 (Or.inl rfl) C D x).congr 0 fun n _ ν _ _ => by simp
  · exact (lin2_pm (hC (by norm_num) (by norm_num)) D y x).congr 0 fun n _ ν _ _ => by
      simp only [neg_mul, one_mul]; omega
  · exact (lin1 (Or.inl rfl) C D y).congr 0 fun n _ ν _ _ => by simp
  · exact (affine_nonneg C D).congr 0 fun n _ ν _ _ => by simp
  · exact (lin1 (Or.inr (Or.inr rfl)) C D y).congr 0 fun n _ ν _ _ => by simp
  · exact (lin2_pm (hC (by norm_num) (by norm_num)) D x y).congr 0 fun n _ ν _ _ => by
      simp only [neg_mul, one_mul]; omega
  · exact (lin1 (Or.inr (Or.inr rfl)) C D x).congr 0 fun n _ ν _ _ => by simp
  · exact (lin2_pp (hC (by norm_num) (by norm_num)) D x y).congr 0 fun n _ ν _ _ => by simp

/-! ### Congruences -/

theorem natCast_mod_modEq (n q : ℕ) : ((n % q : ℕ) : ℤ) ≡ n [ZMOD q] := by
  rw [Int.natCast_mod]; exact Int.mod_modEq _ _

/-- `A n + B + s v ≡ r [ZMOD q]` (`q > 0`) -/
theorem modEq_pos {q : ℕ} (hq : 0 < q) (A B s r : ℤ) (x : Fin m) :
    EvDef (k := k) (fun n ν _ => A * n + B + s * (ν x : ℤ) ≡ r [ZMOD q]) := by
  have key : EvDef (k := k) (fun n ν _ => ∃ ρ : Fin q × Fin q,
      (n % q = ρ.1 ∧ ν x % q = ρ.2) ∧ A * (ρ.1 : ℕ) + B + s * (ρ.2 : ℕ) ≡ r [ZMOD q]) := by
    refine exists_fintype fun ρ => ((of_exact (lenMod q ρ.1) fun n ν _ V => ?_).and
      (of_exact (posMod q ρ.2 x) fun n ν hν V => ?_)).and (const _)
    · rw [sat_lenMod hq ρ.1.2, uw_length]
    · rw [sat_posMod hq ρ.2.2 x (by simpa using hν x)]
  refine key.congr 0 fun n _ ν _ _ => ?_
  have e : A * ((n % q : ℕ) : ℤ) + B + s * ((ν x % q : ℕ) : ℤ) ≡ A * n + B + s * (ν x : ℤ)
      [ZMOD q] :=
    (((natCast_mod_modEq n q).mul_left A).add_right B).add ((natCast_mod_modEq _ q).mul_left s)
  constructor
  · rintro ⟨ρ, ⟨h1, h2⟩, h3⟩
    rw [← h1, ← h2] at h3
    exact e.symm.trans h3
  · intro h
    exact ⟨(⟨n % q, Nat.mod_lt _ hq⟩, ⟨ν x % q, Nat.mod_lt _ hq⟩), ⟨rfl, rfl⟩, e.trans h⟩

/-- `A n + B + s v ≡ r [ZMOD q]` for every `q` (for `q = 0` this is an equation). -/
theorem modEq (q : ℕ) (A B : ℤ) {s : ℤ} (hs : IsSgn s) (r : ℤ) (x : Fin m) :
    EvDef (k := k) (fun n ν _ => A * n + B + s * (ν x : ℤ) ≡ r [ZMOD q]) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine ((lin1 hs (-A) (r - B) x).and (lin1 (k := k) (show IsSgn (-s) by
      rcases hs with rfl | rfl | rfl <;> simp [IsSgn]) A (B - r) x)).congr 0
      fun n _ ν _ _ => ?_
    simp only [Int.ModEq, Nat.cast_zero, Int.emod_zero, neg_mul]
    constructor
    · rintro ⟨h1, h2⟩; linarith
    · intro h; constructor <;> linarith
  · exact modEq_pos hq A B s r x

/-- `2n + η ≡ r [MOD q]` -/
theorem tmodEq (q η r : ℕ) :
    EvDef (fun n (_ : Fin m → ℕ) (_ : Fin k → Set ℕ) => 2 * n + η ≡ r [MOD q]) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine of_eventually_iff False (r + 1) fun n hn _ _ _ => ?_
    simp only [Nat.ModEq, Nat.mod_zero, iff_false]; omega
  have key : EvDef (fun n (_ : Fin m → ℕ) (_ : Fin k → Set ℕ) => ∃ ρ : Fin q,
      n % q = ρ ∧ 2 * (ρ : ℕ) + η ≡ r [MOD q]) :=
    exists_fintype fun ρ => (of_exact (lenMod q ρ) fun n ν _ V => by
      rw [sat_lenMod hq ρ.2, uw_length]).and (const _)
  refine key.congr 0 fun n _ ν _ _ => ?_
  have e : 2 * (n % q) + η ≡ 2 * n + η [MOD q] :=
    ((Nat.mod_modEq n q).mul_left 2).add_right η
  constructor
  · rintro ⟨ρ, h1, h2⟩
    rw [← h1] at h2
    exact e.symm.trans h2
  · intro h
    exact ⟨⟨n % q, Nat.mod_lt _ hq⟩, rfl, e.trans h⟩

end EvDef

end R002.Claude3Mso
