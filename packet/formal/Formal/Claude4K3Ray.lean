import Formal.Claude2K3TwoCommon

/-!
# K3 on rays: the arithmetic reduction

Written by a Claude worker (2026-10-20, K3 bridge).

`ClaudeChallengeK3.main` (version 2, `r₀, s₀ ≥ 1`) asks that literal-path existence in K3 be
eventually periodic on every ray `(r₀ + a t, s₀ + b t)`.  Here it is reduced to

* the K3 classification `K3Statement` (`r, s ≥ 2`: a path exists iff `s ≡ ±1 (mod r)`), and
* the two boundary families: a path exists in `K3(1, s)` for all large `s`, and in `K3(r, 1)`
  for all large `r`.

On a ray with `a > 0` the quantity `a s - b r` is constant, so `r ∣ s ∓ 1` is eventually
constant (`ray_dvd_eventually`); with `a = 0` it has period `r₀`.

* `PE r s`               : a literal path exists in `K3(r, s)` (same as `ClaudeChallengeK3.PathExists`);
* `main_of_K3Statement`  : `K3Statement` and the two boundary facts give the ray statement;
* `main_of_noThree`      : the same from `NoThreeCommon` for all `r, s ≥ 2`.
-/

namespace Claude4K3

open ClaudeChallenge Claude2Aligned

/-- A literal path exists in K3(r,s). -/
def PE (r s : ℤ) : Prop := ∃ n p, LiteralPath (k3Graph r s) n p

/-- Eventual periodicity of a predicate on `ℕ`. -/
def EvPer (Q : ℕ → Prop) : Prop := ∃ t₀ P : ℕ, 0 < P ∧ ∀ t : ℕ, t₀ ≤ t → (Q t ↔ Q (t + P))

theorem evPer_of_iff {Q C : ℕ → Prop} (t₁ : ℕ) (hQ : ∀ t, t₁ ≤ t → (Q t ↔ C t))
    (hC : EvPer C) : EvPer Q := by
  obtain ⟨t₀, P, hP, h⟩ := hC
  refine ⟨max t₀ t₁, P, hP, fun t ht => ?_⟩
  rw [hQ t (le_of_max_le_right ht), hQ (t + P) (by omega)]
  exact h t (le_of_max_le_left ht)

theorem evPer_of_const {Q : ℕ → Prop} (B : Prop) (t₁ : ℕ) (h : ∀ t, t₁ ≤ t → (Q t ↔ B)) :
    EvPer Q :=
  ⟨t₁, 1, Nat.one_pos, fun t ht => by rw [h t ht, h (t + 1) (by omega)]⟩

theorem evPer_or {Q R : ℕ → Prop} (B C : Prop) (t₁ : ℕ) (hQ : ∀ t, t₁ ≤ t → (Q t ↔ B))
    (hR : ∀ t, t₁ ≤ t → (R t ↔ C)) : EvPer (fun t => Q t ∨ R t) :=
  evPer_of_const (B ∨ C) t₁ fun t ht => by rw [hQ t ht, hR t ht]

/-- On a ray with `a > 0`, divisibility `r ∣ s - e` is eventually constant. -/
theorem ray_dvd_eventually (r₀ s₀ a b e : ℤ) (ha : 0 < a) (hb : 0 ≤ b) (hr : 0 < r₀) :
    ∃ t₁ : ℕ, ∃ B : Prop, ∀ t : ℕ, t₁ ≤ t →
      ((r₀ + a * t ∣ s₀ + b * t - e) ↔ B) := by
  set c := a * (s₀ - e) - b * r₀ with hc
  have key : ∀ t : ℕ, a * (s₀ + b * t - e) - b * (r₀ + a * t) = c := fun t => by rw [hc]; ring
  by_cases h0 : c = 0
  · refine ⟨0, a ∣ b, fun t _ => ?_⟩
    have hrt : 0 < r₀ + a * t := by positivity
    have hk := key t
    rw [h0] at hk
    constructor
    · rintro ⟨k, hk'⟩
      refine ⟨k, ?_⟩
      have : a * ((r₀ + a * t) * k) = b * (r₀ + a * t) := by rw [← hk']; linarith
      have h2 : (r₀ + a * t) * (a * k - b) = 0 := by linarith
      rcases mul_eq_zero.1 h2 with h | h
      · omega
      · linarith
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      have h2 : a * ((s₀ + a * k * t - e) - (r₀ + a * t) * k) = 0 := by linarith
      rcases mul_eq_zero.1 h2 with h | h
      · omega
      · linarith
  · refine ⟨c.natAbs + 1, False, fun t ht => ?_⟩
    simp only [iff_false]
    intro hd
    have hd2 : r₀ + a * t ∣ c := by
      rw [← key t]
      exact dvd_sub (dvd_mul_of_dvd_right hd a) (dvd_mul_left _ _)
    have hle := Int.le_of_dvd (by have := Int.natAbs_pos.2 h0; omega) ((Int.dvd_natAbs).2 hd2)
    have : (c.natAbs : ℤ) + 1 ≤ t := by exact_mod_cast ht
    nlinarith

theorem modEq_iff_dvd' (x e n : ℤ) : x ≡ e [ZMOD n] ↔ n ∣ x - e :=
  ⟨fun h => Int.modEq_iff_dvd.1 h.symm, fun h => (Int.modEq_iff_dvd.2 h).symm⟩

/-- With `a > 0`, the K3 criterion is eventually constant on the ray. -/
theorem crit_evPer_pos (r₀ s₀ a b : ℕ) (ha : 0 < a) (hr : 0 < r₀) :
    EvPer (fun t => ((s₀ + b * t : ℕ) : ℤ) ≡ 1 [ZMOD ((r₀ + a * t : ℕ) : ℤ)] ∨
      ((s₀ + b * t : ℕ) : ℤ) ≡ -1 [ZMOD ((r₀ + a * t : ℕ) : ℤ)]) := by
  obtain ⟨t₁, B, hB⟩ := ray_dvd_eventually r₀ s₀ a b 1 (by exact_mod_cast ha) (by positivity)
    (by exact_mod_cast hr)
  obtain ⟨t₂, C, hC⟩ := ray_dvd_eventually r₀ s₀ a b (-1) (by exact_mod_cast ha) (by positivity)
    (by exact_mod_cast hr)
  refine evPer_or B C (max t₁ t₂) (fun t ht => ?_) (fun t ht => ?_)
  · rw [modEq_iff_dvd', ← hB t (le_of_max_le_left ht)]; push_cast; rfl
  · rw [modEq_iff_dvd', ← hC t (le_of_max_le_right ht)]; push_cast; rfl

/-- With `a = 0`, the K3 criterion has period `r₀`. -/
theorem crit_evPer_zero (r₀ s₀ b : ℕ) (hr : 0 < r₀) :
    EvPer (fun t => ((s₀ + b * t : ℕ) : ℤ) ≡ 1 [ZMOD ((r₀ + 0 * t : ℕ) : ℤ)] ∨
      ((s₀ + b * t : ℕ) : ℤ) ≡ -1 [ZMOD ((r₀ + 0 * t : ℕ) : ℤ)]) := by
  refine ⟨0, r₀, hr, fun t _ => ?_⟩
  simp only [zero_mul, add_zero]
  have h : ((s₀ + b * (t + r₀) : ℕ) : ℤ) ≡ ((s₀ + b * t : ℕ) : ℤ) [ZMOD (r₀ : ℤ)] := by
    rw [modEq_iff_dvd']; push_cast; exact ⟨b, by ring⟩
  constructor
  · rintro (h1 | h1)
    · exact Or.inl (h.trans h1)
    · exact Or.inr (h.trans h1)
  · rintro (h1 | h1)
    · exact Or.inl (h.symm.trans h1)
    · exact Or.inr (h.symm.trans h1)

/-- **Reduction of the ray statement** to the K3 classification and the two boundary families. -/
theorem main_of_K3Statement (hK : K3Statement)
    (h1 : ∃ N : ℕ, ∀ s : ℕ, N ≤ s → PE 1 s) (h2 : ∃ N : ℕ, ∀ r : ℕ, N ≤ r → PE r 1)
    (r₀ s₀ a b : ℕ) (hr : 1 ≤ r₀) (hs : 1 ≤ s₀) :
    EvPer (fun t => PE (r₀ + a * t : ℕ) (s₀ + b * t : ℕ)) := by
  by_cases hab : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    exact evPer_of_const (PE r₀ s₀) 0 fun t _ => by simp
  by_cases hA : a = 0 ∧ r₀ = 1
  · obtain ⟨rfl, rfl⟩ := hA
    have hb : 0 < b := by omega
    obtain ⟨N, hN⟩ := h1
    refine evPer_of_const True N fun t ht => ?_
    simp only [iff_true]
    have := hN (s₀ + b * t) (by nlinarith)
    simpa using this
  by_cases hB : b = 0 ∧ s₀ = 1
  · obtain ⟨rfl, rfl⟩ := hB
    have ha : 0 < a := by omega
    obtain ⟨N, hN⟩ := h2
    refine evPer_of_const True N fun t ht => ?_
    simp only [iff_true]
    have := hN (r₀ + a * t) (by nlinarith)
    simpa using this
  have hQ : ∀ t : ℕ, 1 ≤ t → (PE (r₀ + a * t : ℕ) (s₀ + b * t : ℕ) ↔
      (((s₀ + b * t : ℕ) : ℤ) ≡ 1 [ZMOD ((r₀ + a * t : ℕ) : ℤ)] ∨
        ((s₀ + b * t : ℕ) : ℤ) ≡ -1 [ZMOD ((r₀ + a * t : ℕ) : ℤ)])) := by
    intro t ht
    have hr2 : 2 ≤ r₀ + a * t := by
      by_cases ha : a = 0
      · subst ha; omega
      · nlinarith [Nat.pos_of_ne_zero ha]
    have hs2 : 2 ≤ s₀ + b * t := by
      by_cases hb : b = 0
      · subst hb; omega
      · nlinarith [Nat.pos_of_ne_zero hb]
    exact hK _ _ hr2 hs2
  refine evPer_of_iff 1 hQ ?_
  by_cases ha : a = 0
  · subst ha; exact crit_evPer_zero r₀ s₀ b (by omega)
  · exact crit_evPer_pos r₀ s₀ a b (Nat.pos_of_ne_zero ha) (by omega)

/-- **Conditional ray theorem**: `NoThreeCommon` for all `r, s ≥ 2` and the two boundary
families give the ray statement. -/
theorem main_of_noThree
    (hN : ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → Claude2K3.NoThreeCommon r s)
    (h1 : ∃ N : ℕ, ∀ s : ℕ, N ≤ s → PE 1 s) (h2 : ∃ N : ℕ, ∀ r : ℕ, N ≤ r → PE r 1)
    (r₀ s₀ a b : ℕ) (hr : 1 ≤ r₀) (hs : 1 ≤ s₀) :
    EvPer (fun t => PE (r₀ + a * t : ℕ) (s₀ + b * t : ℕ)) :=
  main_of_K3Statement (Claude2K3.k3_statement_of_no_three hN) h1 h2 r₀ s₀ a b hr hs

end Claude4K3

#print axioms Claude4K3.main_of_noThree
