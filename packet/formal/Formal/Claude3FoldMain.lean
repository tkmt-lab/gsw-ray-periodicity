import Formal.Claude3FoldSyntax
import Mathlib.Tactic.Ring

/-!
# Folding the restricted arithmetic into a unary word (paper §3.3, `lem:folding`)

Write `t = 2n + η` (`η ∈ {0,1}`) and a height `h = j t + y` (`0 ≤ y < t`, `|j| ≤ J`).
A *copy* is `c = (τ, j, side) : Cp T J` with `side ∈ {L, R, M}`; position `v < n` of the
unary word of length `n` in copy `c` decodes to the state (`dec`)
`(τ, j t + v)` (L), `(τ, j t + t - 1 - v)` (R), `(τ, j t + n)` (M, independent of `v`).
For `n ≥ J + 1` every state at `t` is a decoded position (`exists_dec`).

Under decoding, a height is `A n + B + s v` with `s ∈ {-1,0,1}` and `A` even when `s ≠ 0`
(`dec_snd`, `even_cA`), so every atom becomes a restricted atom of `Claude3FoldLin`.
A first-order quantifier becomes a finite disjunction over copies, a set quantifier a block of
one set quantifier per copy (`EvDef.exSN`). Hence (`evDef_tr`) the truth of every formula is
eventually MSO-definable, and (`eventuallyPeriodic_holds`) every sentence holds on an
eventually periodic set of parameters `t`.
-/

namespace R002.Claude3Fold

open R002.Claude3Mso MSO

universe u

/-- the three folds of `[0, t)` -/
inductive Side
  | L
  | R
  | M

/-- enumeration of the sides -/
def Side.ofFin : Fin 3 → Side
  | 0 => .L
  | 1 => .R
  | 2 => .M

instance : Finite Side :=
  Finite.of_surjective Side.ofFin (by
    intro x; cases x
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩])

variable {T : Type u}

/-- copies: original type, quotient index `j + J ∈ [0, 2J]`, side -/
abbrev Cp (T : Type u) (J : ℕ) := T × Fin (2 * J + 1) × Side

section Decode

variable (η J : ℕ)

/-- the quotient `j` of a copy -/
def jOf (c : Cp T J) : ℤ := ((c.2.1 : ℕ) : ℤ) - J

/-- the remainder `y` of position `v` in a copy of side `s` -/
def yOf (n : ℕ) : Side → ℕ → ℤ
  | .L, v => v
  | .R, v => ((2 * n + η : ℕ) : ℤ) - 1 - v
  | .M, _ => n

/-- decoding a position of copy `c` into a state -/
def dec (n : ℕ) (c : Cp T J) (v : ℕ) : T × ℤ :=
  (c.1, jOf J c * ((2 * n + η : ℕ) : ℤ) + yOf η n c.2.2 v)

@[simp] theorem dec_fst (n : ℕ) (c : Cp T J) (v : ℕ) : (dec η J n c v).1 = c.1 := rfl

/-- coefficient of `n` in a decoded height -/
def cA (c : Cp T J) : ℤ :=
  match c.2.2 with
  | .L => 2 * jOf J c
  | .R => 2 * jOf J c + 2
  | .M => 2 * jOf J c + 1

/-- constant term of a decoded height -/
def cB (c : Cp T J) : ℤ :=
  match c.2.2 with
  | .L => jOf J c * η
  | .R => (jOf J c + 1) * η - 1
  | .M => jOf J c * η

/-- coefficient of the position in a decoded height -/
def sg (c : Cp T J) : ℤ :=
  match c.2.2 with
  | .L => 1
  | .R => -1
  | .M => 0

theorem dec_snd (n : ℕ) (c : Cp T J) (v : ℕ) :
    (dec η J n c v).2 = cA J c * n + cB η J c + sg J c * v := by
  rcases c with ⟨τ, i, s⟩
  cases s <;> simp only [dec, yOf, cA, cB, sg] <;> push_cast <;> ring

theorem sg_isSgn (c : Cp T J) : IsSgn (sg J c) := by
  rcases c with ⟨τ, i, s⟩
  cases s <;> simp [sg, IsSgn]

theorem even_cA (c : Cp T J) (h : sg J c ≠ 0) : Even (cA J c) := by
  rcases c with ⟨τ, i, s⟩
  cases s
  · exact even_two_mul _
  · exact ⟨jOf J (τ, i, Side.R) + 1, by simp only [cA]; ring⟩
  · exact (h rfl).elim

end Decode

theorem isSgn_mul {a b : ℤ} (ha : IsSgn a) (hb : IsSgn b) : IsSgn (a * b) := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp [IsSgn]

theorem le_iff_le_of_sub_eq {a b c d : ℤ} (h : a - b = c - d) : a ≤ b ↔ c ≤ d := by
  rw [← sub_nonpos, h, sub_nonpos]

section Atoms

variable (lo hi : T → Aff) (η J : ℕ) {m k : ℕ}

/-- **Decoded linear atoms.** `ε₁ h₁ + ε₂ h₂ ≤ f(t)` for decoded heights is eventually
MSO-definable (the coefficient of `n` is even whenever both positions occur). -/
theorem evDef_decLin {ε₁ ε₂ : ℤ} (h₁ : IsSgn ε₁) (h₂ : IsSgn ε₂) (c₁ c₂ : Cp T J)
    (x y : Fin m) (f : Aff) :
    EvDef (k := k) (fun n ν _ => ε₁ * (dec η J n c₁ (ν x)).2 + ε₂ * (dec η J n c₂ (ν y)).2 ≤
      f.eval (2 * n + η)) := by
  have hC : ε₁ * sg J c₁ ≠ 0 → ε₂ * sg J c₂ ≠ 0 →
      Even (2 * f.a - ε₁ * cA J c₁ - ε₂ * cA J c₂) := by
    intro e₁ e₂
    exact ((even_two_mul _).sub ((even_cA J c₁ (right_ne_zero_of_mul e₁)).mul_left _)).sub
      ((even_cA J c₂ (right_ne_zero_of_mul e₂)).mul_left _)
  refine (EvDef.lin2 (isSgn_mul h₁ (sg_isSgn J c₁)) (isSgn_mul h₂ (sg_isSgn J c₂))
    (2 * f.a - ε₁ * cA J c₁ - ε₂ * cA J c₂) (f.a * η + f.b - ε₁ * cB η J c₁ - ε₂ * cB η J c₂)
    hC x y).congr 0 fun n _ ν _ _ => ?_
  rw [dec_snd, dec_snd, Aff.eval]
  apply le_iff_le_of_sub_eq
  push_cast
  ring

/-- decoded state equality -/
theorem evDef_decEq (c₁ c₂ : Cp T J) (x y : Fin m) :
    EvDef (k := k) (fun n ν _ => dec η J n c₁ (ν x) = dec η J n c₂ (ν y)) := by
  refine ((EvDef.const (c₁.1 = c₂.1)).and
    ((evDef_decLin η J (show IsSgn 1 by simp [IsSgn]) (show IsSgn (-1) by simp [IsSgn])
      c₁ c₂ x y ⟨0, 0⟩).and
     (evDef_decLin η J (show IsSgn (-1) by simp [IsSgn]) (show IsSgn 1 by simp [IsSgn])
      c₁ c₂ x y ⟨0, 0⟩))).congr 0 fun n _ ν _ _ => ?_
  rw [Prod.ext_iff, dec_fst, dec_fst]
  simp only [Aff.eval, zero_mul, add_zero, one_mul, neg_mul]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, by linarith⟩

/-- the decoded position is a state at `t = 2n + η` -/
theorem evDef_valid (c : Cp T J) (x : Fin m) :
    EvDef (k := k) (fun n ν _ => dec η J n c (ν x) ∈ St lo hi (2 * n + η)) := by
  refine ((evDef_decLin η J (show IsSgn (-1) by simp [IsSgn]) (show IsSgn 0 by simp [IsSgn])
      c c x x ⟨-(lo c.1).a, -(lo c.1).b⟩).and
    (evDef_decLin η J (show IsSgn 1 by simp [IsSgn]) (show IsSgn 0 by simp [IsSgn])
      c c x x (hi c.1))).congr 0 fun n _ ν _ _ => ?_
  simp only [St, Set.mem_ofPred_eq, dec_fst, Aff.eval, zero_mul, add_zero, one_mul, neg_mul]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩

end Atoms

section Surj

variable (lo hi : T → Aff) (η J : ℕ)

/-- the coefficient bound making `J` large enough -/
def Bounded (lo hi : T → Aff) (J : ℕ) : Prop :=
  ∀ τ, (lo τ).a.natAbs < J ∧ (lo τ).b.natAbs < J ∧ (hi τ).a.natAbs < J ∧ (hi τ).b.natAbs < J

theorem exists_bounded [Finite T] (lo hi : T → Aff) : ∃ J, Bounded lo hi J := by
  have := Fintype.ofFinite T
  let F : T → ℕ := fun τ =>
    (lo τ).a.natAbs + (lo τ).b.natAbs + (hi τ).a.natAbs + (hi τ).b.natAbs
  refine ⟨Finset.univ.sup F + 1, fun τ => ?_⟩
  have h1 : F τ ≤ Finset.univ.sup F := Finset.le_sup (Finset.mem_univ τ)
  change (lo τ).a.natAbs + (lo τ).b.natAbs + (hi τ).a.natAbs + (hi τ).b.natAbs ≤
    Finset.univ.sup F at h1
  omega

/-- Every state at `t = 2n + η` (`η < 2`, `n > J`) is a decoded position. -/
theorem exists_dec (hη : η < 2) (hJ : Bounded lo hi J) {n : ℕ} (hn : J + 1 ≤ n)
    {s : T × ℤ} (hs : s ∈ St lo hi (2 * n + η)) :
    ∃ c : Cp T J, ∃ v, v < n ∧ dec η J n c v = s := by
  obtain ⟨τ, h⟩ := s
  obtain ⟨hlo, hhi⟩ := hs
  simp only [Aff.eval] at hlo hhi
  obtain ⟨b1, b2, b3, b4⟩ := hJ τ
  set tz : ℤ := ((2 * n + η : ℕ) : ℤ) with htz
  have htz' : tz = 2 * (n : ℤ) + η := by rw [htz]; push_cast; ring
  have htpos : (J : ℤ) < tz := by omega
  have e1 : (lo τ).a * tz ≥ -((J : ℤ) - 1) * tz :=
    mul_le_mul_of_nonneg_right (by omega) (by omega)
  have e2 : (hi τ).a * tz ≤ ((J : ℤ) - 1) * tz :=
    mul_le_mul_of_nonneg_right (by omega) (by omega)
  have hb2 : -((J : ℤ) - 1) ≤ (lo τ).b := by omega
  have hb4 : (hi τ).b ≤ (J : ℤ) - 1 := by omega
  have hupper : h < (J : ℤ) * tz := by linarith
  have hlower : -((J : ℤ) * tz) < h := by linarith
  set j := h / tz with hj
  set y := h % tz with hy
  have hdiv : tz * j + y = h := Int.mul_ediv_add_emod h tz
  have hy0 : 0 ≤ y := Int.emod_nonneg h (by omega)
  have hyt : y < tz := Int.emod_lt_of_pos h (by omega)
  have hjJ : j < J := by
    by_contra hc
    have : tz * (J : ℤ) ≤ tz * j := mul_le_mul_of_nonneg_left (by omega) (by omega)
    nlinarith
  have hjJ' : -(J : ℤ) ≤ j := by
    by_contra hc
    have : tz * j ≤ tz * (-(J : ℤ) - 1) := mul_le_mul_of_nonneg_left (by omega) (by omega)
    nlinarith
  let i : Fin (2 * J + 1) := ⟨(j + J).toNat, by omega⟩
  have hi' : jOf J (τ, i, Side.L) = j := by simp only [jOf, i]; omega
  have hjR : jOf J (τ, i, Side.R) = j := hi'
  have hjM : jOf J (τ, i, Side.M) = j := hi'
  by_cases hL : y < n
  · refine ⟨(τ, i, Side.L), y.toNat, by omega, ?_⟩
    simp only [dec, yOf, hi', Prod.mk.injEq, true_and]
    rw [Int.toNat_of_nonneg hy0, ← hdiv]; ring
  by_cases hR : (n : ℤ) + η ≤ y
  · refine ⟨(τ, i, Side.R), (tz - 1 - y).toNat, by omega, ?_⟩
    simp only [dec, yOf, hjR, Prod.mk.injEq, true_and]
    rw [← htz, Int.toNat_of_nonneg (by omega), ← hdiv]; ring
  · refine ⟨(τ, i, Side.M), 0, by omega, ?_⟩
    simp only [dec, yOf, hjM, Prod.mk.injEq, true_and]
    rw [← htz, ← hdiv]
    have : y = n := by omega
    rw [this]; ring

/-- decoding sets of positions, one set per copy -/
def decSet (n : ℕ) (W : Cp T J → Set ℕ) : Set (T × ℤ) :=
  {s | ∃ c v, v < n ∧ v ∈ W c ∧ dec η J n c v ∈ St lo hi (2 * n + η) ∧ dec η J n c v = s}

theorem decSet_subset (n : ℕ) (W : Cp T J → Set ℕ) :
    decSet lo hi η J n W ⊆ St lo hi (2 * n + η) := by
  rintro s ⟨c, v, -, -, hv, rfl⟩
  exact hv

theorem decSet_eq (hη : η < 2) (hJ : Bounded lo hi J) {n : ℕ} (hn : J + 1 ≤ n)
    {X : Set (T × ℤ)} (hX : X ⊆ St lo hi (2 * n + η)) :
    decSet lo hi η J n (fun c => {v | v < n ∧ dec η J n c v ∈ X}) = X := by
  ext s
  constructor
  · rintro ⟨c, v, -, ⟨-, hvX⟩, -, rfl⟩
    exact hvX
  · intro hs
    obtain ⟨c, v, hv, rfl⟩ := exists_dec lo hi η J hη hJ hn (hX hs)
    exact ⟨c, v, hv, ⟨hv, hs⟩, hX hs, rfl⟩

end Surj

end R002.Claude3Fold
