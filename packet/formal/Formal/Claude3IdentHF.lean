import Formal.Claude3IdentMeet
import Formal.Claude3FoldSyntax

/-!
# Theorem 1a, G3b (3): identification formulas in the restricted arithmetic `HF`

Written by a Claude worker (2026-10-20, Theorem 1a, part G3b).

Translation of the pairwise atoms `PA` into the formulas `R002.Claude3Fold.HF` over states
`(τ, h)`, and the packaged identification formula.

* `toFAff` : the affine functions of the specification as those of `R002.Claude3Fold`.
* `PA.toHF x y`, `PA.sat_toHF` : an `OK` atom (coefficients in `{-1,0,1}`) is one `HF` atom
  (`le`, `nle`, `addLe`, `subLe`, `negAddLe` or `tNonneg`).
* `bigAnd`, `bigOr` with their semantics.
* **`meetHF R₁ R₂ x y`**, **`sat_meetHF`** : under `Embedded S t`,
  `HF.Sat lo hi t (meetHF R₁ R₂ x y) ν V ↔ Meet S t R₁ (ν x).2 R₂ (ν y).2`.
* `meetHF1 R₁ R₂ y`, `sat_meetHF1` : the same with the first row at height `0`.
-/

namespace ClaudeChallenge2.Geo

open ClaudeChallenge2 R002.Claude3Fold

universe u

variable {S : Sig} {t : ℕ}

/-- The same affine function, for the formulas. -/
def toFAff (A : ClaudeChallenge2.Aff) : R002.Claude3Fold.Aff := ⟨A.a, A.b⟩

@[simp] theorem toFAff_eval (A : ClaudeChallenge2.Aff) (t : ℕ) :
    (toFAff A).eval t = A.eval t := rfl

variable {T : Type u} {m k : ℕ}

/-- `0 ≤ 0`. -/
def hfTrue : HF T m k := .tNonneg ⟨0, 0⟩

/-- `0 ≤ -1`. -/
def hfFalse : HF T m k := .tNonneg ⟨0, -1⟩

@[simp] theorem sat_hfTrue {lo hi : T → R002.Claude3Fold.Aff} {ν : Fin m → T × ℤ}
    {V : Fin k → Set (T × ℤ)} : HF.Sat lo hi t hfTrue ν V := by
  simp [hfTrue, R002.Claude3Fold.Aff.eval]

@[simp] theorem sat_hfFalse {lo hi : T → R002.Claude3Fold.Aff} {ν : Fin m → T × ℤ}
    {V : Fin k → Set (T × ℤ)} : ¬ HF.Sat lo hi t hfFalse ν V := by
  simp [hfFalse, R002.Claude3Fold.Aff.eval]

/-- Finite conjunction. -/
def bigAnd : List (HF T m k) → HF T m k
  | [] => hfTrue
  | φ :: l => .and φ (bigAnd l)

/-- Finite disjunction. -/
def bigOr : List (HF T m k) → HF T m k
  | [] => hfFalse
  | φ :: l => HF.or φ (bigOr l)

section
variable {lo hi : T → R002.Claude3Fold.Aff} {ν : Fin m → T × ℤ} {V : Fin k → Set (T × ℤ)}

theorem sat_bigAnd (l : List (HF T m k)) :
    HF.Sat lo hi t (bigAnd l) ν V ↔ ∀ φ ∈ l, HF.Sat lo hi t φ ν V := by
  induction l with
  | nil => simp [bigAnd]
  | cons φ l ih => simp [bigAnd, ih]

theorem sat_bigOr (l : List (HF T m k)) :
    HF.Sat lo hi t (bigOr l) ν V ↔ ∃ φ ∈ l, HF.Sat lo hi t φ ν V := by
  induction l with
  | nil => simp [bigOr]
  | cons φ l ih => simp [bigOr, ih]

end

/-- The atom `a (x.h) + b (y.h) ≤ F(t)` (for `a, b ∈ {-1, 0, 1}`). -/
def PA.toHF (x y : Fin m) (c : PA) : HF T m k :=
  if c.a = 0 then
    (if c.b = 0 then .tNonneg (toFAff c.F) else if c.b = 1 then .le y (toFAff c.F)
      else .nle y (toFAff c.F))
  else if c.a = 1 then
    (if c.b = 0 then .le x (toFAff c.F) else if c.b = 1 then .addLe x y (toFAff c.F)
      else .subLe x y (toFAff c.F))
  else
    (if c.b = 0 then .nle x (toFAff c.F) else if c.b = 1 then .subLe y x (toFAff c.F)
      else .negAddLe x y (toFAff c.F))

theorem PA.sat_toHF {c : PA} (hc : c.OK) (x y : Fin m) {lo hi : T → R002.Claude3Fold.Aff}
    (ν : Fin m → T × ℤ) (V : Fin k → Set (T × ℤ)) :
    HF.Sat lo hi t (c.toHF x y) ν V ↔ c.Sat t (ν x).2 (ν y).2 := by
  obtain ⟨a, b, F⟩ := c
  obtain ⟨ha | ha | ha, hb | hb | hb⟩ := hc <;> subst ha <;> subst hb <;>
    simp [PA.toHF, PA.Sat] <;> constructor <;> intro h <;> linarith

/-- The identification formula of two rows, with free state variables `x` (height of `R₁`) and
`y` (height of `R₂`). -/
def meetHF (R₁ R₂ : RowSet S) (x y : Fin m) : HF T m k :=
  bigOr ((wordsLT S S.C).map fun w =>
    if WordOK S w R₂.f R₁.f then bigAnd ((meetPA R₁ R₂ w).map (PA.toHF x y)) else hfFalse)

/-- **Identification as a formula.** Under embeddedness (at this `t`), the formula `meetHF`
holds at a valuation iff the rows meet at the heights of the two state variables. -/
theorem sat_meetHF (hE : Embedded S t) {R₁ R₂ : RowSet S} (hR₁ : R₁.WF) (hR₂ : R₂.WF)
    (x y : Fin m) {lo hi : T → R002.Claude3Fold.Aff} (ν : Fin m → T × ℤ)
    (V : Fin k → Set (T × ℤ)) :
    HF.Sat lo hi t (meetHF R₁ R₂ x y) ν V ↔ Meet S t R₁ (ν x).2 R₂ (ν y).2 := by
  rw [meet_iff_patoms hE hR₁ hR₂, meetHF, sat_bigOr]
  simp only [List.mem_map, mem_wordsLT]
  constructor
  · rintro ⟨φ, ⟨w, hw, rfl⟩, hφ⟩
    split_ifs at hφ with hok
    · rw [sat_bigAnd] at hφ
      refine ⟨w, hw, hok, fun a ha => ?_⟩
      rw [← PA.sat_toHF (meetPA_ok hR₁ hR₂ w a ha) x y (lo := lo) (hi := hi) ν V]
      exact hφ _ (List.mem_map_of_mem ha)
    · exact absurd hφ sat_hfFalse
  · rintro ⟨w, hw, hok, ha⟩
    refine ⟨_, ⟨w, hw, rfl⟩, ?_⟩
    simp only [hok, ↓reduceIte]
    rw [sat_bigAnd]
    intro φ hφ
    obtain ⟨a, haw, rfl⟩ := List.mem_map.1 hφ
    exact (PA.sat_toHF (meetPA_ok hR₁ hR₂ w a haw) x y ν V).2 (ha a haw)

/-- The identification formula with the first row at height `0` and one free variable `y`. -/
def meetHF1 (R₁ R₂ : RowSet S) (y : Fin m) : HF T m k :=
  bigOr ((wordsLT S S.C).map fun w =>
    if WordOK S w R₂.f R₁.f then
      bigAnd ((meetPA R₁ R₂ w).map fun c => (PA.toHF y y ⟨0, c.b, c.F⟩)) else hfFalse)

theorem sat_meetHF1 (hE : Embedded S t) {R₁ R₂ : RowSet S} (hR₁ : R₁.WF) (hR₂ : R₂.WF)
    (y : Fin m) {lo hi : T → R002.Claude3Fold.Aff} (ν : Fin m → T × ℤ)
    (V : Fin k → Set (T × ℤ)) :
    HF.Sat lo hi t (meetHF1 R₁ R₂ y) ν V ↔ Meet S t R₁ 0 R₂ (ν y).2 := by
  have hok0 : ∀ w, ∀ c ∈ meetPA R₁ R₂ w, (⟨0, c.b, c.F⟩ : PA).OK := fun w c hc =>
    ⟨Or.inr (Or.inl rfl), (meetPA_ok hR₁ hR₂ w c hc).2⟩
  have hsat : ∀ c : PA, (⟨0, c.b, c.F⟩ : PA).Sat t (ν y).2 (ν y).2 ↔ c.Sat t 0 (ν y).2 := by
    intro c; simp [PA.Sat]
  rw [meet_iff_patoms hE hR₁ hR₂, meetHF1, sat_bigOr]
  simp only [List.mem_map, mem_wordsLT]
  constructor
  · rintro ⟨φ, ⟨w, hw, rfl⟩, hφ⟩
    split_ifs at hφ with hok
    · rw [sat_bigAnd] at hφ
      refine ⟨w, hw, hok, fun a ha => ?_⟩
      rw [← hsat, ← PA.sat_toHF (hok0 w a ha) y y (lo := lo) (hi := hi) ν V]
      exact hφ _ (List.mem_map_of_mem ha)
    · exact absurd hφ sat_hfFalse
  · rintro ⟨w, hw, hok, ha⟩
    refine ⟨_, ⟨w, hw, rfl⟩, ?_⟩
    simp only [hok, ↓reduceIte]
    rw [sat_bigAnd]
    intro φ hφ
    obtain ⟨a, haw, rfl⟩ := List.mem_map.1 hφ
    exact (PA.sat_toHF (hok0 w a haw) y y ν V).2 ((hsat a).2 (ha a haw))

end ClaudeChallenge2.Geo
