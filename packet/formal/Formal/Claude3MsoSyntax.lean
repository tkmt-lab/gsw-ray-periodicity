import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Set.Basic

/-!
# Monadic second-order logic over finite words: syntax and semantics

Formulas `MSO α m k` have `m` free first-order (position) variables and `k` free set
variables, both in de Bruijn style: index `0` is the innermost binder of that sort.
A first-order binder does not shift set-variable indices and vice versa.

Semantics over a word `w : List α`: positions are naturals below `w.length`;
first-order quantifiers range over `{x | x < w.length}`, set quantifiers over subsets of
`{i | i < w.length}`.
-/

namespace R002.Claude3Mso

universe u

/-- MSO formulas over the alphabet `α` with `m` free position variables and `k` free set
variables. -/
inductive MSO (α : Type u) : ℕ → ℕ → Type u
  /-- `x < y` -/
  | lt {m k : ℕ} : Fin m → Fin m → MSO α m k
  /-- `x = y` -/
  | eq {m k : ℕ} : Fin m → Fin m → MSO α m k
  /-- `succ x y` means `y = x + 1` -/
  | succ {m k : ℕ} : Fin m → Fin m → MSO α m k
  /-- `x ∈ X` -/
  | mem {m k : ℕ} : Fin m → Fin k → MSO α m k
  /-- letter predicate `P_a x` -/
  | lab {m k : ℕ} : α → Fin m → MSO α m k
  /-- negation -/
  | neg {m k : ℕ} : MSO α m k → MSO α m k
  /-- conjunction -/
  | and {m k : ℕ} : MSO α m k → MSO α m k → MSO α m k
  /-- first-order existential quantifier (binds position variable `0`) -/
  | exF {m k : ℕ} : MSO α (m + 1) k → MSO α m k
  /-- set existential quantifier (binds set variable `0`) -/
  | exS {m k : ℕ} : MSO α m (k + 1) → MSO α m k

variable {α : Type u}

namespace MSO

/-- Satisfaction of a formula by a word `w` under a position valuation `ν` and a set
valuation `V`. -/
@[simp]
def Sat (w : List α) : {m k : ℕ} → MSO α m k → (Fin m → ℕ) → (Fin k → Set ℕ) → Prop
  | _, _, .lt x y, ν, _ => ν x < ν y
  | _, _, .eq x y, ν, _ => ν x = ν y
  | _, _, .succ x y, ν, _ => ν y = ν x + 1
  | _, _, .mem x X, ν, V => ν x ∈ V X
  | _, _, .lab a x, ν, _ => w[ν x]? = some a
  | _, _, .neg φ, ν, V => ¬ Sat w φ ν V
  | _, _, .and φ ψ, ν, V => Sat w φ ν V ∧ Sat w ψ ν V
  | _, _, .exF φ, ν, V => ∃ x, x < w.length ∧ Sat w φ (Fin.cons x ν) V
  | _, _, .exS φ, ν, V => ∃ X : Set ℕ, X ⊆ {i | i < w.length} ∧ Sat w φ ν (Fin.cons X V)

/-! ## Derived connectives -/

/-- disjunction -/
def or {m k : ℕ} (φ ψ : MSO α m k) : MSO α m k := .neg (.and (.neg φ) (.neg ψ))
/-- implication -/
def imp {m k : ℕ} (φ ψ : MSO α m k) : MSO α m k := .neg (.and φ (.neg ψ))
/-- biconditional -/
def iff {m k : ℕ} (φ ψ : MSO α m k) : MSO α m k := .and (imp φ ψ) (imp ψ φ)
/-- first-order universal quantifier -/
def allF {m k : ℕ} (φ : MSO α (m + 1) k) : MSO α m k := .neg (.exF (.neg φ))
/-- set universal quantifier -/
def allS {m k : ℕ} (φ : MSO α m (k + 1)) : MSO α m k := .neg (.exS (.neg φ))
/-- `x ≤ y` -/
def le {m k : ℕ} (x y : Fin m) : MSO α m k := or (.lt x y) (.eq x y)
/-- truth: `∀x. x = x` -/
def tt {m k : ℕ} : MSO α m k := allF (.eq 0 0)
/-- falsity -/
def ff {m k : ℕ} : MSO α m k := .neg tt

variable {w : List α} {m k : ℕ} {ν : Fin m → ℕ} {V : Fin k → Set ℕ}

@[simp] theorem sat_or {φ ψ : MSO α m k} : Sat w (or φ ψ) ν V ↔ Sat w φ ν V ∨ Sat w ψ ν V := by
  simp [or]; tauto
@[simp] theorem sat_imp {φ ψ : MSO α m k} : Sat w (imp φ ψ) ν V ↔ (Sat w φ ν V → Sat w ψ ν V) := by
  simp [imp]
@[simp] theorem sat_iff {φ ψ : MSO α m k} : Sat w (iff φ ψ) ν V ↔ (Sat w φ ν V ↔ Sat w ψ ν V) := by
  simp [iff]; tauto
@[simp] theorem sat_allF {φ : MSO α (m + 1) k} :
    Sat w (allF φ) ν V ↔ ∀ x, x < w.length → Sat w φ (Fin.cons x ν) V := by
  simp [allF]
@[simp] theorem sat_allS {φ : MSO α m (k + 1)} :
    Sat w (allS φ) ν V ↔ ∀ X : Set ℕ, X ⊆ {i | i < w.length} → Sat w φ ν (Fin.cons X V) := by
  simp [allS]
@[simp] theorem sat_tt : Sat w (tt : MSO α m k) ν V := by simp [tt]
@[simp] theorem sat_ff : ¬ Sat w (ff : MSO α m k) ν V := by simp [ff]
@[simp] theorem sat_le {x y : Fin m} : Sat w (le x y : MSO α m k) ν V ↔ ν x ≤ ν y := by
  simp [le, le_iff_lt_or_eq]

end MSO

/-- Sentences: no free variables. -/
abbrev Sentence (α : Type u) := MSO α 0 0

/-- `w ⊨ φ` for a sentence `φ`. -/
def Models (w : List α) (φ : Sentence α) : Prop :=
  MSO.Sat w φ (fun i => i.elim0) (fun i => i.elim0)

end R002.Claude3Mso
