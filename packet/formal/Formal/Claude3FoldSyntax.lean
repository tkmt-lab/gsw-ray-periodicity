import Formal.Claude3FoldLin

/-!
# Restricted arithmetic over heights: syntax and semantics

Paper §3.2 (`lem:restricted`). Fix a type `T` of state types and, for each `τ : T`, affine
bounds `lo τ`, `hi τ` (`a t + b`, integers `a, b`). At parameter `t : ℕ` the states are the
pairs `(τ, h) : T × ℤ` with `lo τ (t) ≤ h ≤ hi τ (t)` (`St lo hi t`).

Formulas `HF T m k` have `m` free state variables and `k` free variables for sets of states
(de Bruijn, index `0` innermost; the two sorts are independent, as for `MSO`). Atoms:
type test, state equality, `±x.h ≤ a t + b`, `x.h + y.h`, `x.h - y.h`, `-x.h - y.h ≤ a t + b`,
`x.h ≡ r [ZMOD q]`, `t ≡ r [MOD q]`, `0 ≤ a t + b`, and `x ∈ X`; connectives `¬`, `∧`,
`∃` over states at `t`, `∃` over sets of states at `t`.
-/

namespace R002.Claude3Fold

universe u

/-- an integer affine function `t ↦ a t + b` -/
structure Aff where
  a : ℤ
  b : ℤ

/-- value at `t` -/
def Aff.eval (f : Aff) (t : ℕ) : ℤ := f.a * (t : ℤ) + f.b

/-- Formulas of the restricted arithmetic over heights. -/
inductive HF (T : Type u) : ℕ → ℕ → Type u
  /-- the type of state `x` is `τ` -/
  | typ {m k : ℕ} : Fin m → T → HF T m k
  /-- `x = y` (as states) -/
  | eq {m k : ℕ} : Fin m → Fin m → HF T m k
  /-- `x.h ≤ f(t)` -/
  | le {m k : ℕ} : Fin m → Aff → HF T m k
  /-- `-x.h ≤ f(t)` -/
  | nle {m k : ℕ} : Fin m → Aff → HF T m k
  /-- `x.h + y.h ≤ f(t)` -/
  | addLe {m k : ℕ} : Fin m → Fin m → Aff → HF T m k
  /-- `x.h - y.h ≤ f(t)` -/
  | subLe {m k : ℕ} : Fin m → Fin m → Aff → HF T m k
  /-- `-x.h - y.h ≤ f(t)` -/
  | negAddLe {m k : ℕ} : Fin m → Fin m → Aff → HF T m k
  /-- `x.h ≡ r [ZMOD q]` -/
  | modEq {m k : ℕ} : Fin m → ℕ → ℤ → HF T m k
  /-- `t ≡ r [MOD q]` -/
  | tModEq {m k : ℕ} : ℕ → ℕ → HF T m k
  /-- `0 ≤ f(t)` -/
  | tNonneg {m k : ℕ} : Aff → HF T m k
  /-- `x ∈ X` -/
  | mem {m k : ℕ} : Fin m → Fin k → HF T m k
  /-- negation -/
  | neg {m k : ℕ} : HF T m k → HF T m k
  /-- conjunction -/
  | and {m k : ℕ} : HF T m k → HF T m k → HF T m k
  /-- `∃ x` over the states at `t` (binds state variable `0`) -/
  | exF {m k : ℕ} : HF T (m + 1) k → HF T m k
  /-- `∃ X` over the sets of states at `t` (binds set variable `0`) -/
  | exS {m k : ℕ} : HF T m (k + 1) → HF T m k

variable {T : Type u}

/-- The states at parameter `t`. -/
def St (lo hi : T → Aff) (t : ℕ) : Set (T × ℤ) :=
  {s | (lo s.1).eval t ≤ s.2 ∧ s.2 ≤ (hi s.1).eval t}

namespace HF

/-- Semantics at parameter `t`. -/
@[simp]
def Sat (lo hi : T → Aff) (t : ℕ) :
    {m k : ℕ} → HF T m k → (Fin m → T × ℤ) → (Fin k → Set (T × ℤ)) → Prop
  | _, _, .typ x τ, ν, _ => (ν x).1 = τ
  | _, _, .eq x y, ν, _ => ν x = ν y
  | _, _, .le x f, ν, _ => (ν x).2 ≤ f.eval t
  | _, _, .nle x f, ν, _ => -(ν x).2 ≤ f.eval t
  | _, _, .addLe x y f, ν, _ => (ν x).2 + (ν y).2 ≤ f.eval t
  | _, _, .subLe x y f, ν, _ => (ν x).2 - (ν y).2 ≤ f.eval t
  | _, _, .negAddLe x y f, ν, _ => -(ν x).2 - (ν y).2 ≤ f.eval t
  | _, _, .modEq x q r, ν, _ => (ν x).2 ≡ r [ZMOD q]
  | _, _, .tModEq q r, _, _ => t ≡ r [MOD q]
  | _, _, .tNonneg f, _, _ => 0 ≤ f.eval t
  | _, _, .mem x X, ν, V => ν x ∈ V X
  | _, _, .neg φ, ν, V => ¬ Sat lo hi t φ ν V
  | _, _, .and φ ψ, ν, V => Sat lo hi t φ ν V ∧ Sat lo hi t ψ ν V
  | _, _, .exF φ, ν, V => ∃ s, s ∈ St lo hi t ∧ Sat lo hi t φ (Fin.cons s ν) V
  | _, _, .exS φ, ν, V => ∃ X, X ⊆ St lo hi t ∧ Sat lo hi t φ ν (Fin.cons X V)

/-! ### Derived connectives -/

/-- disjunction -/
def or {m k : ℕ} (φ ψ : HF T m k) : HF T m k := .neg (.and (.neg φ) (.neg ψ))
/-- implication -/
def imp {m k : ℕ} (φ ψ : HF T m k) : HF T m k := .neg (.and φ (.neg ψ))
/-- `∀ x` over states -/
def allF {m k : ℕ} (φ : HF T (m + 1) k) : HF T m k := .neg (.exF (.neg φ))
/-- `∀ X` over sets of states -/
def allS {m k : ℕ} (φ : HF T m (k + 1)) : HF T m k := .neg (.exS (.neg φ))

variable {lo hi : T → Aff} {t : ℕ} {m k : ℕ} {ν : Fin m → T × ℤ} {V : Fin k → Set (T × ℤ)}

@[simp] theorem sat_or {φ ψ : HF T m k} :
    Sat lo hi t (or φ ψ) ν V ↔ Sat lo hi t φ ν V ∨ Sat lo hi t ψ ν V := by
  simp [or]; tauto
@[simp] theorem sat_imp {φ ψ : HF T m k} :
    Sat lo hi t (imp φ ψ) ν V ↔ (Sat lo hi t φ ν V → Sat lo hi t ψ ν V) := by
  simp [imp]
@[simp] theorem sat_allF {φ : HF T (m + 1) k} :
    Sat lo hi t (allF φ) ν V ↔ ∀ s ∈ St lo hi t, Sat lo hi t φ (Fin.cons s ν) V := by
  simp [allF]
@[simp] theorem sat_allS {φ : HF T m (k + 1)} :
    Sat lo hi t (allS φ) ν V ↔ ∀ X ⊆ St lo hi t, Sat lo hi t φ ν (Fin.cons X V) := by
  simp [allS]

end HF

/-- Sentences: no free variables. -/
abbrev HSentence (T : Type u) := HF T 0 0

/-- `φ` holds at parameter `t`. -/
def Holds (lo hi : T → Aff) (t : ℕ) (φ : HSentence T) : Prop :=
  HF.Sat lo hi t φ (fun i => i.elim0) (fun i => i.elim0)

end R002.Claude3Fold
