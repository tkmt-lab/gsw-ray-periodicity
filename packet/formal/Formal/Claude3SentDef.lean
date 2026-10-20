import Formal.Claude3StateMain
import Formal.Claude3FoldTheorem
import Formal.Claude3IdentHF

/-!
# Theorem 1a, G6: the sentence statement and the formula toolkit

Written by a Claude worker (2026-10-20, Theorem 1a, parts G6/A).

* `GeoSentenceStatement` : for every signature there is a sentence of the restricted height
  arithmetic (`R002.Claude3Fold.HSentence (PType S)`, bounds `stLo stHi`) that, for all large
  valid `t`, holds iff some state set satisfies the path conditions `CondCore` (G6).
* `HF.ren` : renaming of free state and set variables, with `sat_ren`.
* `typeHF` : a test of a property of the type of a state (a finite disjunction of type atoms).
* `Def1`, `Def2` : definability of one- and two-state predicates (for all large valid `t`,
  on the states at `t`).
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo R002.Claude3Fold

/-- **G6 (statement).** A sentence over the state types whose truth, for all large valid `t`,
is the existence of a state set satisfying the path conditions without connectivity
(`CondCore`; `reduction_core` shows this is equivalent to path existence). -/
def GeoSentenceStatement : Prop :=
  ∀ S : Sig, ∃ φ : HSentence (PType S), ∃ t₂ : ℕ, ∀ t, t₂ ≤ t → Valid S t →
    ClaudeChallenge2.TrianglesInCharts S t →
      ((∃ X ⊆ St (stLo (S := S)) stHi t, CondCore t X) ↔ Holds stLo stHi t φ)

/-! ## Renaming -/

namespace HFR

universe u
variable {T : Type u}

/-- Lift a renaming under a binder. -/
def liftR {m m' : ℕ} (ρ : Fin m → Fin m') : Fin (m + 1) → Fin (m' + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

/-- Renaming of free state variables (`ρ`) and free set variables (`κ`). -/
def ren : {m k m' k' : ℕ} → (Fin m → Fin m') → (Fin k → Fin k') → HF T m k → HF T m' k'
  | _, _, _, _, ρ, _, .typ x τ => .typ (ρ x) τ
  | _, _, _, _, ρ, _, .eq x y => .eq (ρ x) (ρ y)
  | _, _, _, _, ρ, _, .le x f => .le (ρ x) f
  | _, _, _, _, ρ, _, .nle x f => .nle (ρ x) f
  | _, _, _, _, ρ, _, .addLe x y f => .addLe (ρ x) (ρ y) f
  | _, _, _, _, ρ, _, .subLe x y f => .subLe (ρ x) (ρ y) f
  | _, _, _, _, ρ, _, .negAddLe x y f =>
    .negAddLe (ρ x) (ρ y) f
  | _, _, _, _, ρ, _, .modEq x q r => .modEq (ρ x) q r
  | _, _, _, _, _, _, .tModEq q r => .tModEq q r
  | _, _, _, _, _, _, .tNonneg f => .tNonneg f
  | _, _, _, _, ρ, κ, .mem x X => .mem (ρ x) (κ X)
  | _, _, _, _, ρ, κ, .neg φ => .neg (ren ρ κ φ)
  | _, _, _, _, ρ, κ, .and φ ψ => .and (ren ρ κ φ) (ren ρ κ ψ)
  | _, _, _, _, ρ, κ, .exF φ => .exF (ren (liftR ρ) κ φ)
  | _, _, _, _, ρ, κ, .exS φ => .exS (ren ρ (liftR κ) φ)

theorem cons_comp_liftR {α : Type u} {m m' : ℕ} (ρ : Fin m → Fin m') (s : α)
    (ν : Fin m' → α) :
    (fun i => (Fin.cons s ν : Fin (m' + 1) → α) (liftR ρ i)) =
      Fin.cons s (fun i => ν (ρ i)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [liftR]

theorem sat_ren {lo hi : T → R002.Claude3Fold.Aff} {t : ℕ} :
    ∀ {m k m' k' : ℕ} (ρ : Fin m → Fin m') (κ : Fin k → Fin k') (φ : HF T m k)
      (ν : Fin m' → T × ℤ) (V : Fin k' → Set (T × ℤ)),
      HF.Sat lo hi t (ren ρ κ φ) ν V ↔
        HF.Sat lo hi t φ (fun i => ν (ρ i)) (fun i => V (κ i)) := by
  intro m k m' k' ρ κ φ
  induction φ generalizing m' k' with
  | typ => intros; simp [ren]
  | eq => intros; simp [ren]
  | le => intros; simp [ren]
  | nle => intros; simp [ren]
  | addLe => intros; simp [ren]
  | subLe => intros; simp [ren]
  | negAddLe => intros; simp [ren]
  | modEq => intros; simp [ren]
  | tModEq => intros; simp [ren]
  | tNonneg => intros; simp [ren]
  | mem => intros; simp [ren]
  | neg φ ih => intro ν V; simp only [ren, HF.Sat, ih]
  | and φ ψ ih₁ ih₂ => intro ν V; simp only [ren, HF.Sat, ih₁, ih₂]
  | exF φ ih =>
    intro ν V
    simp only [ren, HF.Sat, ih, cons_comp_liftR]
  | exS φ ih =>
    intro ν V
    simp only [ren, HF.Sat, ih, cons_comp_liftR]

end HFR

/-! ## Type tests -/

variable {S : Sig}

/-- A fixed list of all state types. -/
noncomputable def allTypes (S : Sig) : List (PType S) :=
  (Finite.exists_univ_list (PType S)).choose

theorem mem_allTypes (τ : PType S) : τ ∈ allTypes S :=
  (Finite.exists_univ_list (PType S)).choose_spec.2 τ

open Classical in
/-- The type of state `x` has property `p`. -/
noncomputable def typeHF {m k : ℕ} (p : PType S → Prop) (x : Fin m) : HF (PType S) m k :=
  bigOr ((allTypes S).map fun τ => if p τ then HF.typ x τ else hfFalse)

theorem sat_typeHF {lo hi : PType S → R002.Claude3Fold.Aff} {t : ℕ} {m k : ℕ}
    (p : PType S → Prop) (x : Fin m) (ν : Fin m → PState S) (V : Fin k → Set (PState S)) :
    HF.Sat lo hi t (typeHF p x) ν V ↔ p (ν x).1 := by
  classical
  simp only [typeHF, sat_bigOr, List.mem_map]
  constructor
  · rintro ⟨φ, ⟨τ, -, rfl⟩, h⟩
    by_cases hp : p τ
    · simp only [hp, ↓reduceIte, HF.Sat] at h
      exact h ▸ hp
    · simp only [hp, ↓reduceIte] at h
      exact absurd h sat_hfFalse
  · intro hp
    exact ⟨_, ⟨(ν x).1, mem_allTypes _, rfl⟩, by simp [hp]⟩

/-! ## Definability of one- and two-state predicates -/

/-- `P` is defined, on the states at every large valid `t`, by a formula with one free state
variable. -/
def Def1 (S : Sig) (P : ℕ → PState S → Prop) : Prop :=
  ∃ φ : HF (PType S) 1 0, ∃ t₂ : ℕ, ∀ t, t₂ ≤ t → Valid S t →
    ClaudeChallenge2.TrianglesInCharts S t → ∀ x ∈ St (stLo (S := S)) stHi t,
      (HF.Sat stLo stHi t φ ![x] Fin.elim0 ↔ P t x)

/-- `R` is defined, on the states at every large valid `t`, by a formula with two free state
variables (`0 ↦ x`, `1 ↦ y`). -/
def Def2 (S : Sig) (R : ℕ → PState S → PState S → Prop) : Prop :=
  ∃ φ : HF (PType S) 2 0, ∃ t₂ : ℕ, ∀ t, t₂ ≤ t → Valid S t →
    ClaudeChallenge2.TrianglesInCharts S t → ∀ x ∈ St (stLo (S := S)) stHi t,
      ∀ y ∈ St (stLo (S := S)) stHi t, (HF.Sat stLo stHi t φ ![x, y] Fin.elim0 ↔ R t x y)

/-- Place a one-state formula at variable `a`. -/
def at1 {m k : ℕ} (φ : HF (PType S) 1 0) (a : Fin m) : HF (PType S) m k :=
  HFR.ren ![a] Fin.elim0 φ

/-- Place a two-state formula at variables `a, b`. -/
def at2 {m k : ℕ} (φ : HF (PType S) 2 0) (a b : Fin m) : HF (PType S) m k :=
  HFR.ren ![a, b] Fin.elim0 φ

theorem elim0_eq {α : Type} (V : Fin 0 → α) : V = Fin.elim0 := funext fun i => i.elim0

theorem sat_at1 {lo hi : PType S → R002.Claude3Fold.Aff} {t : ℕ} {m k : ℕ}
    (φ : HF (PType S) 1 0) (a : Fin m) (ν : Fin m → PState S) (V : Fin k → Set (PState S)) :
    HF.Sat lo hi t (at1 φ a) ν V ↔ HF.Sat lo hi t φ ![ν a] Fin.elim0 := by
  rw [at1, HFR.sat_ren, elim0_eq (fun i => V _)]
  have : (fun i => ν (![a] i)) = ![ν a] := by
    funext i; refine Fin.cases ?_ (fun i => i.elim0) i; rfl
  rw [this]

theorem sat_at2 {lo hi : PType S → R002.Claude3Fold.Aff} {t : ℕ} {m k : ℕ}
    (φ : HF (PType S) 2 0) (a b : Fin m) (ν : Fin m → PState S) (V : Fin k → Set (PState S)) :
    HF.Sat lo hi t (at2 φ a b) ν V ↔ HF.Sat lo hi t φ ![ν a, ν b] Fin.elim0 := by
  rw [at2, HFR.sat_ren, elim0_eq (fun i => V _)]
  have : (fun i => ν (![a, b] i)) = ![ν a, ν b] := by
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => i.elim0) i) i <;> rfl
  rw [this]

end ClaudeChallenge2.State
