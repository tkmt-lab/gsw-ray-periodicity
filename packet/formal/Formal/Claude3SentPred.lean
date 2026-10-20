import Formal.Claude3SentDef

/-!
# Theorem 1a, G6: the atomic predicates of the path conditions

Written by a Claude worker (2026-10-20, Theorem 1a, parts G6/A).

The path conditions `CondCore` quantify over entry/exit indices and vertices. Here they are
rewritten so that every index and vertex quantifier sits inside one of finitely many one- or
two-state predicates (the **atoms**):

* `DaR`, `DbR`, `DcR` : the three clauses of condition 3 for a fixed pair of states;
* `E1P` : the root degree clause of condition 4;
* `PR q`, `PT q` : "every passage of `y` entered at its root (resp. by a transition from `x`)
  has property `q`", for the six passage properties `q : QIdx`.

`Trans t x y ↔ ¬ PT .q0 t x y` (`trans_iff`), and "some passage entered at the root" is
`¬ PR .q0 t y`. `AtomsStatement S` says that all atoms are definable (`Def1`, `Def2`).
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo

variable {S : Sig}

/-- Condition 3 (a) for the pair `(y, y')`. -/
def DaR (t : ℕ) (y y' : PState S) : Prop :=
  ∀ s e s' e', OwnStart t y s → ExitAt t y e → OwnStart t y' s' → ExitAt t y' e' →
    ∀ v, OutV t y s e v → ¬ OutV t y' s' e' v

/-- Condition 3 (b) for the pair `(x, y)`. -/
def DbR (t : ℕ) (x y : PState S) : Prop :=
  ∀ s e i e', OwnStart t x s → ExitAt t x e → TransAt t x y i → ExitAt t y e' →
    ∀ v, OutV t y i e' v → ¬ OutV t x s e v

/-- Condition 3 (c) for the pair `(x, y)`. -/
def DcR (t : ℕ) (x y : PState S) : Prop :=
  ∀ i₀ s e, RootAt t x i₀ → OwnStart t y s → ExitAt t y e →
    ∀ v, (RV t x i₀ v ∨ RV t x (i₀ + 1) v) → ¬ OutV t y s e v

/-- Condition 4, root degrees. -/
def E1P (t : ℕ) (x : PState S) : Prop :=
  ∀ i, RootAt t x i →
    (∀ v, RV t x i v → deg (graph S t) v = 5) ∧ (∀ v, RV t x (i + 1) v → deg (graph S t) v = 6)

/-- The passage properties used by the conditions. -/
inductive QIdx
  /-- false (used for existence of passages) -/
  | q0
  /-- terminal degrees -/
  | qT
  /-- parity update, with the successor's parity bit -/
  | qP (b : Bool)
  /-- terminal parity -/
  | qE
  /-- length of a one-passage path -/
  | qL
  deriving DecidableEq, Fintype

/-- The passage property of an index. -/
def QIdx.Q : QIdx → ℕ → PState S → ℤ → ℤ → Prop
  | .q0, _, _, _, _ => False
  | .qT, t, y, _, e => y.1.term ≠ none →
      (∀ v, RV t y (e + 2) v → deg (graph S t) v = 5) ∧
        (∀ v, RV t y (e + 1) v → deg (graph S t) v = 6)
  | .qP b, _, x, i, e => (b = x.1.par ↔ Even (e - i + 1))
  | .qE, _, y, i, e => y.1.term ≠ none → (y.1.par = false ↔ Even (e - i + 1))
  | .qL, _, x, i, e => x.1.root ≠ none → x.1.term ≠ none → i + 1 ≤ e

/-- Every passage of `y` entered at its root has property `q`. -/
def PR (q : QIdx) (t : ℕ) (y : PState S) : Prop :=
  ∀ i e, RootAt t y i → PassOK t y i e → q.Q t y i e

/-- Every passage of `y` entered by a transition from `x` has property `q`. -/
def PT (q : QIdx) (t : ℕ) (x y : PState S) : Prop :=
  ∀ i e, TransAt t x y i → PassOK t y i e → q.Q t y i e

/-- **The atoms are definable.** -/
def AtomsStatement (S : Sig) : Prop :=
  Def2 S DaR ∧ Def2 S DbR ∧ Def2 S DcR ∧ Def1 S E1P ∧
    ∀ q : QIdx, Def1 S (PR q) ∧ Def2 S (PT q)

/-- The atoms that remain to be defined: all of `AtomsStatement` except `PT .qL`, which is
trivially true (`pt_qL`). -/
def AtomsGap (S : Sig) : Prop :=
  Def2 S DaR ∧ Def2 S DbR ∧ Def2 S DcR ∧ Def1 S E1P ∧ (∀ q : QIdx, Def1 S (PR q)) ∧
    ∀ q : QIdx, q ≠ .qL → Def2 S (PT q)

/-- A transition enters a non-root state, so the one-passage length clause is vacuous. -/
theorem pt_qL (t : ℕ) (x y : PState S) : PT .qL t x y := fun _ _ ht _ hr =>
  absurd ht.2.1 hr

theorem def2_pt_qL : Def2 S (PT .qL) :=
  ⟨hfTrue, 0, fun t _ _ _ x _ y _ => iff_of_true sat_hfTrue (pt_qL t x y)⟩

theorem atomsStatement_of_gap (h : AtomsGap S) : AtomsStatement S := by
  obtain ⟨ha, hb, hc, he, hpr, hpt⟩ := h
  refine ⟨ha, hb, hc, he, fun q => ⟨hpr q, ?_⟩⟩
  by_cases hq : q = .qL
  · subst hq; exact def2_pt_qL
  · exact hpt q hq

/-! ## Logical rewriting -/

theorem trans_iff (t : ℕ) (x y : PState S) : Trans t x y ↔ ¬ PT .q0 t x y := by
  simp only [Trans, PT, QIdx.Q, imp_false, not_forall, not_not]
  constructor
  · rintro ⟨i, h⟩
    obtain ⟨e, he⟩ := h.2.2.1
    exact ⟨i, e, h, he⟩
  · rintro ⟨i, e, h, -⟩
    exact ⟨i, h⟩

theorem rootPass_iff (t : ℕ) (y : PState S) :
    (∃ i e, RootAt t y i ∧ PassOK t y i e) ↔ ¬ PR .q0 t y := by
  simp only [PR, QIdx.Q, imp_false, not_forall, not_not, exists_prop]

theorem condPass_iff (t : ℕ) (X : Set (PState S)) :
    CondPass t X ↔ ∀ y ∈ X, ¬ PR .q0 t y ∨ ∃ x ∈ X, ¬ PT .q0 t x y := by
  simp only [CondPass, EntryIn, PR, PT, QIdx.Q, imp_false, not_forall, not_not]
  refine forall₂_congr fun y _ => ?_
  constructor
  · rintro ⟨i, e, hr | ⟨x, hx, ht⟩, hp⟩
    · exact Or.inl ⟨i, e, hr, hp⟩
    · exact Or.inr ⟨x, hx, i, e, ht, hp⟩
  · rintro (⟨i, e, hr, hp⟩ | ⟨x, hx, i, e, ht, hp⟩)
    · exact ⟨i, e, Or.inl hr, hp⟩
    · exact ⟨i, e, Or.inr ⟨x, hx, ht⟩, hp⟩

theorem passIn_iff (q : QIdx) (t : ℕ) (X : Set (PState S)) (y : PState S) :
    (∀ i e, PassIn t X y i e → q.Q t y i e) ↔
      (y ∈ X → PR q t y ∧ ∀ x ∈ X, PT q t x y) := by
  simp only [PassIn, EntryIn, PR, PT]
  constructor
  · intro H hy
    exact ⟨fun i e hr hp => H i e ⟨hy, Or.inl hr, hp⟩,
      fun x hx i e ht hp => H i e ⟨hy, Or.inr ⟨x, hx, ht⟩, hp⟩⟩
  · rintro H i e ⟨hy, hr | ⟨x, hx, ht⟩, hp⟩
    · exact (H hy).1 i e hr hp
    · exact (H hy).2 x hx i e ht hp

/-- Condition 4 with every passage quantifier inside an atom. -/
def EndsA (t : ℕ) (X : Set (PState S)) : Prop :=
  (∀ x ∈ X, E1P t x) ∧
    (∀ y ∈ X, PR .qT t y ∧ ∀ x ∈ X, PT .qT t x y) ∧
    (∀ x ∈ X, x.1.root ≠ none → x.1.par = false) ∧
    (∀ x ∈ X, ∀ y ∈ X, Trans t x y →
      (y.1.par = true → PR (.qP true) t x ∧ ∀ w ∈ X, PT (.qP true) t w x) ∧
        (y.1.par = false → PR (.qP false) t x ∧ ∀ w ∈ X, PT (.qP false) t w x)) ∧
    (∀ y ∈ X, PR .qE t y ∧ ∀ x ∈ X, PT .qE t x y) ∧
    (∀ y ∈ X, PR .qL t y ∧ ∀ x ∈ X, PT .qL t x y)

theorem forall_passIn_iff (q : QIdx) (t : ℕ) (X : Set (PState S)) :
    (∀ y i e, PassIn t X y i e → q.Q t y i e) ↔ ∀ y ∈ X, PR q t y ∧ ∀ x ∈ X, PT q t x y :=
  forall_congr' fun y => passIn_iff q t X y

theorem condEnds_iff (t : ℕ) (X : Set (PState S)) : CondEnds t X ↔ EndsA t X := by
  unfold CondEnds EndsA
  refine and_congr Iff.rfl (and_congr ?_ (and_congr Iff.rfl (and_congr ?_ (and_congr ?_ ?_))))
  · exact forall_passIn_iff .qT t X
  · have key : ∀ x y : PState S, (∀ i e, PassIn t X x i e → QIdx.Q (.qP y.1.par) t x i e) ↔
        ((y.1.par = true → x ∈ X → PR (.qP true) t x ∧ ∀ w ∈ X, PT (.qP true) t w x) ∧
          (y.1.par = false → x ∈ X → PR (.qP false) t x ∧ ∀ w ∈ X, PT (.qP false) t w x)) := by
      intro x y
      rw [passIn_iff]
      cases y.1.par <;> simp
    constructor
    · intro H x hx y hy ⟨i', ht⟩
      have := (key x y).1 (fun i e hp => H x i e y i' hp hy ht)
      exact ⟨fun h => this.1 h hx, fun h => this.2 h hx⟩
    · intro H x i e y i' hp hy ht
      have := H x hp.1 y hy ⟨i', ht⟩
      exact (key x y).2 ⟨fun h _ => this.1 h, fun h _ => this.2 h⟩ i e hp
  · exact forall_passIn_iff .qE t X
  · exact forall_passIn_iff .qL t X

/-- Condition 3 with every index quantifier inside an atom. -/
def DisjA (t : ℕ) (X : Set (PState S)) : Prop :=
  (∀ y ∈ X, ∀ y' ∈ X, y ≠ y' → ¬ Trans t y y' → ¬ Trans t y' y → DaR t y y') ∧
    (∀ x ∈ X, ∀ y ∈ X, DbR t x y) ∧ (∀ x ∈ X, ∀ y ∈ X, y ≠ x → DcR t x y)

theorem condDisj_iff (t : ℕ) (X : Set (PState S)) : CondDisj t X ↔ DisjA t X := by
  unfold CondDisj DisjA DaR DbR DcR
  refine and_congr ?_ (and_congr ?_ ?_)
  · constructor
    · intro H y hy y' hy' hne h1 h2 s e s' e' hs he hs' he'
      exact H y s e y' s' e' hy hy' hs he hs' he' hne h1 h2
    · intro H y s e y' s' e' hy hy' hs he hs' he' hne h1 h2
      exact H y hy y' hy' hne h1 h2 s e s' e' hs he hs' he'
  · constructor
    · intro H x hx y hy s e i e' hs he ht he'
      exact H x s e y i e' hx hy hs he ht he'
    · intro H x s e y i e' hx hy hs he ht he'
      exact H x hx y hy s e i e' hs he ht he'
  · constructor
    · intro H x hx y hy hne i₀ s e hr hs he
      exact H x i₀ y s e hx hy hr hne hs he
    · intro H x i₀ y s e hx hy hr hne hs he
      exact H x hx y hy hne i₀ s e hr hs he

end ClaudeChallenge2.State
