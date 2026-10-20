import Formal.Claude3GeoSeam
import Formal.Claude3FoldSyntax

/-!
# Theorem 1a, G4: face-passage states, transitions, and the four path conditions (interfaces)

Written by a Claude worker (2026-10-20, Theorem 1a, parts G4/G5), against
`Formal.Claude3ChallengeSpec` (namespace `ClaudeChallenge2`, version 2) and the geometric
foundation `Formal.Claude3Geo*` (namespace `ClaudeChallenge2.Geo`). Definitions only; the
reduction theorem is stated as `ReductionStatement` and proved in `Claude3StateMain`.

Paper §3.1–3.4 (`lem:rows`, `lem:restricted`, `lem:mso-path`).

## States

* `PType S` (finite): chart `f`, direction `k < 6`, root data (`none`, or the marked corner where
  the path starts), terminal data (`none`, or the marked corner where it ends), and `par`, the
  parity of the number of vertices output before this passage (the root's two saved vertices
  count, so the root has `par = false`).
* A state is `(τ, h) : PType S × ℤ`; its row is the rotated row walk
  `rp σ i = rotN k (rowPt h i)` (paper eq. (rows)) in chart `f`. The heights range over the
  affine interval `stLo τ ≤ h ≤ stHi τ` (both rows inside the rotated chart), so the states at
  `t` are exactly `R002.Claude3Fold.St stLo stHi t` (`mem_St_iff`), the state domain of the
  restricted height arithmetic `HF`.
* Max/min branches and the row-parity phase of the paper's types are **not** stored: they are
  Boolean combinations of atoms `±h ≤ a t + b` and can be case-split inside formulas (G6). Only
  information that is not local (root/terminal corner, count parity) is in the type.

## Passages (all relational, at a fixed parameter `t`)

* `RV t σ i v` : `v` is the vertex of the row point `rp σ i` (which lies in chart `f`).
* `RootAt t σ i` : `σ` is a root type whose corner is the vertex of `rp σ i` (start index).
* `ExitAt t σ e` : the last triangle index: `e = hi` (end of the row in the chart) for an
  ordinary exit, the index with `rp σ (e+2)` at the terminal corner for a terminal exit.
* `PassOK t σ i e` : rows in the chart, `lo ≤ i ≤ e ≤ hi`, and `ExitAt`. The passage is the
  vertex sequence `rp σ i, …, rp σ (e+2)`; its new output is `rp σ (i+2), …, rp σ (e+2)`
  (`OutV`, `e - i + 1` vertices).
* `TransAt t x y i` : the **generic transition** (design memo, summary item 4): `x` has an
  ordinary exit at `u = hi`, `y` is not a root, `y` has a passage entered at `i`, and its first
  triangle `(a', b', c') = (rp y i, rp y (i+1), rp y (i+2))` satisfies `a' ∼ q_{u+1}`,
  `b' ∼ q_{u+2}`, `c' ≁ q_u`. Under `TwoCommonNeighbors`, `c'` is then the forced continuation.
  The entry index of a non-root state is thus determined by its predecessor, not by the state
  alone (this avoids the open seam cases of memo §5.3).

## The four conditions of `lem:mso-path` on a set `X` of states

* `CondPass` : every state of `X` has an entry (root or a transition from `X`) and a valid
  passage;
* `CondDeg` (condition 1) : a unique root state `a` and a unique terminal state `b` in `X`;
  every non-terminal state has exactly one successor in `X`, every non-root state exactly one
  predecessor (roots have no predecessors and terminals no successors by definition);
* `CondConn` (condition 2) : every nonempty proper subset has a transition across its boundary;
* `CondDisj` (condition 3) : outputs of distinct states are disjoint, and disjoint from the two
  saved root vertices — stated through **own-state full tails** (`OwnStart`: `lo` of the row, or
  the root index), so that no clause couples three heights (revised 2026-10-20 after the G3b
  interface: the entry of a non-root state is still given by its predecessor, but only inside
  the two-state transition clause);
* `CondEnds` (condition 4) : degrees `5, 6` at the root's two saved vertices and `6, 5` at the
  terminal's last two; count parity (`par`) consistent, total vertex count even; at least four
  vertices for a one-passage path.

`Cond` is the conjunction; `CondCore` omits `CondConn` (not needed for `⇐`).
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo

/-- State types. -/
structure PType (S : Sig) where
  /-- the chart -/
  f : Fin S.C
  /-- the direction: the row walk is rotated by `rotN k` -/
  k : Fin 6
  /-- root data: the marked corner where the path starts -/
  root : Option (Fin S.M)
  /-- terminal data: the marked corner where the path ends -/
  term : Option (Fin S.M)
  /-- parity of the number of vertices output before this passage -/
  par : Bool

variable {S : Sig}

/-- Encoding of a state type as a tuple. -/
def PType.toProd (τ : PType S) :
    Fin S.C × Fin 6 × Option (Fin S.M) × Option (Fin S.M) × Bool :=
  (τ.f, τ.k, τ.root, τ.term, τ.par)

theorem PType.toProd_injective : Function.Injective (PType.toProd (S := S)) := by
  rintro ⟨f, k, r, e, p⟩ ⟨f', k', r', e', p'⟩ h
  simp only [PType.toProd, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

instance : Finite (PType S) := Finite.of_injective _ PType.toProd_injective

/-- States: a type and a row height. -/
abbrev PState (S : Sig) : Type := PType S × ℤ

/-- The chart of a type, pulled back along the rotation of its direction. -/
def rc (τ : PType S) : Chart := rotPreN τ.k (S.chart τ.f)

/-- The `i`-th point of the row walk of a state (a lattice point of chart `σ.1.f` when it is in
the chart). -/
def rp (σ : PState S) (i : ℤ) : ℤ × ℤ := rotN σ.1.k (rowPt σ.2 i)

/-- `v` is the vertex of the row point `rp σ i`. -/
def RV (t : ℕ) (σ : PState S) (i : ℤ) (v : Vertex S t) : Prop :=
  ∃ hz : (S.chart σ.1.f).Mem t (rp σ i), pt S t σ.1.f (rp σ i) hz = v

/-- Both rows `h, h+1` of the state lie in the rotated chart. -/
def RowsIn (t : ℕ) (σ : PState S) : Prop :=
  (rc σ.1).ly.eval t ≤ σ.2 ∧ σ.2 + 1 ≤ (rc σ.1).uy.eval t

/-- First triangle index of the full row in the chart (paper `ℓ`). -/
def loS (t : ℕ) (σ : PState S) : ℤ := lo (rc σ.1) t σ.2

/-- Last triangle index of the full row in the chart (paper `u`). -/
def hiS (t : ℕ) (σ : PState S) : ℤ := hi (rc σ.1) t σ.2

/-- `v` is the vertex of the marked corner `m`. -/
def CornerV (t : ℕ) (m : Fin S.M) (v : Vertex S t) : Prop :=
  ∃ hm : (S.chart (S.mchart m)).Mem t ((S.mx m).eval t, (S.my m).eval t),
    vtx ⟨(S.mchart m, ((S.mx m).eval t, (S.my m).eval t)), hm⟩ = v

/-- The row point `rp σ i` is the marked corner `m`. -/
def AtCorner (t : ℕ) (σ : PState S) (i : ℤ) (m : Fin S.M) : Prop :=
  ∃ v, RV t σ i v ∧ CornerV t m v

/-- `σ` is a root state and `i` its start index. -/
def RootAt (t : ℕ) (σ : PState S) (i : ℤ) : Prop :=
  ∃ m, σ.1.root = some m ∧ AtCorner t σ i m

/-- `e` is the last triangle index of the passage of `σ`: the end of the row for an ordinary
exit, the terminal corner (at `rp σ (e+2)`) for a terminal exit. -/
def ExitAt (t : ℕ) (σ : PState S) (e : ℤ) : Prop :=
  (σ.1.term = none → e = hiS t σ) ∧ ∀ m, σ.1.term = some m → AtCorner t σ (e + 2) m

/-- The passage of `σ` entered at triangle index `i` and left at `e` is valid. -/
def PassOK (t : ℕ) (σ : PState S) (i e : ℤ) : Prop :=
  RowsIn t σ ∧ loS t σ ≤ i ∧ i ≤ e ∧ e ≤ hiS t σ ∧ ExitAt t σ e

/-- The new output of the passage `(σ, i, e)`: the vertices of `rp σ (i+2), …, rp σ (e+2)`. -/
def OutV (t : ℕ) (σ : PState S) (i e : ℤ) (v : Vertex S t) : Prop :=
  ∃ j, i + 2 ≤ j ∧ j ≤ e + 2 ∧ RV t σ j v

/-- **Generic transition** from `x` to `y`, with entry index `i` of `y`: the first triangle
`(a', b', c')` of `y` satisfies `a' ∼ q_{u+1}`, `b' ∼ q_{u+2}`, `c' ≁ q_u` for the last
triangle index `u = hi` of `x`. -/
def TransAt (t : ℕ) (x y : PState S) (i : ℤ) : Prop :=
  x.1.term = none ∧ y.1.root = none ∧ (∃ e, PassOK t y i e) ∧
    (∃ v, RV t y i v ∧ RV t x (hiS t x + 1) v) ∧
    (∃ v, RV t y (i + 1) v ∧ RV t x (hiS t x + 2) v) ∧
    (∀ v w, RV t y (i + 2) v → RV t x (hiS t x) w → v ≠ w)

/-- Transition (the entry index is determined by `x` and `y`). -/
def Trans (t : ℕ) (x y : PState S) : Prop := ∃ i, TransAt t x y i

/-- `i` is an entry index of `y` within the state set `X`. -/
def EntryIn (t : ℕ) (X : Set (PState S)) (y : PState S) (i : ℤ) : Prop :=
  RootAt t y i ∨ ∃ x ∈ X, TransAt t x y i

/-- `(y, i, e)` is a passage of the state set `X`. -/
def PassIn (t : ℕ) (X : Set (PState S)) (y : PState S) (i e : ℤ) : Prop :=
  y ∈ X ∧ EntryIn t X y i ∧ PassOK t y i e

/-- Every state of `X` has an entry and a valid passage. -/
def CondPass (t : ℕ) (X : Set (PState S)) : Prop :=
  ∀ y ∈ X, ∃ i e, EntryIn t X y i ∧ PassOK t y i e

/-- **Condition 1**: one root `a`, one terminal `b`; in/out degrees `(0,1)`, `(1,0)`, `(1,1)`
(roots have no incoming and terminals no outgoing transitions by definition of `TransAt`). -/
def CondDeg (t : ℕ) (X : Set (PState S)) : Prop :=
  ∃ a ∈ X, ∃ b ∈ X, a.1.root ≠ none ∧ b.1.term ≠ none ∧
    (∀ x ∈ X, x.1.root ≠ none → x = a) ∧ (∀ x ∈ X, x.1.term ≠ none → x = b) ∧
    (∀ x ∈ X, x.1.term = none → ∃ y ∈ X, Trans t x y ∧ ∀ y' ∈ X, Trans t x y' → y' = y) ∧
    (∀ y ∈ X, y.1.root = none → ∃ x ∈ X, Trans t x y ∧ ∀ x' ∈ X, Trans t x' y → x' = x)

/-- **Condition 2** (connectivity): every nonempty proper subset has a transition across its
boundary. -/
def CondConn (t : ℕ) (X : Set (PState S)) : Prop :=
  ∀ A ⊆ X, A.Nonempty → A ≠ X → ∃ x ∈ X, ∃ y ∈ X, Trans t x y ∧ (x ∈ A ↔ y ∉ A)

/-- The own start of a state: the start `lo` of its row in the chart for a non-root state, the
root corner index for a root state. The **full tail** `OutV t y s e` with `OwnStart t y s` and
`ExitAt t y e` depends on `y` alone. -/
def OwnStart (t : ℕ) (y : PState S) (s : ℤ) : Prop :=
  (y.1.root = none ∧ s = loS t y) ∨ RootAt t y s

/-- **Condition 3** (in a form whose every clause involves at most two heights):
(a) the full tails of two distinct states not linked by a transition are disjoint;
(b) along a transition `x → y` (entry `i`), the output of `y` is disjoint from the full tail
of `x`; (c) the two saved root vertices avoid the full tails of all other states.
Together with conditions 1 and 4 this is exactly "outputs of distinct states are disjoint and
disjoint from the saved root vertices" (the output of a state lies in its full tail). -/
def CondDisj (t : ℕ) (X : Set (PState S)) : Prop :=
  (∀ y s e y' s' e', y ∈ X → y' ∈ X → OwnStart t y s → ExitAt t y e → OwnStart t y' s' →
      ExitAt t y' e' → y ≠ y' → ¬ Trans t y y' → ¬ Trans t y' y →
      ∀ v, OutV t y s e v → ¬ OutV t y' s' e' v) ∧
    (∀ x s e y i e', x ∈ X → y ∈ X → OwnStart t x s → ExitAt t x e → TransAt t x y i →
      ExitAt t y e' → ∀ v, OutV t y i e' v → ¬ OutV t x s e v) ∧
    (∀ x i₀ y s e, x ∈ X → y ∈ X → RootAt t x i₀ → y ≠ x → OwnStart t y s → ExitAt t y e →
      ∀ v, (RV t x i₀ v ∨ RV t x (i₀ + 1) v) → ¬ OutV t y s e v)

/-- **Condition 4**: endpoint degrees `5, 6, …, 6, 5`; the count parity starts even, is updated
by `e - i + 1` along transitions and ends even; a one-passage path has at least four
vertices. -/
def CondEnds (t : ℕ) (X : Set (PState S)) : Prop :=
  (∀ x ∈ X, ∀ i, RootAt t x i →
      (∀ v, RV t x i v → deg (graph S t) v = 5) ∧ (∀ v, RV t x (i + 1) v → deg (graph S t) v = 6)) ∧
    (∀ y i e, PassIn t X y i e → y.1.term ≠ none →
      (∀ v, RV t y (e + 2) v → deg (graph S t) v = 5) ∧
        (∀ v, RV t y (e + 1) v → deg (graph S t) v = 6)) ∧
    (∀ x ∈ X, x.1.root ≠ none → x.1.par = false) ∧
    (∀ x i e y i', PassIn t X x i e → y ∈ X → TransAt t x y i' →
      (y.1.par = x.1.par ↔ Even (e - i + 1))) ∧
    (∀ y i e, PassIn t X y i e → y.1.term ≠ none → (y.1.par = false ↔ Even (e - i + 1))) ∧
    (∀ x i e, PassIn t X x i e → x.1.root ≠ none → x.1.term ≠ none → i + 1 ≤ e)

/-- The four conditions of `lem:mso-path` (with the passage condition). -/
def Cond (t : ℕ) (X : Set (PState S)) : Prop :=
  CondPass t X ∧ CondDeg t X ∧ CondConn t X ∧ CondDisj t X ∧ CondEnds t X

/-- The conditions without connectivity (enough for the converse direction). -/
def CondCore (t : ℕ) (X : Set (PState S)) : Prop :=
  CondPass t X ∧ CondDeg t X ∧ CondDisj t X ∧ CondEnds t X

/-! ## The state domain as an `HF` domain -/

/-- Lower height bound of a type (`h ≥ L_y` of the rotated chart). -/
def stLo (τ : PType S) : R002.Claude3Fold.Aff := ⟨(rc τ).ly.a, (rc τ).ly.b⟩

/-- Upper height bound of a type (`h ≤ U_y - 1` of the rotated chart). -/
def stHi (τ : PType S) : R002.Claude3Fold.Aff := ⟨(rc τ).uy.a, (rc τ).uy.b - 1⟩

theorem mem_St_iff (t : ℕ) (σ : PState S) :
    σ ∈ R002.Claude3Fold.St stLo stHi t ↔ RowsIn t σ := by
  obtain ⟨τ, h⟩ := σ
  simp only [R002.Claude3Fold.St, Set.mem_ofPred_eq, RowsIn, stLo, stHi,
    R002.Claude3Fold.Aff.eval, Aff.eval]
  constructor <;> intro H <;> omega

/-- **G5, the reduction theorem (statement).** Under `Valid` and `TrianglesInCharts` at `t`,
a literal path exists iff some set of states at `t` satisfies the four conditions. -/
def ReductionStatement : Prop :=
  ∀ (S : Sig) (t : ℕ), Valid S t → ClaudeChallenge2.TrianglesInCharts S t →
    (PathExists S t ↔ ∃ X ⊆ R002.Claude3Fold.St (stLo (S := S)) stHi t, Cond t X)

/-- The same with the conditions without connectivity. -/
def ReductionCoreStatement : Prop :=
  ∀ (S : Sig) (t : ℕ), Valid S t → ClaudeChallenge2.TrianglesInCharts S t →
    (PathExists S t ↔ ∃ X ⊆ R002.Claude3Fold.St (stLo (S := S)) stHi t, CondCore t X)

end ClaudeChallenge2.State
