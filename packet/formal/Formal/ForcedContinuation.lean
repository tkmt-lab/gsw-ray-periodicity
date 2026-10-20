import Mathlib.Combinatorics.SimpleGraph.Basic
import Formal.SequenceDecision
import Lean.Elab.Tactic.Omega

/-! Local graph layer of R002. The two-common-neighbors condition is an explicit
hypothesis, not a formalization of a triangulated surface. No simplicity of the
whole forced walk is assumed: it may revisit vertices. -/

namespace R002

variable {V : Type*}

def TwoCommonNeighbors (G : SimpleGraph V) : Prop :=
  ∀ b c, G.Adj b c → ∃ x y, x ≠ y ∧
    ∀ v, (G.Adj b v ∧ G.Adj c v) ↔ v = x ∨ v = y

structure OrderedTriangle (G : SimpleGraph V) where
  a : V
  b : V
  c : V
  ab : G.Adj a b
  bc : G.Adj b c
  ca : G.Adj c a

def OtherCommon (G : SimpleGraph V) (a b c d : V) : Prop :=
  (G.Adj b d ∧ G.Adj c d) ∧ d ≠ a

theorem unique_other_common (G : SimpleGraph V) (hG : TwoCommonNeighbors G)
    (t : OrderedTriangle G) : ∃! d, OtherCommon G t.a t.b t.c d := by
  obtain ⟨x, y, hxy, h⟩ := hG t.b t.c t.bc
  rcases (h t.a).mp ⟨t.ab.symm, t.ca⟩ with ha | ha
  · refine ⟨y, ⟨(h y).mpr (Or.inr rfl), ?_⟩, ?_⟩
    · intro hy
      exact hxy (ha.symm.trans hy.symm)
    · intro d hd
      rcases (h d).mp hd.1 with hd' | hd'
      · exact False.elim (hd.2 (hd'.trans ha.symm))
      · exact hd'
  · refine ⟨x, ⟨(h x).mpr (Or.inl rfl), ?_⟩, ?_⟩
    · intro hx
      exact hxy (hx.trans ha)
    · intro d hd
      rcases (h d).mp hd.1 with hd' | hd'
      · exact hd'
      · exact False.elim (hd.2 (hd'.trans ha.symm))

noncomputable def otherVertex (G : SimpleGraph V) (hG : TwoCommonNeighbors G)
    (t : OrderedTriangle G) : V := Classical.choose (unique_other_common G hG t)

theorem otherVertex_spec (G : SimpleGraph V) (hG : TwoCommonNeighbors G)
    (t : OrderedTriangle G) : OtherCommon G t.a t.b t.c (otherVertex G hG t) :=
  (Classical.choose_spec (unique_other_common G hG t)).1

noncomputable def nextTriangle (G : SimpleGraph V) (hG : TwoCommonNeighbors G)
    (t : OrderedTriangle G) : OrderedTriangle G where
  a := t.b
  b := t.c
  c := otherVertex G hG t
  ab := t.bc
  bc := (otherVertex_spec G hG t).1.2
  ca := (otherVertex_spec G hG t).1.1.symm

noncomputable def triangleOrbit (G : SimpleGraph V) (hG : TwoCommonNeighbors G)
    (t : OrderedTriangle G) : ℕ → OrderedTriangle G
  | 0 => t
  | n + 1 => nextTriangle G hG (triangleOrbit G hG t n)

noncomputable def forcedWalk (G : SimpleGraph V) (hG : TwoCommonNeighbors G)
    (t : OrderedTriangle G) (n : ℕ) : V := (triangleOrbit G hG t n).a

theorem forcedWalk_coordinates (G : SimpleGraph V) (hG : TwoCommonNeighbors G)
    (t : OrderedTriangle G) (n : ℕ) :
    forcedWalk G hG t (n + 1) = (triangleOrbit G hG t n).b ∧
    forcedWalk G hG t (n + 2) = (triangleOrbit G hG t n).c ∧
    forcedWalk G hG t (n + 3) = otherVertex G hG (triangleOrbit G hG t n) := by
  exact ⟨rfl, rfl, rfl⟩

def IsForcedWalk (G : SimpleGraph V) (p : ℕ → V) : Prop :=
  ∀ n, G.Adj (p n) (p (n + 1)) ∧ G.Adj (p (n + 1)) (p (n + 2)) ∧
    G.Adj (p (n + 2)) (p n) ∧ p (n + 3) ≠ p n

theorem forcedWalk_is_forced (G : SimpleGraph V) (hG : TwoCommonNeighbors G)
    (t : OrderedTriangle G) : IsForcedWalk G (forcedWalk G hG t) := by
  intro n
  obtain ⟨h1, h2, h3⟩ := forcedWalk_coordinates G hG t n
  rw [h1, h2, h3]
  exact ⟨(triangleOrbit G hG t n).ab, (triangleOrbit G hG t n).bc,
    (triangleOrbit G hG t n).ca, (otherVertex_spec G hG _).2⟩

theorem forced_walk_unique (G : SimpleGraph V) (hG : TwoCommonNeighbors G)
    (p q : ℕ → V) (hp : IsForcedWalk G p) (hq : IsForcedWalk G q)
    (h0 : p 0 = q 0) (h1 : p 1 = q 1) (h2 : p 2 = q 2) : p = q := by
  funext k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk0 : k = 0
    · simpa only [hk0] using h0
    by_cases hk1 : k = 1
    · simpa only [hk1] using h1
    by_cases hk2 : k = 2
    · simpa only [hk2] using h2
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
    have e0 := ih n (by omega)
    have e1 := ih (n + 1) (by omega)
    have e2 := ih (n + 2) (by omega)
    let t : OrderedTriangle G := ⟨p n, p (n + 1), p (n + 2),
      (hp n).1, (hp n).2.1, (hp n).2.2.1⟩
    have hpd : OtherCommon G t.a t.b t.c (p (n + 3)) :=
      ⟨⟨(hp (n + 1)).2.2.1.symm, (hp (n + 2)).1⟩, (hp n).2.2.2⟩
    have hqd : OtherCommon G t.a t.b t.c (q (n + 3)) := by
      change (G.Adj (p (n + 1)) (q (n + 3)) ∧
        G.Adj (p (n + 2)) (q (n + 3))) ∧ q (n + 3) ≠ p n
      rw [e0, e1, e2]
      exact ⟨⟨(hq (n + 1)).2.2.1.symm, (hq (n + 2)).1⟩, (hq n).2.2.2⟩
    obtain ⟨d, _, hd⟩ := unique_other_common G hG t
    exact (hd _ hpd).trans (hd _ hqd).symm

theorem forcedWalk_initial (G : SimpleGraph V) (hG : TwoCommonNeighbors G)
    (t : OrderedTriangle G) :
    forcedWalk G hG t 0 = t.a ∧ forcedWalk G hG t 1 = t.b ∧
      forcedWalk G hG t 2 = t.c := ⟨rfl, rfl, rfl⟩

/-- An initial oriented triangle determines one entire infinite walk. Finite
valid paths are prefixes, tested separately by SequenceDecision. -/
theorem forced_walk_exists_unique (G : SimpleGraph V) (hG : TwoCommonNeighbors G)
    (t : OrderedTriangle G) :
    ∃! p : ℕ → V, IsForcedWalk G p ∧ p 0 = t.a ∧ p 1 = t.b ∧ p 2 = t.c := by
  refine ⟨forcedWalk G hG t, ⟨forcedWalk_is_forced G hG t,
    forcedWalk_initial G hG t⟩, ?_⟩
  intro q hq
  exact forced_walk_unique G hG q (forcedWalk G hG t) hq.1
    (forcedWalk_is_forced G hG t) hq.2.1 hq.2.2.1 hq.2.2.2

/-- Connect the graph construction to the previously checked stopping logic.
No assertion is made here about the geometry or the executable Python adapter. -/
theorem finite_forced_walk_decision [Fintype V] (G : SimpleGraph V)
    (hG : TwoCommonNeighbors G) (t : OrderedTriangle G) (legal : ℕ → Prop) :
    ∃ r ≤ Fintype.card V, FirstRepeat (forcedWalk G hG t) r ∧
      ((∃ n, ValidEnd (forcedWalk G hG t) legal n) ↔ ∃ e < r, legal e) := by
  obtain ⟨r, hr, hfirst⟩ := first_repeat_exists_bounded (forcedWalk G hG t)
  exact ⟨r, hr, hfirst,
    valid_exists_iff_bounded_endpoint (forcedWalk G hG t) legal r hfirst⟩

#print axioms unique_other_common
#print axioms forced_walk_unique
#print axioms forced_walk_exists_unique
#print axioms finite_forced_walk_decision

end R002
