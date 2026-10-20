import Formal.ForcedContinuation

/-! The finite-path bridge missing from AA. Conditions on p are restricted to
0..n; no hypothesis is imposed on the arbitrary values beyond the endpoint.
For fullerene duals, cone denotes degree five, and non-cone denotes degree six.
The degree interpretation and the surface hypotheses remain external. -/

namespace R002

variable {V : Type*}

structure FiniteTrianglePath (G : SimpleGraph V) (p : ℕ → V) (n : ℕ) : Prop where
  injective : PrefixInjective p n
  adjacent : ∀ i, i + 1 ≤ n → G.Adj (p i) (p (i + 1))
  skipAdjacent : ∀ i, i + 2 ≤ n → G.Adj (p i) (p (i + 2))

theorem finite_path_no_backtrack (G : SimpleGraph V) (p : ℕ → V) (n : ℕ)
    (hp : FiniteTrianglePath G p n) (i : ℕ) (hi : i + 3 ≤ n) :
    p (i + 3) ≠ p i := by
  intro heq
  have := hp.injective (i + 3) hi i (by omega) heq
  omega

/-- A finite simple path is forced solely by its adjacency and injectivity.
There is no assumed infinite extension or non-backtracking hypothesis. -/
theorem finite_path_eq_forced_prefix (G : SimpleGraph V)
    (hG : TwoCommonNeighbors G) (t : OrderedTriangle G) (p : ℕ → V) (n : ℕ)
    (hp : FiniteTrianglePath G p n) (h0 : p 0 = t.a) (h1 : p 1 = t.b)
    (h2 : p 2 = t.c) : ∀ k ≤ n, p k = forcedWalk G hG t k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hkn
    by_cases hk0 : k = 0
    · subst k; exact h0
    by_cases hk1 : k = 1
    · subst k; exact h1
    by_cases hk2 : k = 2
    · subst k; exact h2
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have e0 := ih j (by omega) (by omega)
    have e1 := ih (j + 1) (by omega) (by omega)
    have e2 := ih (j + 2) (by omega) (by omega)
    let u : OrderedTriangle G := ⟨p j, p (j + 1), p (j + 2),
      hp.adjacent j (by omega), hp.adjacent (j + 1) (by omega),
      (hp.skipAdjacent j (by omega)).symm⟩
    have hpd : OtherCommon G u.a u.b u.c (p (j + 3)) :=
      ⟨⟨hp.skipAdjacent (j + 1) (by omega), hp.adjacent (j + 2) (by omega)⟩,
        finite_path_no_backtrack G p n hp j hkn⟩
    have hwd : OtherCommon G u.a u.b u.c (forcedWalk G hG t (j + 3)) := by
      change (G.Adj (p (j + 1)) (forcedWalk G hG t (j + 3)) ∧
        G.Adj (p (j + 2)) (forcedWalk G hG t (j + 3))) ∧
          forcedWalk G hG t (j + 3) ≠ p j
      rw [e0, e1, e2]
      have hw := forcedWalk_is_forced G hG t
      exact ⟨⟨(hw (j + 1)).2.2.1.symm, (hw (j + 2)).1⟩, (hw j).2.2.2⟩
    obtain ⟨d, _, hd⟩ := unique_other_common G hG u
    exact (hd _ hpd).trans (hd _ hwd).symm

theorem forced_prefix_is_finite_path (G : SimpleGraph V)
    (hG : TwoCommonNeighbors G) (t : OrderedTriangle G) (n : ℕ)
    (hi : PrefixInjective (forcedWalk G hG t) n) :
    FiniteTrianglePath G (forcedWalk G hG t) n := by
  have hw := forcedWalk_is_forced G hG t
  exact ⟨hi, fun i _ => (hw i).1, fun i _ => (hw i).2.2.1.symm⟩

theorem legal_endpoint_of_prefix_eq (cone : V → Prop) (p q : ℕ → V) (n : ℕ)
    (h : ∀ k ≤ n, p k = q k) (hp : LegalConeEndpoint cone p n) :
    LegalConeEndpoint cone q n := by
  obtain ⟨hmin, hodd, hc, hn⟩ := hp
  rw [h n (by omega)] at hc
  rw [h (n - 1) (by omega)] at hn
  exact ⟨hmin, hodd, hc, hn⟩

/-- Literal finite path from the oriented triangle t. Only the closed prefix is
constrained; in a degree-5/6 dual graph cone is precisely the degree-5 predicate. -/
structure LiteralPathFrom (G : SimpleGraph V) (cone : V → Prop)
    (t : OrderedTriangle G) (p : ℕ → V) (n : ℕ) : Prop where
  finitePath : FiniteTrianglePath G p n
  initial0 : p 0 = t.a
  initial1 : p 1 = t.b
  initial2 : p 2 = t.c
  startCone : cone (p 0)
  secondNotCone : ¬ cone (p 1)
  endpoint : LegalConeEndpoint cone p n

theorem literal_path_iff_valid_forced_prefix (G : SimpleGraph V)
    (hG : TwoCommonNeighbors G) (cone : V → Prop) (t : OrderedTriangle G)
    (hc : cone t.a) (hb : ¬ cone t.b) :
    (∃ n p, LiteralPathFrom G cone t p n) ↔
      ∃ n, ValidEnd (forcedWalk G hG t) (LegalConeEndpoint cone (forcedWalk G hG t)) n := by
  constructor
  · rintro ⟨n, p, hp⟩
    have heq := finite_path_eq_forced_prefix G hG t p n hp.finitePath
      hp.initial0 hp.initial1 hp.initial2
    refine ⟨n, legal_endpoint_of_prefix_eq cone p _ n heq hp.endpoint, ?_⟩
    intro i hi j hj hij
    apply hp.finitePath.injective i hi j hj
    exact (heq i hi).trans (hij.trans (heq j hj).symm)
  · rintro ⟨n, hn⟩
    exact ⟨n, forcedWalk G hG t,
      ⟨forced_prefix_is_finite_path G hG t n hn.2,
        rfl, rfl, rfl, hc, hb, hn.1⟩⟩

/-- The finite literal-path decision theorem, including the graph-to-sequence
bridge. No extension of a finite input path is assumed. -/
theorem finite_literal_path_decision [Fintype V] (G : SimpleGraph V)
    (hG : TwoCommonNeighbors G) (cone : V → Prop) (t : OrderedTriangle G)
    (hc : cone t.a) (hb : ¬ cone t.b) :
    ∃ r ≤ Fintype.card V, FirstRepeat (forcedWalk G hG t) r ∧
      ((∃ n p, LiteralPathFrom G cone t p n) ↔
        ∃ e < r, LegalConeEndpoint cone (forcedWalk G hG t) e) := by
  obtain ⟨r, hr, hfirst, hdecision⟩ := finite_forced_walk_decision G hG t
    (LegalConeEndpoint cone (forcedWalk G hG t))
  exact ⟨r, hr, hfirst,
    (literal_path_iff_valid_forced_prefix G hG cone t hc hb).trans hdecision⟩

#print axioms finite_path_eq_forced_prefix
#print axioms literal_path_iff_valid_forced_prefix
#print axioms finite_literal_path_decision

end R002
