import Formal.Claude3ChallengeSpec
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# Theorem 1a, geometric foundation (1): finiteness, unit vectors, adjacency, forced continuation

Written by a Claude worker (2026-10-20, Theorem 1a geometric session), against the
definitions of `Formal.Claude3ChallengeSpec` (namespace `ClaudeChallenge2`), unmodified.

* `instance : Finite (Site S t)`, `instance : Finite (Vertex S t)` : charts are bounded.
* `mem_unitVec_iff`, `neg_mem_unitVec`, `rotN_mem_unitVec`, `rotN_add`, `rotN_sub`,
  `rotN_injective` : the six unit vectors and the linear rotation `rotN`.
* `adj_of_unit` / `valid_adj_of_unit` : a unit step inside one chart is an edge (under `Valid`
  the endpoints are automatically distinct, by chart-embeddedness).
* `Next G a b c d` : `d` is a common neighbour of `b, c` other than `a`;
  `exists_unique_next` : under `TwoCommonNeighbors`, an oriented triangle `(a,b,c)` has a unique
  forced continuation.
* `IsForced G p N` : `p 0, …, p (N-1)` is a forced walk; `LiteralPath.isForced` : every literal
  path is one; `IsForced.unique` : a forced walk is determined by its first triangle.
-/

namespace ClaudeChallenge2.Geo

open ClaudeChallenge2

variable {S : Sig} {t : ℕ}

/-! ## Finiteness -/

theorem chart_mem_finite (c : Chart) (t : ℕ) : {z : ℤ × ℤ | c.Mem t z}.Finite := by
  refine ((Set.finite_Icc (c.lx.eval t) (c.ux.eval t)).prod
    (Set.finite_Icc (c.ly.eval t) (c.uy.eval t))).subset ?_
  rintro z ⟨h1, h2, h3, h4, -, -⟩
  exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

instance (c : Chart) (t : ℕ) : Finite {z : ℤ × ℤ // c.Mem t z} :=
  (chart_mem_finite c t).to_subtype

instance instFiniteSite : Finite (Site S t) := by
  refine Finite.of_injective
    (fun s : Site S t => (⟨s.1.1, ⟨s.1.2, s.2⟩⟩ : Σ f : Fin S.C, {z // (S.chart f).Mem t z})) ?_
  rintro ⟨⟨f, z⟩, h⟩ ⟨⟨f', z'⟩, h'⟩ e
  simp only [Sigma.mk.injEq] at e
  obtain ⟨rfl, e⟩ := e
  simp only [heq_eq_eq, Subtype.mk.injEq] at e
  subst e
  rfl

instance instFiniteVertex : Finite (Vertex S t) :=
  Finite.of_surjective (Quot.mk _) (fun v => Quot.exists_rep v)

/-! ## Unit vectors and rotations -/

theorem mem_unitVec_iff (u : ℤ × ℤ) :
    u ∈ unitVec ↔ u = (1, 0) ∨ u = (0, 1) ∨ u = (-1, 1) ∨ u = (-1, 0) ∨ u = (0, -1) ∨
      u = (1, -1) := by
  simp [unitVec]

theorem unitVec_ne_zero {u : ℤ × ℤ} (hu : u ∈ unitVec) : u ≠ 0 := by
  rw [mem_unitVec_iff] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem neg_mem_unitVec {u : ℤ × ℤ} (hu : u ∈ unitVec) : -u ∈ unitVec := by
  rw [mem_unitVec_iff] at hu ⊢
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sub_mem_unitVec_comm {z z' : ℤ × ℤ} (hu : z' - z ∈ unitVec) : z - z' ∈ unitVec := by
  simpa using neg_mem_unitVec hu

theorem rot_mem_unitVec {u : ℤ × ℤ} (hu : u ∈ unitVec) : rot u ∈ unitVec := by
  rw [mem_unitVec_iff] at hu ⊢
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rot]

theorem rotN_mem_unitVec (k : ℕ) {u : ℤ × ℤ} (hu : u ∈ unitVec) : rotN k u ∈ unitVec := by
  induction k with
  | zero => exact hu
  | succ k ih => exact rot_mem_unitVec ih

theorem rot_add (z w : ℤ × ℤ) : rot (z + w) = rot z + rot w := by
  simp only [rot, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

theorem rot_neg (z : ℤ × ℤ) : rot (-z) = -rot z := by
  ext <;> simp [rot, add_comm]

theorem rot_injective : Function.Injective rot := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ e
  simp only [rot, Prod.mk.injEq] at e
  ext <;> simp <;> omega

theorem rotN_add (k : ℕ) (z w : ℤ × ℤ) : rotN k (z + w) = rotN k z + rotN k w := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rotN, ih, rot_add]

theorem rotN_neg (k : ℕ) (z : ℤ × ℤ) : rotN k (-z) = -rotN k z := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rotN, ih, rot_neg]

theorem rotN_sub (k : ℕ) (z w : ℤ × ℤ) : rotN k (z - w) = rotN k z - rotN k w := by
  rw [sub_eq_add_neg, rotN_add, rotN_neg, ← sub_eq_add_neg]

theorem rotN_injective (k : ℕ) : Function.Injective (rotN k) := by
  induction k with
  | zero => exact fun _ _ h => h
  | succ k ih => exact fun _ _ h => ih (rot_injective h)

theorem rotN_six (z : ℤ × ℤ) : rotN 6 z = z := by
  obtain ⟨x, y⟩ := z
  simp only [rotN, rot, Prod.mk.injEq]
  constructor <;> ring_nf

/-! ## Points of a chart and adjacency -/

/-- The vertex of the lattice point `z` of chart `f`. -/
abbrev pt (S : Sig) (t : ℕ) (f : Fin S.C) (z : ℤ × ℤ) (h : (S.chart f).Mem t z) :
    Vertex S t :=
  vtx ⟨(f, z), h⟩

/-- A unit step inside one chart between distinct vertices is an edge. -/
theorem adj_of_unit {f : Fin S.C} {z z' : ℤ × ℤ} (h : (S.chart f).Mem t z)
    (h' : (S.chart f).Mem t z') (hu : z' - z ∈ unitVec) (hne : pt S t f z h ≠ pt S t f z' h') :
    (graph S t).Adj (pt S t f z h) (pt S t f z' h') :=
  ⟨hne, Or.inl ⟨_, _, rfl, rfl, rfl, z' - z, hu, by abel⟩⟩

/-- Chart-embeddedness, as a lemma. -/
theorem valid_pt_inj (hV : Valid S t) {f : Fin S.C} {z z' : ℤ × ℤ} (h : (S.chart f).Mem t z)
    (h' : (S.chart f).Mem t z') (e : pt S t f z h = pt S t f z' h') : z = z' :=
  hV.2.1 f z z' h h' e

theorem valid_pt_ne (hV : Valid S t) {f : Fin S.C} {z z' : ℤ × ℤ} (h : (S.chart f).Mem t z)
    (h' : (S.chart f).Mem t z') (hne : z ≠ z') : pt S t f z h ≠ pt S t f z' h' :=
  fun e => hne (valid_pt_inj hV h h' e)

/-- Under `Valid`, a unit step inside one chart is an edge. -/
theorem valid_adj_of_unit (hV : Valid S t) {f : Fin S.C} {z z' : ℤ × ℤ}
    (h : (S.chart f).Mem t z) (h' : (S.chart f).Mem t z') (hu : z' - z ∈ unitVec) :
    (graph S t).Adj (pt S t f z h) (pt S t f z' h') := by
  refine adj_of_unit h h' hu (valid_pt_ne hV h h' ?_)
  intro e
  exact unitVec_ne_zero hu (by rw [e, sub_self])

/-- Conversely, an edge has representatives in one chart differing by a unit vector. -/
theorem exists_unit_of_adj {v w : Vertex S t} (h : (graph S t).Adj v w) :
    ∃ s s' : Site S t, s.1.1 = s'.1.1 ∧ s'.1.2 - s.1.2 ∈ unitVec ∧
      ((vtx s = v ∧ vtx s' = w) ∨ (vtx s = w ∧ vtx s' = v)) := by
  rcases h.2 with ⟨s, s', hs, hs', hf, u, hu, e⟩ | ⟨s, s', hs, hs', hf, u, hu, e⟩
  · exact ⟨s, s', hf, by rw [e]; simpa using hu, Or.inl ⟨hs, hs'⟩⟩
  · exact ⟨s, s', hf, by rw [e]; simpa using hu, Or.inr ⟨hs, hs'⟩⟩

/-! ## Forced continuation -/

section Forced

variable {V : Type} (G : SimpleGraph V)

/-- `d` continues the oriented triangle `(a, b, c)`: a common neighbour of `b, c` other than
`a`. -/
def Next (a b c d : V) : Prop := d ≠ a ∧ G.Adj b d ∧ G.Adj c d

/-- `p 0, …, p (N-1)` is a forced walk: each vertex from the fourth on continues the triangle
of its three predecessors. -/
def IsForced (p : ℕ → V) (N : ℕ) : Prop :=
  ∀ k, k + 3 < N → Next G (p k) (p (k + 1)) (p (k + 2)) (p (k + 3))

variable {G}

/-- Under `TwoCommonNeighbors`, the forced continuation of a triangle exists and is unique. -/
theorem exists_unique_next (hT : TwoCommonNeighbors G) {a b c : V} (hab : G.Adj a b)
    (hac : G.Adj a c) (hbc : G.Adj b c) : ∃! d, Next G a b c d := by
  obtain ⟨x, y, hxy, hiff⟩ := hT b c hbc
  have ha : a = x ∨ a = y := (hiff a).1 ⟨hab.symm, hac.symm⟩
  rcases ha with rfl | rfl
  · refine ⟨y, ⟨hxy.symm, (hiff y).2 (Or.inr rfl)⟩, ?_⟩
    rintro d ⟨hda, hd⟩
    exact ((hiff d).1 hd).resolve_left hda
  · refine ⟨x, ⟨hxy, (hiff x).2 (Or.inl rfl)⟩, ?_⟩
    rintro d ⟨hda, hd⟩
    exact ((hiff d).1 hd).resolve_right hda

/-- If the two common neighbours of an edge `b c` are exactly `a` and `d` (with `a ≠ d`), the
forced continuation of `(a, b, c)` is `d`. -/
theorem next_iff_of_common {a b c d : V} (had : a ≠ d)
    (hcom : ∀ v, (G.Adj b v ∧ G.Adj c v) ↔ (v = a ∨ v = d)) (e : V) :
    Next G a b c e ↔ e = d := by
  constructor
  · rintro ⟨hea, he⟩
    exact ((hcom e).1 he).resolve_left hea
  · rintro rfl
    exact ⟨had.symm, (hcom _).2 (Or.inr rfl)⟩

/-- Every literal path is a forced walk (no `TwoCommonNeighbors` needed). -/
theorem LiteralPath.isForced {n : ℕ} {p : ℕ → V} (hp : LiteralPath G n p) :
    IsForced G p n := by
  obtain ⟨-, -, hinj, h1, h2, -⟩ := hp
  intro k hk
  refine ⟨fun e => ?_, h2 (k + 1) (by omega), h1 (k + 2) (by omega)⟩
  have := hinj (k + 3) k (by omega) (by omega) e
  omega

/-- Consecutive vertices of a forced walk whose first triangle is a triangle are adjacent, and
so are vertices at distance two. -/
theorem IsForced.adj {p : ℕ → V} {N : ℕ} (hp : IsForced G p N) (h01 : G.Adj (p 0) (p 1))
    (h02 : G.Adj (p 0) (p 2)) (h12 : G.Adj (p 1) (p 2)) :
    ∀ k, k + 2 < N → G.Adj (p k) (p (k + 1)) ∧ G.Adj (p k) (p (k + 2)) ∧
      G.Adj (p (k + 1)) (p (k + 2)) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨h01, h02, h12⟩
  | succ k ih =>
    intro hk
    obtain ⟨-, -, h⟩ := ih (by omega)
    obtain ⟨-, hb, hc⟩ := hp k (by omega)
    exact ⟨h, hb, hc⟩

/-- A forced walk is determined by its first triangle. -/
theorem IsForced.unique (hT : TwoCommonNeighbors G) {p p' : ℕ → V} {N : ℕ}
    (hp : IsForced G p N) (hp' : IsForced G p' N) (h01 : G.Adj (p 0) (p 1))
    (h02 : G.Adj (p 0) (p 2)) (h12 : G.Adj (p 1) (p 2)) (e0 : p 0 = p' 0) (e1 : p 1 = p' 1)
    (e2 : p 2 = p' 2) : ∀ k, k < N → p k = p' k := by
  have hadj := hp.adj h01 h02 h12
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    match k, ih with
    | 0, _ => exact e0
    | 1, _ => exact e1
    | 2, _ => exact e2
    | m + 3, ih =>
      obtain ⟨ha, hb, hc⟩ := hadj m (by omega)
      have hu := exists_unique_next hT ha hb hc
      have q1 := hp m (by omega)
      have q2 := hp' m (by omega)
      rw [← ih m (by omega) (by omega), ← ih (m + 1) (by omega) (by omega),
        ← ih (m + 2) (by omega) (by omega)] at q2
      exact hu.unique q1 q2

end Forced

end ClaudeChallenge2.Geo
