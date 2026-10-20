import Formal.Claude4C1Spec
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Fin

/-!
# C1 as the surface of a truncated simplex in `ℤ⁴`

Written by a Claude worker (2026-10-20, C1 bridge session).

C1(r,s) is the surface of the truncated tetrahedron.  Put the tetrahedron as the simplex
`{x ∈ ℤ⁴ : x ≥ 0, Σ x = 2r + s}` and cut every vertex `a` at `x_a = r + s`.  The faces are the
hexagons `x_d = 0` (sides `s, r, …`) and the triangles `x_a = r + s` (side `r`); the corner with
label `4a + b` is `x_a = r + s, x_b = r`.  This file defines that model:

* `InS r s x`  : `x` is a lattice point of the surface;
* `AdjR r s x y` : `y = x + e_i - e_j` and some third coordinate `k ∉ {i, j}` has `x_k ∈ {0, r+s}`
                   (both points lie in the face `k`);
* `G4 r s`     : the graph on `Surf r s`;
* `pm σ`       : a permutation of the coordinates is an automorphism (`pmE`, `adjR_pm`);
* `deg_of_equiv`, `exists_literal_iff` : degrees and literal paths move along a bijection that
                   preserves adjacency.

`Claude4C1Phi*.lean` shows that `c1Graph r s` is isomorphic to `G4 r s`.
-/

namespace Claude4C1

open ClaudeChallenge Claude2Aligned

/-- The root `e_i - e_j`. -/
def rt (i j : Fin 4) : Fin 4 → ℤ := fun k => (if k = i then 1 else 0) - (if k = j then 1 else 0)

/-- Lattice points of the truncated simplex surface. -/
def InS (r s : ℤ) (x : Fin 4 → ℤ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ r + s) ∧ ∑ i, x i = 2 * r + s ∧ ∃ k, x k = 0 ∨ x k = r + s

abbrev Surf (r s : ℤ) : Type := {x : Fin 4 → ℤ // InS r s x}

/-- Adjacency in the model. -/
def AdjR (r s : ℤ) (x y : Fin 4 → ℤ) : Prop :=
  ∃ i j, i ≠ j ∧ y = x + rt i j ∧ ∃ k, k ≠ i ∧ k ≠ j ∧ (x k = 0 ∨ x k = r + s)

variable {r s : ℤ}

theorem inS_iff {x : Fin 4 → ℤ} : InS r s x ↔
    (0 ≤ x 0 ∧ x 0 ≤ r + s) ∧ (0 ≤ x 1 ∧ x 1 ≤ r + s) ∧ (0 ≤ x 2 ∧ x 2 ≤ r + s) ∧
    (0 ≤ x 3 ∧ x 3 ≤ r + s) ∧ x 0 + x 1 + x 2 + x 3 = 2 * r + s ∧
    (x 0 = 0 ∨ x 0 = r + s ∨ x 1 = 0 ∨ x 1 = r + s ∨ x 2 = 0 ∨ x 2 = r + s ∨ x 3 = 0 ∨
      x 3 = r + s) := by
  constructor
  · rintro ⟨h1, h2, k, hk⟩
    rw [Fin.sum_univ_four] at h2
    refine ⟨h1 0, h1 1, h1 2, h1 3, h2, ?_⟩
    fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hk <;> tauto
  · rintro ⟨h0, h1, h2, h3, hs, hk⟩
    refine ⟨fun i => by fin_cases i <;> assumption, by rw [Fin.sum_univ_four]; exact hs, ?_⟩
    rcases hk with h | h | h | h | h | h | h | h
    exacts [⟨0, Or.inl h⟩, ⟨0, Or.inr h⟩, ⟨1, Or.inl h⟩, ⟨1, Or.inr h⟩, ⟨2, Or.inl h⟩,
      ⟨2, Or.inr h⟩, ⟨3, Or.inl h⟩, ⟨3, Or.inr h⟩]

theorem rt_ne {i j k : Fin 4} (hi : k ≠ i) (hj : k ≠ j) : rt i j k = 0 := by
  simp [rt, hi, hj]

theorem rt_left {i j : Fin 4} (h : i ≠ j) : rt i j i = 1 := by simp [rt, h]

theorem rt_right {i j : Fin 4} (h : i ≠ j) : rt i j j = -1 := by simp [rt, h.symm]

theorem add_rt_left (x : Fin 4 → ℤ) {i j : Fin 4} (h : i ≠ j) : (x + rt i j) i = x i + 1 := by
  simp [rt_left h]

theorem add_rt_right (x : Fin 4 → ℤ) {i j : Fin 4} (h : i ≠ j) : (x + rt i j) j = x j - 1 := by
  simp [rt_right h]; omega

theorem add_rt_ne (x : Fin 4 → ℤ) {i j k : Fin 4} (hi : k ≠ i) (hj : k ≠ j) :
    (x + rt i j) k = x k := by simp [rt_ne hi hj]

theorem adjR_symm {x y : Fin 4 → ℤ} (h : AdjR r s x y) : AdjR r s y x := by
  obtain ⟨i, j, hij, rfl, k, hki, hkj, hk⟩ := h
  refine ⟨j, i, hij.symm, ?_, k, hkj, hki, ?_⟩
  · funext t
    simp only [Pi.add_apply, rt]
    split_ifs <;> omega
  · rw [add_rt_ne x hki hkj]; exact hk

theorem adjR_ne {x y : Fin 4 → ℤ} (h : AdjR r s x y) : x ≠ y := by
  obtain ⟨i, j, hij, rfl, -⟩ := h
  intro h
  have := congrFun h i
  rw [add_rt_left x hij] at this
  omega

/-- The model graph. -/
def G4 (r s : ℤ) : SimpleGraph (Surf r s) where
  Adj x y := AdjR r s x.1 y.1
  symm := ⟨fun _ _ h => adjR_symm h⟩
  loopless := ⟨fun _ h => adjR_ne h rfl⟩

theorem g4_adj {x y : Surf r s} : (G4 r s).Adj x y ↔ AdjR r s x.1 y.1 := Iff.rfl

/-! ## Coordinate permutations -/

/-- Reindexing by a permutation. -/
def pm (σ : Equiv.Perm (Fin 4)) (x : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => x (σ i)

theorem pm_pm_symm (σ : Equiv.Perm (Fin 4)) (x : Fin 4 → ℤ) : pm σ (pm σ.symm x) = x := by
  funext i; simp [pm]

theorem pm_symm_pm (σ : Equiv.Perm (Fin 4)) (x : Fin 4 → ℤ) : pm σ.symm (pm σ x) = x := by
  funext i; simp [pm]

theorem inS_pm_of (σ : Equiv.Perm (Fin 4)) {x : Fin 4 → ℤ} (h : InS r s x) : InS r s (pm σ x) := by
  obtain ⟨h1, h2, k, hk⟩ := h
  refine ⟨fun i => h1 (σ i), ?_, σ.symm k, by simpa [pm] using hk⟩
  rw [← h2]; exact Equiv.sum_comp σ x

theorem rt_comp (σ : Equiv.Perm (Fin 4)) (i j t : Fin 4) :
    rt i j (σ t) = rt (σ.symm i) (σ.symm j) t := by
  simp only [rt, Equiv.apply_eq_iff_eq_symm_apply]

theorem adjR_pm_of (σ : Equiv.Perm (Fin 4)) {x y : Fin 4 → ℤ} (h : AdjR r s x y) :
    AdjR r s (pm σ x) (pm σ y) := by
  obtain ⟨i, j, hij, rfl, k, hki, hkj, hk⟩ := h
  refine ⟨σ.symm i, σ.symm j, fun e => hij (σ.symm.injective e), ?_, σ.symm k,
    fun e => hki (σ.symm.injective e), fun e => hkj (σ.symm.injective e), by simpa [pm] using hk⟩
  funext t
  simp only [pm, Pi.add_apply, rt_comp]

theorem adjR_pm (σ : Equiv.Perm (Fin 4)) {x y : Fin 4 → ℤ} :
    AdjR r s (pm σ x) (pm σ y) ↔ AdjR r s x y := by
  refine ⟨fun h => ?_, adjR_pm_of σ⟩
  have := adjR_pm_of σ.symm h
  rwa [pm_symm_pm, pm_symm_pm] at this

/-- The automorphism of `G4` given by a coordinate permutation. -/
def pmE (σ : Equiv.Perm (Fin 4)) : Surf r s ≃ Surf r s where
  toFun x := ⟨pm σ x.1, inS_pm_of σ x.2⟩
  invFun x := ⟨pm σ.symm x.1, inS_pm_of σ.symm x.2⟩
  left_inv x := Subtype.ext (pm_symm_pm σ x.1)
  right_inv x := Subtype.ext (pm_pm_symm σ x.1)

theorem pmE_adj (σ : Equiv.Perm (Fin 4)) (x y : Surf r s) :
    (G4 r s).Adj x y ↔ (G4 r s).Adj (pmE σ x) (pmE σ y) := (adjR_pm σ).symm

/-! ## Transport along adjacency-preserving bijections -/

theorem deg_of_equiv {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} (e : V ≃ W)
    (he : ∀ v w, G.Adj v w ↔ H.Adj (e v) (e w)) (v : V) : deg G v = deg H (e v) := by
  unfold deg
  have : H.neighborSet (e v) = e '' G.neighborSet v := by
    ext w
    constructor
    · intro hw
      refine ⟨e.symm w, ?_, by simp⟩
      rw [SimpleGraph.mem_neighborSet, he]; simpa using hw
    · rintro ⟨u, hu, rfl⟩
      exact (he v u).1 hu
  rw [this, Set.ncard_image_of_injective _ e.injective]

theorem literal_of_equiv {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} (e : V ≃ W)
    (he : ∀ v w, G.Adj v w ↔ H.Adj (e v) (e w)) {n : ℕ} {p : ℕ → V}
    (h : LiteralPath G n p) : LiteralPath H n (fun i => e (p i)) := by
  obtain ⟨h4, hev, hinj, h1, h2, d0, d1, d2, d3⟩ := h
  refine ⟨h4, hev, fun i j hi hj hij => hinj i j hi hj (e.injective hij),
    fun i hi => (he _ _).1 (h1 i hi), fun i hi => (he _ _).1 (h2 i hi), ?_, ?_, ?_, ?_⟩ <;>
  · rwa [← deg_of_equiv e he]

theorem exists_literal_iff {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} (e : V ≃ W)
    (he : ∀ v w, G.Adj v w ↔ H.Adj (e v) (e w)) :
    (∃ n p, LiteralPath G n p) ↔ (∃ n q, LiteralPath H n q) := by
  constructor
  · rintro ⟨n, p, h⟩; exact ⟨n, _, literal_of_equiv e he h⟩
  · rintro ⟨n, q, h⟩
    refine ⟨n, _, literal_of_equiv e.symm (fun v w => ?_) h⟩
    rw [he]; simp

end Claude4C1
