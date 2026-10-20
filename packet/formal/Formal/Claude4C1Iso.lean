import Formal.Claude4C1Phi3

/-!
# C1: `c1Graph r s` is isomorphic to the `ℤ⁴` model `G4 r s`

Written by a Claude worker (2026-10-20, C1 bridge session).

* `vphi`          : the vertex map (well defined by `samePoint_phi`);
* `vphi_bijective`: injective by `eqv_of_phi`, surjective by the inverse charts `psi`;
* `adj_iff`       : adjacency corresponds (a unit step in a cell is a root `e_i - e_j` in the
                    face of that cell, and conversely);
* `c1_iff_g4`     : a literal path exists in `c1Graph r s` iff one exists in `G4 r s`
                    (`0 < r`, `0 < s`).
-/

set_option linter.unusedVariables false

namespace Claude4C1

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

theorem phi_of_eqvGen (hr : 0 < r) (hs : 0 < s) {a b : (c1Sig r s).Site}
    (h : Relation.EqvGen (c1Sig r s).SamePoint a b) : phi r s a.1.1 a.1.2 = phi r s b.1.1 b.1.2 := by
  induction h with
  | rel x y hxy => exact samePoint_phi hr hs x y hxy
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- The model point of a site. -/
def siteS (hr : 0 < r) (hs : 0 < s) (a : (c1Sig r s).Site) : Surf r s :=
  ⟨phi r s a.1.1 a.1.2, phi_inS hr hs ((inCell_iff hr hs _ _).1 a.2)⟩

/-- The model point of a vertex. -/
def vphi (hr : 0 < r) (hs : 0 < s) : (c1Sig r s).Vertex → Surf r s :=
  Quot.lift (siteS hr hs) (fun _ _ h => Subtype.ext (phi_of_eqvGen hr hs h))

theorem vphi_vtx (hr : 0 < r) (hs : 0 < s) (a : (c1Sig r s).Site) :
    (vphi hr hs ((c1Sig r s).vtx a)).1 = phi r s a.1.1 a.1.2 := rfl

theorem vphi_injective (hr : 0 < r) (hs : 0 < s) : Function.Injective (vphi hr hs) := by
  intro v w h
  induction v using Quot.ind
  induction w using Quot.ind
  exact Quot.sound (eqv_of_phi hr hs _ _ (congrArg Subtype.val h))

/-- The cell of the face `x_k = 0` (`top = false`) or `x_k = r + s` (`top = true`). -/
def cellOf (k : Fin 4) (top : Bool) : Fin 8 := if top then ![4, 5, 6, 7] k else ![3, 2, 1, 0] k

theorem faceK_cellOf : ∀ (k : Fin 4) (top : Bool), faceK (cellOf k top) = k := by decide

theorem exists_cell {x : Fin 4 → ℤ} {k : Fin 4} (hk : x k = 0 ∨ x k = r + s) :
    ∃ f, faceK f = k ∧ x (faceK f) = faceV r s f := by
  rcases hk with hk | hk
  · refine ⟨cellOf k false, faceK_cellOf k false, ?_⟩
    rw [faceK_cellOf, hk]
    have : (cellOf k false).val < 4 := by fin_cases k <;> decide
    simp [faceV, this]
  · refine ⟨cellOf k true, faceK_cellOf k true, ?_⟩
    rw [faceK_cellOf, hk]
    have : ¬ (cellOf k true).val < 4 := by fin_cases k <;> decide
    simp [faceV, this]

theorem vphi_surjective (hr : 0 < r) (hs : 0 < s) : Function.Surjective (vphi hr hs) := by
  intro x
  obtain ⟨k, hk⟩ := x.2.2.2
  obtain ⟨f, -, hf⟩ := exists_cell hk
  obtain ⟨hc, he⟩ := psi_spec f x.2 hf
  exact ⟨(c1Sig r s).vtx ⟨(f, psi r f x.1), (inCell_iff hr hs _ _).2 hc⟩, Subtype.ext he⟩

/-! ## Adjacency -/

theorem phi_add (f : Fin 8) (z u : ℤ × ℤ) :
    phi r s f (z + u) = phi r s f z + (phi 0 0 f u - phi 0 0 f (0, 0)) := by
  funext t
  fin_cases f <;> fin_cases t <;> simp [phi] <;> ring

theorem phi_unit : ∀ f : Fin 8, ∀ u ∈ unitVec, ∃ i j : Fin 4, i ≠ j ∧ faceK f ≠ i ∧
    faceK f ≠ j ∧ ∀ t, (phi 0 0 f u - phi 0 0 f (0, 0)) t = rt i j t := by
  decide

theorem psi_add (f : Fin 8) (x v : Fin 4 → ℤ) : psi r f (x + v) = psi r f x + psi 0 f v := by
  fin_cases f <;> simp [psi] <;> ring_nf

theorem psi_unit : ∀ f : Fin 8, ∀ i j : Fin 4, i ≠ j → faceK f ≠ i → faceK f ≠ j →
    psi 0 f (rt i j) ∈ unitVec := by
  decide

theorem unit_adj (g : Fin 8) (z w : ℤ × ℤ) (h2 : w - z ∈ unitVec) :
    AdjR r s (phi r s g z) (phi r s g w) := by
  obtain ⟨i, j, hij, hfi, hfj, ht⟩ := phi_unit g _ h2
  refine ⟨i, j, hij, ?_, faceK g, hfi, hfj, ?_⟩
  · rw [show w = z + (w - z) by simp, phi_add]
    funext t; simp [ht]
  · rw [phi_face]; exact faceV_mem g

theorem step_adj (hr : 0 < r) (hs : 0 < s) (a b : (c1Sig r s).Site) (h1 : b.1.1 = a.1.1)
    (h2 : b.1.2 - a.1.2 ∈ unitVec) : AdjR r s (phi r s a.1.1 a.1.2) (phi r s b.1.1 b.1.2) := by
  obtain ⟨⟨f, z⟩, ha⟩ := a
  obtain ⟨⟨g, w⟩, hb⟩ := b
  simp only at h1 h2 ⊢
  subst h1
  exact unit_adj g z w h2

theorem adj_fwd (hr : 0 < r) (hs : 0 < s) {v w : (c1Sig r s).Vertex}
    (h : (c1Graph r s).Adj v w) : (G4 r s).Adj (vphi hr hs v) (vphi hr hs w) := by
  obtain ⟨-, a, b, rfl, rfl, hab⟩ := h
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact step_adj hr hs a b h1 h2
  · exact adjR_symm (step_adj hr hs b a h1 h2)

theorem adj_bwd (hr : 0 < r) (hs : 0 < s) {v w : (c1Sig r s).Vertex}
    (h : (G4 r s).Adj (vphi hr hs v) (vphi hr hs w)) : (c1Graph r s).Adj v w := by
  refine ⟨fun e => adjR_ne h (by rw [e]), ?_⟩
  obtain ⟨i, j, hij, hy, k, hki, hkj, hk⟩ := h
  obtain ⟨f, hfk, hf⟩ := exists_cell hk
  subst hfk
  set x := vphi hr hs v
  set y := vphi hr hs w
  have hyf : y.1 (faceK f) = faceV r s f := by rw [hy, add_rt_ne _ hki hkj]; exact hf
  obtain ⟨hcx, hex⟩ := psi_spec f x.2 hf
  obtain ⟨hcy, hey⟩ := psi_spec f y.2 hyf
  let a : (c1Sig r s).Site := ⟨(f, psi r f x.1), (inCell_iff hr hs _ _).2 hcx⟩
  let b : (c1Sig r s).Site := ⟨(f, psi r f y.1), (inCell_iff hr hs _ _).2 hcy⟩
  refine ⟨a, b, vphi_injective hr hs (Subtype.ext hex), vphi_injective hr hs (Subtype.ext hey),
    Or.inl ⟨rfl, ?_⟩⟩
  show psi r f y.1 - psi r f x.1 ∈ unitVec
  rw [hy, psi_add, add_sub_cancel_left]
  exact psi_unit f i j hij hki hkj

/-- The vertex bijection. -/
noncomputable def vEquiv (hr : 0 < r) (hs : 0 < s) : (c1Sig r s).Vertex ≃ Surf r s :=
  Equiv.ofBijective (vphi hr hs) ⟨vphi_injective hr hs, vphi_surjective hr hs⟩

theorem adj_iff (hr : 0 < r) (hs : 0 < s) (v w : (c1Sig r s).Vertex) :
    (c1Graph r s).Adj v w ↔ (G4 r s).Adj (vEquiv hr hs v) (vEquiv hr hs w) :=
  ⟨adj_fwd hr hs, adj_bwd hr hs⟩

/-- **Transfer**: literal paths in C1(r,s) correspond to literal paths in the `ℤ⁴` model. -/
theorem c1_iff_g4 (hr : 0 < r) (hs : 0 < s) :
    (∃ n p, LiteralPath (c1Graph r s) n p) ↔ (∃ n q, LiteralPath (G4 r s) n q) :=
  exists_literal_iff (vEquiv hr hs) (adj_iff hr hs)

end Claude4C1
