import Formal.Claude2K3Vertex

/-!
# K3 aligned surface: a vertex invariant that separates the points of every cell

Written by a Claude worker (2026-10-19, K3 necessity session).

`inv = (hgt, ang mod 6r)` (`Claude2K3Inv.lean`) collapses the middle cap triangles (cells `3`, `7`)
onto their boundary.  Here a third component `aux` records the `x`-coordinate of a point strictly
inside cell `3` or `7` (and is `0` elsewhere).

* `samePoint_aux`, `vtx_inv3` : `inv3 = (inv, aux)` is constant on every vertex;
* `inv3_inj_cell`             : inside one cell, `inv3` is injective (so distinct lattice points of
                                one cell are distinct vertices, `V_ne_cell`);
* `V_adj_cell`                : distinct unit-adjacent points of one cell are adjacent vertices;
* `rotN_add_pt`, `cross_rotN`  : lattice rotations are linear and preserve the cross product.
-/

namespace Claude2K3

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

/-- `x`-coordinate of a point strictly inside a middle cap triangle (cell `3` or `7`), else `0`. -/
def aux (r : ℤ) (f : Fin 11) (z : ℤ × ℤ) : ℤ :=
  if (f.val = 3 ∨ f.val = 7) ∧ 0 < z.2 ∧ 0 < z.1 ∧ z.1 + z.2 < r then z.1 else 0

/-- The refined invariant. -/
def inv3 (r s : ℤ) (p : Fin 11 × (ℤ × ℤ)) : (ℤ × ℤ) × ℤ := (inv r s p, aux r p.1 p.2)

set_option maxHeartbeats 0 in
theorem samePoint_aux_aux (hr : 0 < r) (hs : 0 < s) (g f : Fin 11) (z w : ℤ × ℤ)
    (hz : CellIn r s g z) (hw : CellIn r s f w) (i j m : ℕ) (τ : ℤ × ℤ)
    (hG : (k3Sig r s).Glue g i f j m τ) (hzw : rotN m z + τ = w) :
    aux r g z = aux r f w := by
  obtain ⟨hi, hj, h1, h2, h3, h4⟩ := hG
  rw [k3Sig_lb, k3Sig_lb] at h1 h2
  have hlg : ((k3Sig r s).poly g).length ≤ 6 := by
    rw [show (k3Sig r s).poly g = k3Poly r s g from rfl, k3_poly_length]
    fin_cases g <;> decide
  have hlf : ((k3Sig r s).poly f).length ≤ 6 := by
    rw [show (k3Sig r s).poly f = k3Poly r s f from rfl, k3_poly_length]
    fin_cases f <;> decide
  have hi' : i < (k3Lab g).length := by
    rw [← k3_poly_length r s g]; exact hi
  have hj' : j < (k3Lab f).length := by
    rw [← k3_poly_length r s f]; exact hj
  have hm := k3_pairs g ⟨i, by omega⟩ f ⟨j, by omega⟩ hi' hj' h1 h2
  simp only [k3GlueTable, List.map_cons, List.map_nil, List.mem_cons, Prod.mk.injEq,
    List.not_mem_nil, or_false] at hm
  rw [rotN_mod6] at h3 h4 hzw
  have hm6 : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize m % 6 = k at h3 h4 hzw hm6
  rcases hm with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
  · interval_cases k <;>
    · simp only [rotN, rot, Sig.pt, k3Sig, k3Poly, walk, Prod.ext_iff] at h3 h4 hzw
      simp [CellIn, TriIn, HexIn] at hz hw
      simp only [aux, Fin.isValue]
      norm_num at h3 h4 hzw ⊢
      all_goals omega

theorem samePoint_inv3 (hr : 0 < r) (hs : 0 < s) (a b : (k3Sig r s).Site)
    (h : (k3Sig r s).SamePoint a b) : inv3 r s a.1 = inv3 r s b.1 := by
  have e1 := samePoint_inv hr hs a b h
  obtain ⟨⟨g, z⟩, hz⟩ := a
  obtain ⟨⟨f, w⟩, hw⟩ := b
  obtain ⟨i, j, m, τ, hG, hzw⟩ := h
  have e2 := samePoint_aux_aux hr hs g f z w ((inCell_iff hr hs g z).1 hz)
    ((inCell_iff hr hs f w).1 hw) i j m τ hG hzw
  simp only [inv3] at e1 ⊢
  rw [e1, e2]

theorem inv3_of_eqvGen (hr : 0 < r) (hs : 0 < s) {a b : (k3Sig r s).Site}
    (h : Relation.EqvGen (k3Sig r s).SamePoint a b) : inv3 r s a.1 = inv3 r s b.1 := by
  induction h with
  | rel x y hxy => exact samePoint_inv3 hr hs x y hxy
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- The refined invariant of a vertex. -/
def vinv3 (hr : 0 < r) (hs : 0 < s) : (k3Sig r s).Vertex → (ℤ × ℤ) × ℤ :=
  Quot.lift (fun a => inv3 r s a.1) (fun _ _ h => inv3_of_eqvGen hr hs h)

theorem vtx_inv3 (hr : 0 < r) (hs : 0 < s) {a b : (k3Sig r s).Site}
    (h : (k3Sig r s).vtx a = (k3Sig r s).vtx b) : inv3 r s a.1 = inv3 r s b.1 :=
  congrArg (vinv3 hr hs) h

theorem V_inv3 (hr : 0 < r) (hs : 0 < s) {f g : Fin 11} {z w : ℤ × ℤ}
    (hz : CellIn r s f z) (hw : CellIn r s g w) (h : V r s f z = V r s g w) :
    inv3 r s (f, z) = inv3 r s (g, w) := by
  have hz' := (inCell_iff hr hs f z).2 hz
  have hw' := (inCell_iff hr hs g w).2 hw
  rw [V_eq hz', V_eq hw'] at h
  exact vtx_inv3 hr hs h

theorem V_ne3 (hr : 0 < r) (hs : 0 < s) {f g : Fin 11} {z w : ℤ × ℤ}
    (hz : CellIn r s f z) (hw : CellIn r s g w) (h : inv3 r s (f, z) ≠ inv3 r s (g, w)) :
    V r s f z ≠ V r s g w := fun e => h (V_inv3 hr hs hz hw e)

theorem vinv3_V (hr : 0 < r) (hs : 0 < s) {f : Fin 11} {z : ℤ × ℤ} (hz : CellIn r s f z) :
    vinv3 hr hs (V r s f z) = inv3 r s (f, z) := by
  rw [V_eq ((inCell_iff hr hs f z).2 hz)]; rfl

set_option maxHeartbeats 4000000 in
/-- Inside one cell the refined invariant is injective. -/
theorem inv3_inj_cell (hr : 0 < r) (hs : 0 < s) {c : Fin 11} {z w : ℤ × ℤ}
    (hz : CellIn r s c z) (hw : CellIn r s c w) (h : inv3 r s (c, z) = inv3 r s (c, w)) :
    z = w := by
  obtain ⟨x, y⟩ := z
  obtain ⟨x', y'⟩ := w
  fin_cases c <;>
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, Prod.ext_iff] at hz hw h ⊢ <;>
  split_ifs at h <;> omega

theorem V_ne_cell (hr : 0 < r) (hs : 0 < s) {c : Fin 11} {z w : ℤ × ℤ}
    (hz : CellIn r s c z) (hw : CellIn r s c w) (h : z ≠ w) : V r s c z ≠ V r s c w :=
  V_ne3 hr hs hz hw (fun e => h (inv3_inj_cell hr hs hz hw e))

/-- Distinct unit-adjacent lattice points of one cell are adjacent vertices. -/
theorem V_adj_cell (hr : 0 < r) (hs : 0 < s) {c : Fin 11} {z w : ℤ × ℤ}
    (hz : CellIn r s c z) (hw : CellIn r s c w) (hu : w - z ∈ unitVec) :
    (k3Graph r s).Adj (V r s c z) (V r s c w) := by
  have hne : z ≠ w := by
    rintro rfl; simp [unitVec, Prod.ext_iff] at hu
  have hz' := (inCell_iff hr hs c z).2 hz
  have hw' := (inCell_iff hr hs c w).2 hw
  refine ⟨V_ne_cell hr hs hz hw hne, ⟨(c, z), hz'⟩, ⟨(c, w), hw'⟩, (V_eq hz').symm,
    (V_eq hw').symm, Or.inl ⟨rfl, hu⟩⟩

/-! ## Lattice rotations -/

theorem rot_add (z w : ℤ × ℤ) : rot (z + w) = rot z + rot w := by
  ext <;> simp [rot] <;> ring

theorem rotN_add_pt (m : ℕ) (z w : ℤ × ℤ) : rotN m (z + w) = rotN m z + rotN m w := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [rotN, ih, rot_add]

theorem rotN_zero_pt (m : ℕ) : rotN m (0 : ℤ × ℤ) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [rotN, ih, rot]

theorem rotN_neg_pt (m : ℕ) (z : ℤ × ℤ) : rotN m (-z) = -rotN m z := by
  have h := rotN_add_pt m z (-z)
  rw [add_neg_cancel, rotN_zero_pt] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem rotN_sub_pt (m : ℕ) (z w : ℤ × ℤ) : rotN m (z - w) = rotN m z - rotN m w := by
  rw [sub_eq_add_neg, rotN_add_pt, rotN_neg_pt, ← sub_eq_add_neg]

theorem cross_rot (d z : ℤ × ℤ) : cross (rot d) (rot z) = cross d z := by
  simp [cross, rot]; ring

theorem cross_rotN (m : ℕ) (d z : ℤ × ℤ) : cross (rotN m d) (rotN m z) = cross d z := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [rotN, cross_rot, ih]

theorem rotN_unit (m : ℕ) {u : ℤ × ℤ} (hu : u ∈ unitVec) : rotN m u ∈ unitVec := by
  induction m with
  | zero => exact hu
  | succ m ih =>
    simp only [rotN]
    simp [unitVec] at ih ⊢
    rcases ih with h | h | h | h | h | h <;> rw [h] <;> simp [rot]

/-- Every unit vector is a rotation image of a unit vector. -/
theorem rotN_unit_surj (m : ℕ) {u : ℤ × ℤ} (hu : u ∈ unitVec) :
    ∃ u0 ∈ unitVec, rotN m u0 = u := by
  refine ⟨rotN (6 * (m + 1) - m) u, rotN_unit _ hu, ?_⟩
  rw [← rotN_add', show m + (6 * (m + 1) - m) = 6 * (m + 1) by omega, rotN_six_mul']

/-- The six unit vectors, listed from any one of them. -/
theorem unit_cases {d u : ℤ × ℤ} (hd : d ∈ unitVec) (hu : u ∈ unitVec) :
    u = d ∨ u = rot d ∨ u = rot (rot d) ∨ u = -d ∨ u = -rot d ∨ u = -rot (rot d) := by
  simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hd hu
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rot]

end Claude2K3

#print axioms Claude2K3.vtx_inv3
#print axioms Claude2K3.inv3_inj_cell
