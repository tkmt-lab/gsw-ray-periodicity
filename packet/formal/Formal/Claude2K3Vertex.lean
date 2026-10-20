import Formal.Claude2K3Inv

/-!
# K3 aligned surface, part 2: vertices, explicit gluings, a degree-counting lemma

Written by a Claude worker (2026-10-19).

* `vtx_inv`  : two sites of one vertex have the same invariant `inv` (from `samePoint_inv`);
* `V f z`    : the vertex of the lattice point `z` of cell `f` (a junk vertex if `z ∉ f`);
* `gl_g_i`   : the 42 gluings of K3 with their explicit translations;
* `deg_eq`   : the degree of a vertex `v` is the length of a duplicate-free list `L` of
               vertices, provided every site of `v` is listed in `C`, every unit step from a
               member of `C` lands at `v` or in `L`, and every member of `L` is adjacent to `v`.
-/

namespace Claude2K3

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

theorem inv_of_eqvGen (hr : 0 < r) (hs : 0 < s) {a b : (k3Sig r s).Site}
    (h : Relation.EqvGen (k3Sig r s).SamePoint a b) : inv r s a.1 = inv r s b.1 := by
  induction h with
  | rel x y hxy => exact samePoint_inv hr hs x y hxy
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- The invariant of a vertex. -/
def vinv (hr : 0 < r) (hs : 0 < s) : (k3Sig r s).Vertex → ℤ × ℤ :=
  Quot.lift (fun a => inv r s a.1) (fun _ _ h => inv_of_eqvGen hr hs h)

theorem vtx_inv (hr : 0 < r) (hs : 0 < s) {a b : (k3Sig r s).Site}
    (h : (k3Sig r s).vtx a = (k3Sig r s).vtx b) : inv r s a.1 = inv r s b.1 :=
  congrArg (vinv hr hs) h

theorem inCell_origin : (k3Sig r s).InCell (0 : Fin 11) (0, 0) := by
  intro i hi
  have hp : (k3Sig r s).poly (0 : Fin 11) = [(0, 0), (r, 0), (0, r)] := by
    simp [k3Sig, k3Poly, walk, rotN, rot]
  simp only [Sig.pt, hp] at hi ⊢
  simp at hi
  interval_cases i <;> simp [cross] <;> nlinarith [sq_nonneg r]

open Classical in
/-- The vertex of the lattice point `z` of cell `f`. -/
noncomputable def V (r s : ℤ) (f : Fin 11) (z : ℤ × ℤ) : (k3Sig r s).Vertex :=
  if h : (k3Sig r s).InCell f z then (k3Sig r s).vtx ⟨(f, z), h⟩
  else (k3Sig r s).vtx ⟨((0 : Fin 11), (0, 0)), inCell_origin⟩

theorem V_eq {f : Fin 11} {z : ℤ × ℤ} (h : (k3Sig r s).InCell f z) :
    V r s f z = (k3Sig r s).vtx ⟨(f, z), h⟩ := by
  simp [V, h]

theorem vtx_eq_V (a : (k3Sig r s).Site) : (k3Sig r s).vtx a = V r s a.1.1 a.1.2 := by
  obtain ⟨⟨f, z⟩, h⟩ := a
  exact (V_eq h).symm

theorem V_inv (hr : 0 < r) (hs : 0 < s) {f g : Fin 11} {z w : ℤ × ℤ}
    (hz : CellIn r s f z) (hw : CellIn r s g w) (h : V r s f z = V r s g w) :
    inv r s (f, z) = inv r s (g, w) := by
  have hz' := (inCell_iff hr hs f z).2 hz
  have hw' := (inCell_iff hr hs g w).2 hw
  rw [V_eq hz', V_eq hw'] at h
  exact vtx_inv hr hs h

theorem V_ne (hr : 0 < r) (hs : 0 < s) {f g : Fin 11} {z w : ℤ × ℤ}
    (hz : CellIn r s f z) (hw : CellIn r s g w) (h : inv r s (f, z) ≠ inv r s (g, w)) :
    V r s f z ≠ V r s g w := fun e => h (V_inv hr hs hz hw e)

theorem V_congr {f : Fin 11} {z w : ℤ × ℤ} (h : z = w) : V r s f z = V r s f w := by rw [h]

theorem V_glue (hr : 0 < r) (hs : 0 < s) {g f : Fin 11} {i j m : ℕ} {τ z w : ℤ × ℤ}
    (hG : (k3Sig r s).Glue g i f j m τ) (h : rotN m z + τ = w)
    (hz : CellIn r s g z) (hw : CellIn r s f w) : V r s g z = V r s f w := by
  have hz' := (inCell_iff hr hs g z).2 hz
  have hw' := (inCell_iff hr hs f w).2 hw
  rw [V_eq hz', V_eq hw']
  exact Quot.sound (Relation.EqvGen.rel _ _ ⟨i, j, m, τ, hG, h⟩)

macro "glue_tac" : tactic =>
  `(tactic| (refine ⟨by simp [k3Sig, k3Poly, walk], by simp [k3Sig, k3Poly, walk],
      by rw [k3Sig_lb, k3Sig_lb]; decide, by rw [k3Sig_lb, k3Sig_lb]; decide, ?_, ?_⟩ <;>
    simp [Sig.pt, k3Sig, k3Poly, walk, rotN, rot, Prod.ext_iff] <;> omega))

theorem gl_0_0 : (k3Sig r s).Glue (0 : Fin 11) 0 (8 : Fin 11) 1 4 (r, r) := by
  glue_tac

theorem gl_0_1 : (k3Sig r s).Glue (0 : Fin 11) 1 (3 : Fin 11) 2 5 (-r, r) := by
  glue_tac

theorem gl_0_2 : (k3Sig r s).Glue (0 : Fin 11) 2 (10 : Fin 11) 0 5 (0, 0) := by
  glue_tac

theorem gl_1_0 : (k3Sig r s).Glue (1 : Fin 11) 0 (9 : Fin 11) 1 4 (r, r) := by
  glue_tac

theorem gl_1_1 : (k3Sig r s).Glue (1 : Fin 11) 1 (3 : Fin 11) 0 1 (r, -r) := by
  glue_tac

theorem gl_1_2 : (k3Sig r s).Glue (1 : Fin 11) 2 (8 : Fin 11) 0 5 (0, 0) := by
  glue_tac

theorem gl_2_0 : (k3Sig r s).Glue (2 : Fin 11) 0 (10 : Fin 11) 1 4 (r, r) := by
  glue_tac

theorem gl_2_1 : (k3Sig r s).Glue (2 : Fin 11) 1 (3 : Fin 11) 1 3 (r, r) := by
  glue_tac

theorem gl_2_2 : (k3Sig r s).Glue (2 : Fin 11) 2 (9 : Fin 11) 0 5 (0, 0) := by
  glue_tac

theorem gl_3_0 : (k3Sig r s).Glue (3 : Fin 11) 0 (1 : Fin 11) 1 5 (0, r) := by
  glue_tac

theorem gl_3_1 : (k3Sig r s).Glue (3 : Fin 11) 1 (2 : Fin 11) 1 3 (r, r) := by
  glue_tac

theorem gl_3_2 : (k3Sig r s).Glue (3 : Fin 11) 2 (0 : Fin 11) 1 1 (r, 0) := by
  glue_tac

theorem gl_4_0 : (k3Sig r s).Glue (4 : Fin 11) 0 (7 : Fin 11) 2 1 (0, 0) := by
  glue_tac

theorem gl_4_1 : (k3Sig r s).Glue (4 : Fin 11) 1 (8 : Fin 11) 3 4 (-s, 2 * r + s) := by
  glue_tac

theorem gl_4_2 : (k3Sig r s).Glue (4 : Fin 11) 2 (10 : Fin 11) 4 3 (-s, r + s) := by
  glue_tac

theorem gl_5_0 : (k3Sig r s).Glue (5 : Fin 11) 0 (7 : Fin 11) 1 5 (0, r) := by
  glue_tac

theorem gl_5_1 : (k3Sig r s).Glue (5 : Fin 11) 1 (9 : Fin 11) 3 4 (-s, 2 * r + s) := by
  glue_tac

theorem gl_5_2 : (k3Sig r s).Glue (5 : Fin 11) 2 (8 : Fin 11) 4 3 (-s, r + s) := by
  glue_tac

theorem gl_6_0 : (k3Sig r s).Glue (6 : Fin 11) 0 (7 : Fin 11) 0 3 (r, 0) := by
  glue_tac

theorem gl_6_1 : (k3Sig r s).Glue (6 : Fin 11) 1 (10 : Fin 11) 3 4 (-s, 2 * r + s) := by
  glue_tac

theorem gl_6_2 : (k3Sig r s).Glue (6 : Fin 11) 2 (9 : Fin 11) 4 3 (-s, r + s) := by
  glue_tac

theorem gl_7_0 : (k3Sig r s).Glue (7 : Fin 11) 0 (6 : Fin 11) 0 3 (r, 0) := by
  glue_tac

theorem gl_7_1 : (k3Sig r s).Glue (7 : Fin 11) 1 (5 : Fin 11) 0 1 (r, -r) := by
  glue_tac

theorem gl_7_2 : (k3Sig r s).Glue (7 : Fin 11) 2 (4 : Fin 11) 0 5 (0, 0) := by
  glue_tac

theorem gl_8_0 : (k3Sig r s).Glue (8 : Fin 11) 0 (1 : Fin 11) 2 1 (0, 0) := by
  glue_tac

theorem gl_8_1 : (k3Sig r s).Glue (8 : Fin 11) 1 (0 : Fin 11) 0 2 (2 * r, -r) := by
  glue_tac

theorem gl_8_2 : (k3Sig r s).Glue (8 : Fin 11) 2 (10 : Fin 11) 5 0 (-r, -r) := by
  glue_tac

theorem gl_8_3 : (k3Sig r s).Glue (8 : Fin 11) 3 (4 : Fin 11) 1 2 (2 * r, s) := by
  glue_tac

theorem gl_8_4 : (k3Sig r s).Glue (8 : Fin 11) 4 (5 : Fin 11) 2 3 (-s, r + s) := by
  glue_tac

theorem gl_8_5 : (k3Sig r s).Glue (8 : Fin 11) 5 (9 : Fin 11) 2 0 (r, r) := by
  glue_tac

theorem gl_9_0 : (k3Sig r s).Glue (9 : Fin 11) 0 (2 : Fin 11) 2 1 (0, 0) := by
  glue_tac

theorem gl_9_1 : (k3Sig r s).Glue (9 : Fin 11) 1 (1 : Fin 11) 0 2 (2 * r, -r) := by
  glue_tac

theorem gl_9_2 : (k3Sig r s).Glue (9 : Fin 11) 2 (8 : Fin 11) 5 0 (-r, -r) := by
  glue_tac

theorem gl_9_3 : (k3Sig r s).Glue (9 : Fin 11) 3 (5 : Fin 11) 1 2 (2 * r, s) := by
  glue_tac

theorem gl_9_4 : (k3Sig r s).Glue (9 : Fin 11) 4 (6 : Fin 11) 2 3 (-s, r + s) := by
  glue_tac

theorem gl_9_5 : (k3Sig r s).Glue (9 : Fin 11) 5 (10 : Fin 11) 2 0 (r, r) := by
  glue_tac

theorem gl_10_0 : (k3Sig r s).Glue (10 : Fin 11) 0 (0 : Fin 11) 2 1 (0, 0) := by
  glue_tac

theorem gl_10_1 : (k3Sig r s).Glue (10 : Fin 11) 1 (2 : Fin 11) 0 2 (2 * r, -r) := by
  glue_tac

theorem gl_10_2 : (k3Sig r s).Glue (10 : Fin 11) 2 (9 : Fin 11) 5 0 (-r, -r) := by
  glue_tac

theorem gl_10_3 : (k3Sig r s).Glue (10 : Fin 11) 3 (6 : Fin 11) 1 2 (2 * r, s) := by
  glue_tac

theorem gl_10_4 : (k3Sig r s).Glue (10 : Fin 11) 4 (4 : Fin 11) 2 3 (-s, r + s) := by
  glue_tac

theorem gl_10_5 : (k3Sig r s).Glue (10 : Fin 11) 5 (8 : Fin 11) 2 0 (r, r) := by
  glue_tac

theorem unitVec_neg {u : ℤ × ℤ} (h : u ∈ unitVec) : -u ∈ unitVec := by
  simp [unitVec] at h ⊢
  rcases h with h | h | h | h | h | h <;> subst h <;> simp

/-- Adjacency of two lattice points of one cell at unit distance. -/
theorem V_adj (hr : 0 < r) (hs : 0 < s) {v : (k3Sig r s).Vertex} {f : Fin 11} {z w : ℤ × ℤ}
    (heq : v = V r s f z) (hz : CellIn r s f z) (hw : CellIn r s f w) (u : ℤ × ℤ)
    (hu : u ∈ unitVec) (hwz : w = z + u)
    (hne : inv r s (f, z) ≠ inv r s (f, w)) : (k3Graph r s).Adj v (V r s f w) := by
  have hz' := (inCell_iff hr hs f z).2 hz
  have hw' := (inCell_iff hr hs f w).2 hw
  subst heq
  refine ⟨V_ne hr hs hz hw hne, ⟨(f, z), hz'⟩, ⟨(f, w), hw'⟩, (V_eq hz').symm, (V_eq hw').symm,
    Or.inl ⟨rfl, ?_⟩⟩
  simp only [hwz, add_sub_cancel_left]; exact hu

theorem vinv_V (hr : 0 < r) (hs : 0 < s) {f : Fin 11} {z : ℤ × ℤ} (hz : CellIn r s f z) :
    vinv hr hs (V r s f z) = inv r s (f, z) := by
  rw [V_eq ((inCell_iff hr hs f z).2 hz)]; rfl

theorem nodup_V (hr : 0 < r) (hs : 0 < s) (P : List (Fin 11 × (ℤ × ℤ)))
    (hP : ∀ p ∈ P, CellIn r s p.1 p.2) (hinj : (P.map (inv r s)).Nodup) :
    (P.map (fun p => V r s p.1 p.2)).Nodup := by
  apply List.Nodup.of_map (vinv hr hs)
  rw [List.map_map]
  have : P.map (vinv hr hs ∘ fun p => V r s p.1 p.2) = P.map (inv r s) :=
    List.map_congr_left (fun p hp => by simp [Function.comp, vinv_V hr hs (hP p hp)])
  rw [this]; exact hinj

open Classical in
/-- Degree counting. -/
theorem deg_eq (hr : 0 < r) (hs : 0 < s) (v : (k3Sig r s).Vertex)
    (C : List (Fin 11 × (ℤ × ℤ))) (L : List (k3Sig r s).Vertex)
    (hC : ∀ (g : Fin 11) (w : ℤ × ℤ), CellIn r s g w → V r s g w = v → (g, w) ∈ C)
    (hstep : ∀ c ∈ C, ∀ u ∈ unitVec, CellIn r s c.1 (c.2 + u) →
      V r s c.1 (c.2 + u) = v ∨ V r s c.1 (c.2 + u) ∈ L)
    (hL : ∀ w ∈ L, (k3Graph r s).Adj v w) (hnd : L.Nodup) :
    deg (k3Graph r s) v = L.length := by
  have hset : (k3Graph r s).neighborSet v = (L.toFinset : Set (k3Sig r s).Vertex) := by
    ext w
    simp only [SimpleGraph.mem_neighborSet, List.coe_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hne, a, b, ha, hb, hst⟩
      obtain ⟨u, hu, hab1, hab2⟩ : ∃ u ∈ unitVec, b.1.1 = a.1.1 ∧ b.1.2 = a.1.2 + u := by
        rcases hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨_, h2, h1, by abel⟩
        · exact ⟨_, unitVec_neg h2, h1.symm, by rw [neg_sub]; abel⟩
      have hcell : CellIn r s a.1.1 (a.1.2 + u) := by
        rw [← hab1, ← hab2]; exact (inCell_iff hr hs _ _).1 b.2
      have ha' : (a.1.1, a.1.2) ∈ C :=
        hC a.1.1 a.1.2 ((inCell_iff hr hs _ _).1 a.2) (by rw [← ha, vtx_eq_V])
      have hbV : V r s a.1.1 (a.1.2 + u) = w := by rw [← hab1, ← hab2, ← vtx_eq_V, hb]
      rcases hstep _ ha' u hu hcell with h | h
      · exact absurd (hbV ▸ h).symm hne
      · rwa [hbV] at h
    · exact hL w
  rw [deg, hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

end Claude2K3
