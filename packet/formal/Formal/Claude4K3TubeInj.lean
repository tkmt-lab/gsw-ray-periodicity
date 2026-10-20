import Formal.Claude4K3CapInj

/-!
# K3 pieces: the tube coordinate, values and edges

Written by a Claude worker (2026-10-20, K3 bridge).

* `tube_inj`        : two tube sites with the same invariant `inv` are the same vertex;
* `val_top`, `val_bot`, `val_tube` : ranges of the coordinates on the three pieces
                      (the top cap lies below the top seam `h = -zz a`, the tube between the seams);
* `cap_edge`, `tube_edge` : a unit step inside a cell is a unit step of the cap position, resp. a
                      tube step `TA` of the invariant.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Claude4K3

open ClaudeChallenge Claude2Aligned Claude2K3

variable {r s : ℤ}

theorem ta_1 {t u : ℤ × ℤ} (h1 : u.1 = t.1 + 1) (h2 : AE r u.2 (t.2 + 1)) : TA r t u :=
  Or.inl ⟨h1, h2⟩
theorem ta_2 {t u : ℤ × ℤ} (h1 : u.1 = t.1 - 1) (h2 : AE r u.2 (t.2 - 1)) : TA r t u :=
  Or.inr (Or.inl ⟨h1, h2⟩)
theorem ta_3 {t u : ℤ × ℤ} (h1 : u.1 = t.1 + 1) (h2 : AE r u.2 (t.2 - 1)) : TA r t u :=
  Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
theorem ta_4 {t u : ℤ × ℤ} (h1 : u.1 = t.1 - 1) (h2 : AE r u.2 (t.2 + 1)) : TA r t u :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
theorem ta_5 {t u : ℤ × ℤ} (h1 : u.1 = t.1 + 2) (h2 : AE r u.2 t.2) : TA r t u :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))
theorem ta_6 {t u : ℤ × ℤ} (h1 : u.1 = t.1 - 2) (h2 : AE r u.2 t.2) : TA r t u :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))))

/-! ## Tube injectivity -/

macro "tglue_tac" : tactic =>
  `(tactic| (simp [inv, hgt, ang, nrm, CellIn, HexIn, rotN, Prod.ext_iff] at * <;>
    (try split_ifs at *) <;> omega))

theorem tube_inj (hr : 2 ≤ r) (hs : 2 ≤ s) {g g' : Fin 11} {w w' : ℤ × ℤ} (hg : 8 ≤ g.val)
    (hg' : 8 ≤ g'.val) (hw : CellIn r s g w) (hw' : CellIn r s g' w')
    (h : inv r s (g, w) = inv r s (g', w')) : V r s g w = V r s g' w' := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  by_cases e : g = g'
  · subst e
    have h3 : inv3 r s (g, w) = inv3 r s (g, w') := by
      have a1 : aux r g w = 0 := by simp [aux]; omega
      have a2 : aux r g w' = 0 := by simp [aux]; omega
      simp only [inv3, h, a1, a2]
    rw [inv3_inj_cell hr0 hs0 hw hw' h3]
  obtain ⟨x, y⟩ := w; obtain ⟨x', y'⟩ := w'
  fin_cases g <;> fin_cases g' <;> simp at hg hg' e
  · exact (V_glue hr0 hs0 gl_9_2 (by tglue_tac) hw' hw).symm
  · exact V_glue hr0 hs0 gl_8_2 (by tglue_tac) hw hw'
  · exact V_glue hr0 hs0 gl_9_2 (by tglue_tac) hw hw'
  · exact (V_glue hr0 hs0 gl_10_2 (by tglue_tac) hw' hw).symm
  · exact (V_glue hr0 hs0 gl_8_2 (by tglue_tac) hw' hw).symm
  · exact V_glue hr0 hs0 gl_10_2 (by tglue_tac) hw hw'

/-! ## Values -/

macro "val_tac" : tactic =>
  `(tactic| (simp [inv, hgt, ang, nrm, CellIn, TriIn, HexIn, dC, AR, InD, RM, zz] at * <;>
    (try split_ifs) <;> omega))

set_option maxHeartbeats 4000000 in
theorem val_top (hr : 2 ≤ r) (hs : 2 ≤ s) {f : Fin 11} {z : ℤ × ℤ} (hf : f.val < 4)
    (hz : CellIn r s f z) :
    AR r (inv r s (f, z)) ∧ (inv r s (f, z)).1 ≤ -zz r (inv r s (f, z)).2 ∧ InD r (dC r f z) ∧
      (inv r s (f, z)).1 ≤ 0 := by
  obtain ⟨x, y⟩ := z
  fin_cases f <;> simp at hf <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> val_tac

set_option maxHeartbeats 4000000 in
theorem val_bot (hr : 2 ≤ r) (hs : 2 ≤ s) {f : Fin 11} {z : ℤ × ℤ} (hf1 : 4 ≤ f.val)
    (hf : f.val < 8) (hz : CellIn r s f z) :
    AR r (inv r s (f, z)) ∧ 2 * s + zz r (inv r s (f, z)).2 ≤ (inv r s (f, z)).1 ∧
      InD r (dC r f z) ∧ 2 * s ≤ (inv r s (f, z)).1 := by
  obtain ⟨x, y⟩ := z
  fin_cases f <;> simp at hf hf1 <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> val_tac

set_option maxHeartbeats 4000000 in
theorem val_tube (hr : 2 ≤ r) (hs : 2 ≤ s) {g : Fin 11} {w : ℤ × ℤ} (hg : 8 ≤ g.val)
    (hw : CellIn r s g w) : RM r s (inv r s (g, w)) := by
  obtain ⟨x, y⟩ := w
  fin_cases g <;> simp at hg <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> val_tac

/-! ## Edges -/

theorem cap_edge {f : Fin 11} {z d : ℤ × ℤ} (hf : capOf f < 2) (hd : d ∈ unitVec) :
    Unit (dC r f (z + d) - dC r f z) := by
  obtain ⟨x, y⟩ := z
  simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hd
  fin_cases f <;> simp [capOf] at hf <;>
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [dC, Unit] <;> omega

set_option maxHeartbeats 4000000 in
theorem tube_edge (hr : 2 ≤ r) (hs : 2 ≤ s) {g : Fin 11} {z d : ℤ × ℤ} (hg : 8 ≤ g.val)
    (hz : CellIn r s g z) (hz' : CellIn r s g (z + d)) (hd : d ∈ unitVec) :
    TA r (inv r s (g, z)) (inv r s (g, z + d)) := by
  obtain ⟨x, y⟩ := z
  simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · fin_cases g <;> simp at hg <;> apply ta_4 <;> simp [inv, hgt, ang, nrm, AE, CellIn, HexIn] at * <;> (try split_ifs) <;> omega
  · fin_cases g <;> simp at hg <;> apply ta_1 <;> simp [inv, hgt, ang, nrm, AE, CellIn, HexIn] at * <;> (try split_ifs) <;> omega
  · fin_cases g <;> simp at hg <;> apply ta_5 <;> simp [inv, hgt, ang, nrm, AE, CellIn, HexIn] at * <;> (try split_ifs) <;> omega
  · fin_cases g <;> simp at hg <;> apply ta_3 <;> simp [inv, hgt, ang, nrm, AE, CellIn, HexIn] at * <;> (try split_ifs) <;> omega
  · fin_cases g <;> simp at hg <;> apply ta_2 <;> simp [inv, hgt, ang, nrm, AE, CellIn, HexIn] at * <;> (try split_ifs) <;> omega
  · fin_cases g <;> simp at hg <;> apply ta_6 <;> simp [inv, hgt, ang, nrm, AE, CellIn, HexIn] at * <;> (try split_ifs) <;> omega

end Claude4K3
