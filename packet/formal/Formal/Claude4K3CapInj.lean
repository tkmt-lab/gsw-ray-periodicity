import Formal.Claude4K3CapWdB

/-!
# K3 pieces: cap coordinates are injective on vertices

Written by a Claude worker (2026-10-20, K3 bridge).

* `toMid_*` : a point of a corner triangle that is also placed in the middle triangle of its
              cap is glued to the corresponding point of the middle triangle;
* `dC_inj`  : two sites of one cap with the same position in `Δ` are the same vertex.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Claude4K3

open ClaudeChallenge Claude2Aligned Claude2K3

variable {r s : ℤ}

/-- Inverse of the placement of the middle top triangle (cell 3). -/
def m3 (r : ℤ) (p : ℤ × ℤ) : ℤ × ℤ := (p.1 + p.2 - r, r - p.1)

/-- Inverse of the placement of the middle bottom triangle (cell 7). -/
def m7 (r : ℤ) (p : ℤ × ℤ) : ℤ × ℤ := (r - p.2, p.1 + p.2 - r)

theorem m3_dC (z : ℤ × ℤ) : m3 r (dC r 3 z) = z := by
  ext <;> simp [m3, dC] <;> ring

theorem m7_dC (z : ℤ × ℤ) : m7 r (dC r 7 z) = z := by
  ext <;> simp [m7, dC] <;> ring

macro "mid_tac" : tactic =>
  `(tactic| (ext <;> simp [rotN, rot, m3, m7, dC] <;> ring))

theorem toMid_0 (hr : 0 < r) (hs : 0 < s) {z : ℤ × ℤ} (hz : CellIn r s 0 z)
    (hm : CellIn r s 3 (m3 r (dC r 0 z))) : V r s 0 z = V r s 3 (m3 r (dC r 0 z)) :=
  V_glue hr hs gl_0_1 (by mid_tac) hz hm

theorem toMid_1 (hr : 0 < r) (hs : 0 < s) {z : ℤ × ℤ} (hz : CellIn r s 1 z)
    (hm : CellIn r s 3 (m3 r (dC r 1 z))) : V r s 1 z = V r s 3 (m3 r (dC r 1 z)) :=
  V_glue hr hs gl_1_1 (by mid_tac) hz hm

theorem toMid_2 (hr : 0 < r) (hs : 0 < s) {z : ℤ × ℤ} (hz : CellIn r s 2 z)
    (hm : CellIn r s 3 (m3 r (dC r 2 z))) : V r s 2 z = V r s 3 (m3 r (dC r 2 z)) :=
  V_glue hr hs gl_2_1 (by mid_tac) hz hm

theorem toMid_4 (hr : 0 < r) (hs : 0 < s) {z : ℤ × ℤ} (hz : CellIn r s 4 z)
    (hm : CellIn r s 7 (m7 r (dC r 4 z))) : V r s 4 z = V r s 7 (m7 r (dC r 4 z)) :=
  V_glue hr hs gl_4_0 (by mid_tac) hz hm

theorem toMid_5 (hr : 0 < r) (hs : 0 < s) {z : ℤ × ℤ} (hz : CellIn r s 5 z)
    (hm : CellIn r s 7 (m7 r (dC r 5 z))) : V r s 5 z = V r s 7 (m7 r (dC r 5 z)) :=
  V_glue hr hs gl_5_0 (by mid_tac) hz hm

theorem toMid_6 (hr : 0 < r) (hs : 0 < s) {z : ℤ × ℤ} (hz : CellIn r s 6 z)
    (hm : CellIn r s 7 (m7 r (dC r 6 z))) : V r s 6 z = V r s 7 (m7 r (dC r 6 z)) :=
  V_glue hr hs gl_6_0 (by mid_tac) hz hm

/-- A corner cell of the top cap, glued to the middle cell. -/
theorem toMid_top (hr : 0 < r) (hs : 0 < s) {f : Fin 11} (hf : f.val < 3) {z : ℤ × ℤ}
    (hz : CellIn r s f z) (hm : CellIn r s 3 (m3 r (dC r f z))) :
    V r s f z = V r s 3 (m3 r (dC r f z)) := by
  have : f = 0 ∨ f = 1 ∨ f = 2 := by omega
  rcases this with rfl | rfl | rfl
  · exact toMid_0 hr hs hz hm
  · exact toMid_1 hr hs hz hm
  · exact toMid_2 hr hs hz hm

theorem toMid_bot (hr : 0 < r) (hs : 0 < s) {f : Fin 11} (hf1 : 4 ≤ f.val) (hf2 : f.val < 7)
    {z : ℤ × ℤ} (hz : CellIn r s f z) (hm : CellIn r s 7 (m7 r (dC r f z))) :
    V r s f z = V r s 7 (m7 r (dC r f z)) := by
  have : f = 4 ∨ f = 5 ∨ f = 6 := by omega
  rcases this with rfl | rfl | rfl
  · exact toMid_4 hr hs hz hm
  · exact toMid_5 hr hs hz hm
  · exact toMid_6 hr hs hz hm

theorem dC_inj_cell {f : Fin 11} {z w : ℤ × ℤ} (h : dC r f z = dC r f w) : z = w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  fin_cases f <;> simp [dC, Prod.ext_iff] at h ⊢ <;> omega


theorem mid_of_top (hr : 2 ≤ r) {f g : Fin 11} {z w : ℤ × ℤ} (hf : f.val < 3) (hg : g.val < 3)
    (hfg : f ≠ g) (hz : CellIn r s f z) (hw : CellIn r s g w) (h : dC r f z = dC r g w) :
    CellIn r s 3 (m3 r (dC r f z)) := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  fin_cases f <;> fin_cases g <;>
    simp [CellIn, TriIn, dC, m3, m7, capOf, Prod.ext_iff] at * <;> omega

theorem mid_of_bot (hr : 2 ≤ r) {f g : Fin 11} {z w : ℤ × ℤ} (hf1 : 4 ≤ f.val) (hf : f.val < 7)
    (hg1 : 4 ≤ g.val) (hg : g.val < 7) (hfg : f ≠ g) (hz : CellIn r s f z) (hw : CellIn r s g w)
    (h : dC r f z = dC r g w) : CellIn r s 7 (m7 r (dC r f z)) := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  fin_cases f <;> fin_cases g <;>
    simp [CellIn, TriIn, dC, m3, m7, capOf, Prod.ext_iff] at * <;> omega

/-- **Injectivity of the cap position**: two sites of one cap with the same position in `Δ`
are the same vertex. -/
theorem dC_inj (hr : 2 ≤ r) (hs : 2 ≤ s) {f g : Fin 11} {z w : ℤ × ℤ} (hf : capOf f < 2)
    (hfg : capOf f = capOf g) (hz : CellIn r s f z) (hw : CellIn r s g w)
    (h : dC r f z = dC r g w) : V r s f z = V r s g w := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  by_cases e : f = g
  · subst e; rw [dC_inj_cell h]
  have hm3 : ∀ (k : Fin 11) (u : ℤ × ℤ), k = 3 → V r s k u = V r s 3 (m3 r (dC r k u)) := by
    rintro k u rfl; rw [m3_dC]
  have hm7 : ∀ (k : Fin 11) (u : ℤ × ℤ), k = 7 → V r s k u = V r s 7 (m7 r (dC r k u)) := by
    rintro k u rfl; rw [m7_dC]
  simp only [capOf] at hf hfg
  by_cases hfT : f.val < 4
  · have hgT : g.val < 4 := by split_ifs at hfg <;> omega
    have hcell : CellIn r s 3 (m3 r (dC r f z)) := by
      by_cases f3 : f.val = 3
      · have : f = 3 := Fin.ext f3
        subst this; rw [m3_dC]; exact hz
      by_cases g3 : g.val = 3
      · have : g = 3 := Fin.ext g3
        subst this; rw [h, m3_dC]; exact hw
      exact mid_of_top hr (by omega) (by omega) e hz hw h
    have k1 : V r s f z = V r s 3 (m3 r (dC r f z)) := by
      by_cases f3 : f.val = 3
      · exact hm3 f z (Fin.ext f3)
      · exact toMid_top hr0 hs0 (by omega) hz hcell
    have k2 : V r s g w = V r s 3 (m3 r (dC r g w)) := by
      by_cases g3 : g.val = 3
      · exact hm3 g w (Fin.ext g3)
      · exact toMid_top hr0 hs0 (by omega) hw (by rw [← h]; exact hcell)
    rw [k1, k2, h]
  · have hf8 : f.val < 8 := by split_ifs at hf <;> omega
    have hg4 : 4 ≤ g.val ∧ g.val < 8 := by split_ifs at hfg <;> omega
    have hcell : CellIn r s 7 (m7 r (dC r f z)) := by
      by_cases f7 : f.val = 7
      · have : f = 7 := Fin.ext f7
        subst this; rw [m7_dC]; exact hz
      by_cases g7 : g.val = 7
      · have : g = 7 := Fin.ext g7
        subst this; rw [h, m7_dC]; exact hw
      exact mid_of_bot hr (by omega) (by omega) (by omega) (by omega) e hz hw h
    have k1 : V r s f z = V r s 7 (m7 r (dC r f z)) := by
      by_cases f7 : f.val = 7
      · exact hm7 f z (Fin.ext f7)
      · exact toMid_bot hr0 hs0 (by omega) (by omega) hz hcell
    have k2 : V r s g w = V r s 7 (m7 r (dC r g w)) := by
      by_cases g7 : g.val = 7
      · exact hm7 g w (Fin.ext g7)
      · exact toMid_bot hr0 hs0 (by omega) (by omega) hw (by rw [← h]; exact hcell)
    rw [k1, k2, h]

end Claude4K3
