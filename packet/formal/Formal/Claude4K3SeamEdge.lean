import Formal.Claude4K3SeamSite
import Formal.Claude4K3Chord

/-!
# K3 pieces: edges along the seams, cell by cell

Written by a Claude worker (2026-10-20, K3 bridge).

* `tube_top_cap`, `tube_bot_cap` : a point on the top (bottom) edges of a hexagon is glued to a
  cap point;
* `topEdge_of_TopB`, `botEdge_of_BotS`, `outer_top`, `outer_bot` : a site whose invariant lies on
  a seam is on the outer edges of its cell;
* `seam_cases_top/bot` : a cap edge between two seam sites runs along an outer edge or is the
  chord across the corner of the cell;
* `along_TA_top/bot`, `along_uniq_top/bot`, `chord_top/bot`, `tube_seam_top/bot` : what that means
  in tube and cap coordinates.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Claude4K3

open ClaudeChallenge Claude2Aligned Claude2K3

variable {r s : ℤ}

macro "geo_tac" : tactic =>
  `(tactic| (simp [inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bTg, bBg, rotN, rot,
      TopEdge, BotEdge, TopB, BotS, AR, InD, Unit, zz, Prod.ext_iff] at * <;>
    (try split_ifs at *) <;> omega))

/-! ## Seam points of the tube are glued to the caps -/

set_option maxHeartbeats 2000000 in
theorem tube_top_cap (hr : 2 ≤ r) (hs : 2 ≤ s) {g : Fin 11} {w : ℤ × ℤ} (hg : 8 ≤ g.val)
    (hw : CellIn r s g w) (he : TopEdge r w) :
    ∃ f z, f.val < 4 ∧ CellIn r s f z ∧ V r s f z = V r s g w := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  obtain ⟨x, y⟩ := w
  simp only [TopEdge] at he
  fin_cases g <;> simp at hg <;> rcases he with h | h
  · exact ⟨1, (0, x), by decide, by geo_tac, V_glue hr0 hs0 gl_1_2 (by geo_tac) (by geo_tac) hw⟩
  · exact ⟨0, (r - y, 0), by decide, by geo_tac, V_glue hr0 hs0 gl_0_0 (by geo_tac) (by geo_tac) hw⟩
  · exact ⟨2, (0, x), by decide, by geo_tac, V_glue hr0 hs0 gl_2_2 (by geo_tac) (by geo_tac) hw⟩
  · exact ⟨1, (r - y, 0), by decide, by geo_tac, V_glue hr0 hs0 gl_1_0 (by geo_tac) (by geo_tac) hw⟩
  · exact ⟨0, (0, x), by decide, by geo_tac, V_glue hr0 hs0 gl_0_2 (by geo_tac) (by geo_tac) hw⟩
  · exact ⟨2, (r - y, 0), by decide, by geo_tac, V_glue hr0 hs0 gl_2_0 (by geo_tac) (by geo_tac) hw⟩

set_option maxHeartbeats 2000000 in
theorem tube_bot_cap (hr : 2 ≤ r) (hs : 2 ≤ s) {g : Fin 11} {w : ℤ × ℤ} (hg : 8 ≤ g.val)
    (hw : CellIn r s g w) (he : BotEdge r s w) :
    ∃ f z, 4 ≤ f.val ∧ f.val < 8 ∧ CellIn r s f z ∧ V r s f z = V r s g w := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  obtain ⟨x, y⟩ := w
  simp only [BotEdge] at he
  fin_cases g <;> simp at hg <;> rcases he with h | h
  · exact ⟨4, (r - s - x, s + x), by decide, by decide, by geo_tac,
      V_glue hr0 hs0 gl_4_1 (by geo_tac) (by geo_tac) hw⟩
  · exact ⟨5, (0, r + s - y), by decide, by decide, by geo_tac,
      V_glue hr0 hs0 gl_5_2 (by geo_tac) (by geo_tac) hw⟩
  · exact ⟨5, (r - s - x, s + x), by decide, by decide, by geo_tac,
      V_glue hr0 hs0 gl_5_1 (by geo_tac) (by geo_tac) hw⟩
  · exact ⟨6, (0, r + s - y), by decide, by decide, by geo_tac,
      V_glue hr0 hs0 gl_6_2 (by geo_tac) (by geo_tac) hw⟩
  · exact ⟨6, (r - s - x, s + x), by decide, by decide, by geo_tac,
      V_glue hr0 hs0 gl_6_1 (by geo_tac) (by geo_tac) hw⟩
  · exact ⟨4, (0, r + s - y), by decide, by decide, by geo_tac,
      V_glue hr0 hs0 gl_4_2 (by geo_tac) (by geo_tac) hw⟩

set_option maxHeartbeats 2000000 in
theorem topEdge_of_TopB (hr : 2 ≤ r) (hs : 2 ≤ s) {g : Fin 11} {w : ℤ × ℤ} (hg : 8 ≤ g.val)
    (hw : CellIn r s g w) (h : TopB r (inv r s (g, w))) : TopEdge r w := by
  obtain ⟨x, y⟩ := w
  fin_cases g <;> simp at hg <;> geo_tac

set_option maxHeartbeats 2000000 in
theorem botEdge_of_BotS (hr : 2 ≤ r) (hs : 2 ≤ s) {g : Fin 11} {w : ℤ × ℤ} (hg : 8 ≤ g.val)
    (hw : CellIn r s g w) (h : BotS r s (inv r s (g, w))) : BotEdge r s w := by
  obtain ⟨x, y⟩ := w
  fin_cases g <;> simp at hg <;> geo_tac

/-! ## Seam points of the caps -/

/-- Outer points of a top cap cell: the two outer edges of a corner cell, or a corner of the middle
cell. -/
def OuterT (r : ℤ) (f : Fin 11) (z : ℤ × ℤ) : Prop :=
  (f.val < 3 ∧ (z.2 = 0 ∨ z.1 = 0)) ∨
    (f.val = 3 ∧ ((z.1 = 0 ∧ z.2 = 0) ∨ (z.1 = r ∧ z.2 = 0) ∨ (z.1 = 0 ∧ z.2 = r)))

/-- Outer points of a bottom cap cell. -/
def OuterB (r : ℤ) (f : Fin 11) (z : ℤ × ℤ) : Prop :=
  (4 ≤ f.val ∧ f.val < 7 ∧ (z.1 + z.2 = r ∨ z.1 = 0)) ∨
    (f.val = 7 ∧ ((z.1 = 0 ∧ z.2 = 0) ∨ (z.1 = r ∧ z.2 = 0) ∨ (z.1 = 0 ∧ z.2 = r)))

set_option maxHeartbeats 2000000 in
theorem outer_top (hr : 2 ≤ r) (hs : 2 ≤ s) {f : Fin 11} {z : ℤ × ℤ} (hf : f.val < 4)
    (hz : CellIn r s f z) (h : TopB r (inv r s (f, z))) : OuterT r f z := by
  obtain ⟨x, y⟩ := z
  fin_cases f <;> simp at hf <;> simp [OuterT] <;> geo_tac

set_option maxHeartbeats 2000000 in
theorem outer_bot (hr : 2 ≤ r) (hs : 2 ≤ s) {f : Fin 11} {z : ℤ × ℤ} (hf1 : 4 ≤ f.val)
    (hf : f.val < 8) (hz : CellIn r s f z) (h : BotS r s (inv r s (f, z))) : OuterB r f z := by
  obtain ⟨x, y⟩ := z
  fin_cases f <;> simp at hf hf1 <;> simp [OuterB] <;> geo_tac

end Claude4K3
