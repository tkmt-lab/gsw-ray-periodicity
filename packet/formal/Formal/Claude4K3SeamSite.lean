import Formal.Claude4K3TubeInj

/-!
# K3 pieces: the seams between the caps and the tube, cell by cell

Written by a Claude worker (2026-10-20, K3 bridge).

* `bc_top`, `bc_bot` : a tube site glued to a cap site lies on the top (bottom) edges of its
  hexagon, and its cap position is `bTg` (`bBg`), a linear function on each hexagon;
* `tube_top_cap`, `tube_bot_cap` : conversely such a tube site is glued to a cap site;
* `topEdge_of_TopB`, `botEdge_of_BotB` : a tube site whose invariant is on a seam lies on the
  corresponding edges.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Claude4K3

open ClaudeChallenge Claude2Aligned Claude2K3

variable {r s : ℤ}

/-- On the bottom seam. -/
def BotB (r s : ℤ) (t : ℤ × ℤ) : Prop := AR r t ∧ t.1 = 2 * s + zz r t.2

/-- Top edges of a hexagon. -/
def TopEdge (r : ℤ) (w : ℤ × ℤ) : Prop := w.2 = 0 ∨ w.1 = r

/-- Bottom edges of a hexagon. -/
def BotEdge (r s : ℤ) (w : ℤ × ℤ) : Prop := w.2 = r + s ∨ w.1 = -s

/-- Top-cap position of a point on the top edges of hexagon `g`. -/
def bTg (r : ℤ) (g : Fin 11) (w : ℤ × ℤ) : ℤ × ℤ :=
  match g.val with
  | 10 => (0, w.1 + w.2)
  | 9 => (w.1 + w.2, 2 * r - w.1 - w.2)
  | _ => (2 * r - w.1 - w.2, 0)

/-- Bottom-cap position of a point on the bottom edges of hexagon `g`. -/
def bBg (r : ℤ) (g : Fin 11) (w : ℤ × ℤ) : ℤ × ℤ :=
  match g.val with
  | 10 => (0, 2 * r - w.1 - w.2)
  | 9 => (w.1 + w.2, 0)
  | _ => (2 * r - w.1 - w.2, w.1 + w.2)

set_option maxHeartbeats 2000000 in
theorem bc_top_0_8 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (0 : Fin 11) z)
    (hw : CellIn r s (8 : Fin 11) w)
    (h : inv3 r s ((0 : Fin 11), z) = inv3 r s ((8 : Fin 11), w)) :
    TopEdge r w ∧ dC r (0 : Fin 11) z = bTg r (8 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bTg, TopEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_top_0_9 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (0 : Fin 11) z)
    (hw : CellIn r s (9 : Fin 11) w)
    (h : inv3 r s ((0 : Fin 11), z) = inv3 r s ((9 : Fin 11), w)) :
    TopEdge r w ∧ dC r (0 : Fin 11) z = bTg r (9 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bTg, TopEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_top_0_10 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (0 : Fin 11) z)
    (hw : CellIn r s (10 : Fin 11) w)
    (h : inv3 r s ((0 : Fin 11), z) = inv3 r s ((10 : Fin 11), w)) :
    TopEdge r w ∧ dC r (0 : Fin 11) z = bTg r (10 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bTg, TopEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_top_1_8 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (1 : Fin 11) z)
    (hw : CellIn r s (8 : Fin 11) w)
    (h : inv3 r s ((1 : Fin 11), z) = inv3 r s ((8 : Fin 11), w)) :
    TopEdge r w ∧ dC r (1 : Fin 11) z = bTg r (8 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bTg, TopEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_top_1_9 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (1 : Fin 11) z)
    (hw : CellIn r s (9 : Fin 11) w)
    (h : inv3 r s ((1 : Fin 11), z) = inv3 r s ((9 : Fin 11), w)) :
    TopEdge r w ∧ dC r (1 : Fin 11) z = bTg r (9 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bTg, TopEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_top_1_10 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (1 : Fin 11) z)
    (hw : CellIn r s (10 : Fin 11) w)
    (h : inv3 r s ((1 : Fin 11), z) = inv3 r s ((10 : Fin 11), w)) :
    TopEdge r w ∧ dC r (1 : Fin 11) z = bTg r (10 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bTg, TopEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_top_2_8 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (2 : Fin 11) z)
    (hw : CellIn r s (8 : Fin 11) w)
    (h : inv3 r s ((2 : Fin 11), z) = inv3 r s ((8 : Fin 11), w)) :
    TopEdge r w ∧ dC r (2 : Fin 11) z = bTg r (8 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bTg, TopEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_top_2_9 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (2 : Fin 11) z)
    (hw : CellIn r s (9 : Fin 11) w)
    (h : inv3 r s ((2 : Fin 11), z) = inv3 r s ((9 : Fin 11), w)) :
    TopEdge r w ∧ dC r (2 : Fin 11) z = bTg r (9 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bTg, TopEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_top_2_10 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (2 : Fin 11) z)
    (hw : CellIn r s (10 : Fin 11) w)
    (h : inv3 r s ((2 : Fin 11), z) = inv3 r s ((10 : Fin 11), w)) :
    TopEdge r w ∧ dC r (2 : Fin 11) z = bTg r (10 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bTg, TopEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_top_3_8 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (3 : Fin 11) z)
    (hw : CellIn r s (8 : Fin 11) w)
    (h : inv3 r s ((3 : Fin 11), z) = inv3 r s ((8 : Fin 11), w)) :
    TopEdge r w ∧ dC r (3 : Fin 11) z = bTg r (8 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bTg, TopEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_top_3_9 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (3 : Fin 11) z)
    (hw : CellIn r s (9 : Fin 11) w)
    (h : inv3 r s ((3 : Fin 11), z) = inv3 r s ((9 : Fin 11), w)) :
    TopEdge r w ∧ dC r (3 : Fin 11) z = bTg r (9 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bTg, TopEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_top_3_10 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (3 : Fin 11) z)
    (hw : CellIn r s (10 : Fin 11) w)
    (h : inv3 r s ((3 : Fin 11), z) = inv3 r s ((10 : Fin 11), w)) :
    TopEdge r w ∧ dC r (3 : Fin 11) z = bTg r (10 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bTg, TopEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

theorem bc_top (hr : 2 ≤ r) (hs : 2 ≤ s) {f g : Fin 11} {z w : ℤ × ℤ} (hf : f.val < 4)
    (hg : 8 ≤ g.val) (hz : CellIn r s f z) (hw : CellIn r s g w)
    (h : inv3 r s (f, z) = inv3 r s (g, w)) : TopEdge r w ∧ dC r f z = bTg r g w := by
  fin_cases f <;> fin_cases g <;> simp at hf hg 
  · exact bc_top_0_8 hr hs hz hw h
  · exact bc_top_0_9 hr hs hz hw h
  · exact bc_top_0_10 hr hs hz hw h
  · exact bc_top_1_8 hr hs hz hw h
  · exact bc_top_1_9 hr hs hz hw h
  · exact bc_top_1_10 hr hs hz hw h
  · exact bc_top_2_8 hr hs hz hw h
  · exact bc_top_2_9 hr hs hz hw h
  · exact bc_top_2_10 hr hs hz hw h
  · exact bc_top_3_8 hr hs hz hw h
  · exact bc_top_3_9 hr hs hz hw h
  · exact bc_top_3_10 hr hs hz hw h

set_option maxHeartbeats 2000000 in
theorem bc_bot_4_8 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (4 : Fin 11) z)
    (hw : CellIn r s (8 : Fin 11) w)
    (h : inv3 r s ((4 : Fin 11), z) = inv3 r s ((8 : Fin 11), w)) :
    BotEdge r s w ∧ dC r (4 : Fin 11) z = bBg r (8 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bBg, BotEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_bot_4_9 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (4 : Fin 11) z)
    (hw : CellIn r s (9 : Fin 11) w)
    (h : inv3 r s ((4 : Fin 11), z) = inv3 r s ((9 : Fin 11), w)) :
    BotEdge r s w ∧ dC r (4 : Fin 11) z = bBg r (9 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bBg, BotEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_bot_4_10 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (4 : Fin 11) z)
    (hw : CellIn r s (10 : Fin 11) w)
    (h : inv3 r s ((4 : Fin 11), z) = inv3 r s ((10 : Fin 11), w)) :
    BotEdge r s w ∧ dC r (4 : Fin 11) z = bBg r (10 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bBg, BotEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_bot_5_8 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (5 : Fin 11) z)
    (hw : CellIn r s (8 : Fin 11) w)
    (h : inv3 r s ((5 : Fin 11), z) = inv3 r s ((8 : Fin 11), w)) :
    BotEdge r s w ∧ dC r (5 : Fin 11) z = bBg r (8 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bBg, BotEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_bot_5_9 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (5 : Fin 11) z)
    (hw : CellIn r s (9 : Fin 11) w)
    (h : inv3 r s ((5 : Fin 11), z) = inv3 r s ((9 : Fin 11), w)) :
    BotEdge r s w ∧ dC r (5 : Fin 11) z = bBg r (9 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bBg, BotEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_bot_5_10 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (5 : Fin 11) z)
    (hw : CellIn r s (10 : Fin 11) w)
    (h : inv3 r s ((5 : Fin 11), z) = inv3 r s ((10 : Fin 11), w)) :
    BotEdge r s w ∧ dC r (5 : Fin 11) z = bBg r (10 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bBg, BotEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_bot_6_8 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (6 : Fin 11) z)
    (hw : CellIn r s (8 : Fin 11) w)
    (h : inv3 r s ((6 : Fin 11), z) = inv3 r s ((8 : Fin 11), w)) :
    BotEdge r s w ∧ dC r (6 : Fin 11) z = bBg r (8 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bBg, BotEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_bot_6_9 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (6 : Fin 11) z)
    (hw : CellIn r s (9 : Fin 11) w)
    (h : inv3 r s ((6 : Fin 11), z) = inv3 r s ((9 : Fin 11), w)) :
    BotEdge r s w ∧ dC r (6 : Fin 11) z = bBg r (9 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bBg, BotEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_bot_6_10 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (6 : Fin 11) z)
    (hw : CellIn r s (10 : Fin 11) w)
    (h : inv3 r s ((6 : Fin 11), z) = inv3 r s ((10 : Fin 11), w)) :
    BotEdge r s w ∧ dC r (6 : Fin 11) z = bBg r (10 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bBg, BotEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_bot_7_8 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (7 : Fin 11) z)
    (hw : CellIn r s (8 : Fin 11) w)
    (h : inv3 r s ((7 : Fin 11), z) = inv3 r s ((8 : Fin 11), w)) :
    BotEdge r s w ∧ dC r (7 : Fin 11) z = bBg r (8 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bBg, BotEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_bot_7_9 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (7 : Fin 11) z)
    (hw : CellIn r s (9 : Fin 11) w)
    (h : inv3 r s ((7 : Fin 11), z) = inv3 r s ((9 : Fin 11), w)) :
    BotEdge r s w ∧ dC r (7 : Fin 11) z = bBg r (9 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bBg, BotEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 2000000 in
theorem bc_bot_7_10 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (7 : Fin 11) z)
    (hw : CellIn r s (10 : Fin 11) w)
    (h : inv3 r s ((7 : Fin 11), z) = inv3 r s ((10 : Fin 11), w)) :
    BotEdge r s w ∧ dC r (7 : Fin 11) z = bBg r (10 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, HexIn, dC, bBg, BotEdge, Prod.ext_iff]
    at hz hw h ⊢
  split_ifs at h <;> omega

theorem bc_bot (hr : 2 ≤ r) (hs : 2 ≤ s) {f g : Fin 11} {z w : ℤ × ℤ} (hf : 4 ≤ f.val) (hf' : f.val < 8)
    (hg : 8 ≤ g.val) (hz : CellIn r s f z) (hw : CellIn r s g w)
    (h : inv3 r s (f, z) = inv3 r s (g, w)) : BotEdge r s w ∧ dC r f z = bBg r g w := by
  fin_cases f <;> fin_cases g <;> simp at hf hg hf'
  · exact bc_bot_4_8 hr hs hz hw h
  · exact bc_bot_4_9 hr hs hz hw h
  · exact bc_bot_4_10 hr hs hz hw h
  · exact bc_bot_5_8 hr hs hz hw h
  · exact bc_bot_5_9 hr hs hz hw h
  · exact bc_bot_5_10 hr hs hz hw h
  · exact bc_bot_6_8 hr hs hz hw h
  · exact bc_bot_6_9 hr hs hz hw h
  · exact bc_bot_6_10 hr hs hz hw h
  · exact bc_bot_7_8 hr hs hz hw h
  · exact bc_bot_7_9 hr hs hz hw h
  · exact bc_bot_7_10 hr hs hz hw h

end Claude4K3
