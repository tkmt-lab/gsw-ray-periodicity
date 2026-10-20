import Formal.Claude2K3Inv3
import Formal.Claude4K3Seam

/-!
# K3 pieces: cap coordinates

Written by a Claude worker (2026-10-20, K3 bridge).

`dC r f z` places the four cells of each cap (top: `0..3`, bottom: `4..7`) in the triangle
`Δ = {x, y ≥ 0, x + y ≤ 2r}`.

* `dC_wd_f_g` (top cap; bottom cap and the dispatcher `dC_wd` in `Claude4K3CapWdB.lean`) : two
             sites of one cap with the same invariant `inv3` have the same position (so the position
             is a function of the vertex); injectivity is `dC_inj` (`Claude4K3CapInj.lean`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Claude4K3

open ClaudeChallenge Claude2Aligned Claude2K3

variable {r s : ℤ}

/-- Position of a cap point in `Δ`. -/
def dC (r : ℤ) (f : Fin 11) (z : ℤ × ℤ) : ℤ × ℤ :=
  match f.val with
  | 0 => (z.1, z.2)
  | 1 => (2 * r - z.1 - z.2, z.1)
  | 2 => (z.2, 2 * r - z.1 - z.2)
  | 3 => (r - z.2, z.1 + z.2)
  | 4 => (z.1, z.2 + r)
  | 5 => (z.2 + r, r - z.1 - z.2)
  | 6 => (r - z.1 - z.2, z.1)
  | 7 => (z.1 + z.2, r - z.1)
  | _ => (z.1, z.2)

/-- Piece of a cell: `0` top cap, `1` bottom cap, `2` tube. -/
def capOf (f : Fin 11) : ℕ := if f.val < 4 then 0 else if f.val < 8 then 1 else 2

set_option maxHeartbeats 1000000 in
theorem dC_wd_0_0 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (0 : Fin 11) z)
    (hw : CellIn r s (0 : Fin 11) w) (h : inv3 r s ((0 : Fin 11), z) = inv3 r s ((0 : Fin 11), w)) :
    dC r (0 : Fin 11) z = dC r (0 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_0_1 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (0 : Fin 11) z)
    (hw : CellIn r s (1 : Fin 11) w) (h : inv3 r s ((0 : Fin 11), z) = inv3 r s ((1 : Fin 11), w)) :
    dC r (0 : Fin 11) z = dC r (1 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_0_2 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (0 : Fin 11) z)
    (hw : CellIn r s (2 : Fin 11) w) (h : inv3 r s ((0 : Fin 11), z) = inv3 r s ((2 : Fin 11), w)) :
    dC r (0 : Fin 11) z = dC r (2 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_0_3 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (0 : Fin 11) z)
    (hw : CellIn r s (3 : Fin 11) w) (h : inv3 r s ((0 : Fin 11), z) = inv3 r s ((3 : Fin 11), w)) :
    dC r (0 : Fin 11) z = dC r (3 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_1_0 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (1 : Fin 11) z)
    (hw : CellIn r s (0 : Fin 11) w) (h : inv3 r s ((1 : Fin 11), z) = inv3 r s ((0 : Fin 11), w)) :
    dC r (1 : Fin 11) z = dC r (0 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_1_1 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (1 : Fin 11) z)
    (hw : CellIn r s (1 : Fin 11) w) (h : inv3 r s ((1 : Fin 11), z) = inv3 r s ((1 : Fin 11), w)) :
    dC r (1 : Fin 11) z = dC r (1 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_1_2 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (1 : Fin 11) z)
    (hw : CellIn r s (2 : Fin 11) w) (h : inv3 r s ((1 : Fin 11), z) = inv3 r s ((2 : Fin 11), w)) :
    dC r (1 : Fin 11) z = dC r (2 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_1_3 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (1 : Fin 11) z)
    (hw : CellIn r s (3 : Fin 11) w) (h : inv3 r s ((1 : Fin 11), z) = inv3 r s ((3 : Fin 11), w)) :
    dC r (1 : Fin 11) z = dC r (3 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_2_0 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (2 : Fin 11) z)
    (hw : CellIn r s (0 : Fin 11) w) (h : inv3 r s ((2 : Fin 11), z) = inv3 r s ((0 : Fin 11), w)) :
    dC r (2 : Fin 11) z = dC r (0 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_2_1 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (2 : Fin 11) z)
    (hw : CellIn r s (1 : Fin 11) w) (h : inv3 r s ((2 : Fin 11), z) = inv3 r s ((1 : Fin 11), w)) :
    dC r (2 : Fin 11) z = dC r (1 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_2_2 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (2 : Fin 11) z)
    (hw : CellIn r s (2 : Fin 11) w) (h : inv3 r s ((2 : Fin 11), z) = inv3 r s ((2 : Fin 11), w)) :
    dC r (2 : Fin 11) z = dC r (2 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_2_3 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (2 : Fin 11) z)
    (hw : CellIn r s (3 : Fin 11) w) (h : inv3 r s ((2 : Fin 11), z) = inv3 r s ((3 : Fin 11), w)) :
    dC r (2 : Fin 11) z = dC r (3 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_3_0 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (3 : Fin 11) z)
    (hw : CellIn r s (0 : Fin 11) w) (h : inv3 r s ((3 : Fin 11), z) = inv3 r s ((0 : Fin 11), w)) :
    dC r (3 : Fin 11) z = dC r (0 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_3_1 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (3 : Fin 11) z)
    (hw : CellIn r s (1 : Fin 11) w) (h : inv3 r s ((3 : Fin 11), z) = inv3 r s ((1 : Fin 11), w)) :
    dC r (3 : Fin 11) z = dC r (1 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_3_2 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (3 : Fin 11) z)
    (hw : CellIn r s (2 : Fin 11) w) (h : inv3 r s ((3 : Fin 11), z) = inv3 r s ((2 : Fin 11), w)) :
    dC r (3 : Fin 11) z = dC r (2 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_3_3 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (3 : Fin 11) z)
    (hw : CellIn r s (3 : Fin 11) w) (h : inv3 r s ((3 : Fin 11), z) = inv3 r s ((3 : Fin 11), w)) :
    dC r (3 : Fin 11) z = dC r (3 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

end Claude4K3
