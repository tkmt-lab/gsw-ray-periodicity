import Formal.Claude4K3CapWd

/-!
# K3 pieces: cap coordinates of the bottom cap are well defined

Written by a Claude worker (2026-10-20, K3 bridge).  Continuation of `Claude4K3CapWd.lean`
(split for memory): the bottom-cap pairs and the dispatcher `dC_wd`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Claude4K3

open ClaudeChallenge Claude2Aligned Claude2K3

variable {r s : ℤ}

set_option maxHeartbeats 1000000 in
theorem dC_wd_4_4 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (4 : Fin 11) z)
    (hw : CellIn r s (4 : Fin 11) w) (h : inv3 r s ((4 : Fin 11), z) = inv3 r s ((4 : Fin 11), w)) :
    dC r (4 : Fin 11) z = dC r (4 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_4_5 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (4 : Fin 11) z)
    (hw : CellIn r s (5 : Fin 11) w) (h : inv3 r s ((4 : Fin 11), z) = inv3 r s ((5 : Fin 11), w)) :
    dC r (4 : Fin 11) z = dC r (5 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_4_6 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (4 : Fin 11) z)
    (hw : CellIn r s (6 : Fin 11) w) (h : inv3 r s ((4 : Fin 11), z) = inv3 r s ((6 : Fin 11), w)) :
    dC r (4 : Fin 11) z = dC r (6 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_4_7 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (4 : Fin 11) z)
    (hw : CellIn r s (7 : Fin 11) w) (h : inv3 r s ((4 : Fin 11), z) = inv3 r s ((7 : Fin 11), w)) :
    dC r (4 : Fin 11) z = dC r (7 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_5_4 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (5 : Fin 11) z)
    (hw : CellIn r s (4 : Fin 11) w) (h : inv3 r s ((5 : Fin 11), z) = inv3 r s ((4 : Fin 11), w)) :
    dC r (5 : Fin 11) z = dC r (4 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_5_5 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (5 : Fin 11) z)
    (hw : CellIn r s (5 : Fin 11) w) (h : inv3 r s ((5 : Fin 11), z) = inv3 r s ((5 : Fin 11), w)) :
    dC r (5 : Fin 11) z = dC r (5 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_5_6 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (5 : Fin 11) z)
    (hw : CellIn r s (6 : Fin 11) w) (h : inv3 r s ((5 : Fin 11), z) = inv3 r s ((6 : Fin 11), w)) :
    dC r (5 : Fin 11) z = dC r (6 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_5_7 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (5 : Fin 11) z)
    (hw : CellIn r s (7 : Fin 11) w) (h : inv3 r s ((5 : Fin 11), z) = inv3 r s ((7 : Fin 11), w)) :
    dC r (5 : Fin 11) z = dC r (7 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_6_4 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (6 : Fin 11) z)
    (hw : CellIn r s (4 : Fin 11) w) (h : inv3 r s ((6 : Fin 11), z) = inv3 r s ((4 : Fin 11), w)) :
    dC r (6 : Fin 11) z = dC r (4 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_6_5 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (6 : Fin 11) z)
    (hw : CellIn r s (5 : Fin 11) w) (h : inv3 r s ((6 : Fin 11), z) = inv3 r s ((5 : Fin 11), w)) :
    dC r (6 : Fin 11) z = dC r (5 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_6_6 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (6 : Fin 11) z)
    (hw : CellIn r s (6 : Fin 11) w) (h : inv3 r s ((6 : Fin 11), z) = inv3 r s ((6 : Fin 11), w)) :
    dC r (6 : Fin 11) z = dC r (6 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_6_7 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (6 : Fin 11) z)
    (hw : CellIn r s (7 : Fin 11) w) (h : inv3 r s ((6 : Fin 11), z) = inv3 r s ((7 : Fin 11), w)) :
    dC r (6 : Fin 11) z = dC r (7 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_7_4 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (7 : Fin 11) z)
    (hw : CellIn r s (4 : Fin 11) w) (h : inv3 r s ((7 : Fin 11), z) = inv3 r s ((4 : Fin 11), w)) :
    dC r (7 : Fin 11) z = dC r (4 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_7_5 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (7 : Fin 11) z)
    (hw : CellIn r s (5 : Fin 11) w) (h : inv3 r s ((7 : Fin 11), z) = inv3 r s ((5 : Fin 11), w)) :
    dC r (7 : Fin 11) z = dC r (5 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_7_6 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (7 : Fin 11) z)
    (hw : CellIn r s (6 : Fin 11) w) (h : inv3 r s ((7 : Fin 11), z) = inv3 r s ((6 : Fin 11), w)) :
    dC r (7 : Fin 11) z = dC r (6 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

set_option maxHeartbeats 1000000 in
theorem dC_wd_7_7 (hr : 2 ≤ r) (hs : 2 ≤ s) {z w : ℤ × ℤ} (hz : CellIn r s (7 : Fin 11) z)
    (hw : CellIn r s (7 : Fin 11) w) (h : inv3 r s ((7 : Fin 11), z) = inv3 r s ((7 : Fin 11), w)) :
    dC r (7 : Fin 11) z = dC r (7 : Fin 11) w := by
  obtain ⟨x, y⟩ := z; obtain ⟨x', y'⟩ := w
  simp [inv3, inv, hgt, ang, nrm, aux, CellIn, TriIn, dC, Prod.ext_iff] at hz hw h ⊢
  split_ifs at h <;> omega

theorem dC_wd (hr : 2 ≤ r) (hs : 2 ≤ s) {f g : Fin 11} {z w : ℤ × ℤ} (hf : capOf f < 2)
    (hfg : capOf f = capOf g) (hz : CellIn r s f z) (hw : CellIn r s g w)
    (h : inv3 r s (f, z) = inv3 r s (g, w)) : dC r f z = dC r g w := by
  fin_cases f <;> fin_cases g <;> simp [capOf] at hf hfg
  · exact dC_wd_0_0 hr hs hz hw h
  · exact dC_wd_0_1 hr hs hz hw h
  · exact dC_wd_0_2 hr hs hz hw h
  · exact dC_wd_0_3 hr hs hz hw h
  · exact dC_wd_1_0 hr hs hz hw h
  · exact dC_wd_1_1 hr hs hz hw h
  · exact dC_wd_1_2 hr hs hz hw h
  · exact dC_wd_1_3 hr hs hz hw h
  · exact dC_wd_2_0 hr hs hz hw h
  · exact dC_wd_2_1 hr hs hz hw h
  · exact dC_wd_2_2 hr hs hz hw h
  · exact dC_wd_2_3 hr hs hz hw h
  · exact dC_wd_3_0 hr hs hz hw h
  · exact dC_wd_3_1 hr hs hz hw h
  · exact dC_wd_3_2 hr hs hz hw h
  · exact dC_wd_3_3 hr hs hz hw h
  · exact dC_wd_4_4 hr hs hz hw h
  · exact dC_wd_4_5 hr hs hz hw h
  · exact dC_wd_4_6 hr hs hz hw h
  · exact dC_wd_4_7 hr hs hz hw h
  · exact dC_wd_5_4 hr hs hz hw h
  · exact dC_wd_5_5 hr hs hz hw h
  · exact dC_wd_5_6 hr hs hz hw h
  · exact dC_wd_5_7 hr hs hz hw h
  · exact dC_wd_6_4 hr hs hz hw h
  · exact dC_wd_6_5 hr hs hz hw h
  · exact dC_wd_6_6 hr hs hz hw h
  · exact dC_wd_6_7 hr hs hz hw h
  · exact dC_wd_7_4 hr hs hz hw h
  · exact dC_wd_7_5 hr hs hz hw h
  · exact dC_wd_7_6 hr hs hz hw h
  · exact dC_wd_7_7 hr hs hz hw h

end Claude4K3
