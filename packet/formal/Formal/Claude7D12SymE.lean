import Formal.Claude7D12Sym
import Formal.Claude7D12SuffBase

/-!
# D12 model: the two automorphisms as graph isomorphisms, and moving the first corner

Written by a Claude worker (2026-10-22, D12 bridge session).

* `E1`, `E2` : the automorphisms `sg1`, `sg2` of the model graph `GM r s`;
* `lit_E1`, `lit_E2` : literal paths are carried along;
* `to_label0` : for `r, s ≥ 2` a literal path gives one that starts at the label-0 point.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude7D12

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

theorem ro0_unit {z u : ℤ × ℤ} (hu : u ∈ unitVec) : ro0 r s (z + u) - ro0 r s z ∈ unitVec := by
  rw [unit_U2] at hu; rw [unit_sub]; simp only [ro0, Prod.fst_add, Prod.snd_add, U2] at hu ⊢; omega
theorem ro0'_unit {z u : ℤ × ℤ} (hu : u ∈ unitVec) : ro0' r s (z + u) - ro0' r s z ∈ unitVec := by
  rw [unit_U2] at hu; rw [unit_sub]; simp only [ro0', Prod.fst_add, Prod.snd_add, U2] at hu ⊢; omega
theorem ro1_unit {z u : ℤ × ℤ} (hu : u ∈ unitVec) : ro1 r s (z + u) - ro1 r s z ∈ unitVec := by
  rw [unit_U2] at hu; rw [unit_sub]; simp only [ro1, Prod.fst_add, Prod.snd_add, U2] at hu ⊢; omega
theorem ro1'_unit {z u : ℤ × ℤ} (hu : u ∈ unitVec) : ro1' r s (z + u) - ro1' r s z ∈ unitVec := by
  rw [unit_U2] at hu; rw [unit_sub]; simp only [ro1', Prod.fst_add, Prod.snd_add, U2] at hu ⊢; omega
theorem fi_unit {z u : ℤ × ℤ} (hu : u ∈ unitVec) : fi r s (z + u) - fi r s z ∈ unitVec := by
  rw [unit_U2] at hu; rw [unit_sub]; simp only [fi, Prod.fst_add, Prod.snd_add, U2] at hu ⊢; omega
theorem ps_unit {z u : ℤ × ℤ} (hu : u ∈ unitVec) : ps r s (z + u) - ps r s z ∈ unitVec := by
  rw [unit_U2] at hu; rw [unit_sub]; simp only [ps, Prod.fst_add, Prod.snd_add, U2] at hu ⊢; omega

theorem sg1_adj (hr : 1 ≤ r) (hs : 1 ≤ s) {v w : MV} (hv : Valid r s v) (hw : Valid r s w)
    (h : AdjM r s v w) : AdjM r s (sg1 r s v) (sg1 r s w) := by
  refine adjM_map (sg1 r s) (fun c z => if c = 0 then ro0 r s z else ro1 r s z)
    (fun v w hv hw e => by rw [← sg1'_sg1 hr hs hv, ← sg1'_sg1 hr hs hw, e])
    (fun v hv => sg1_valid hr hs hv) hr hs ?_ hv hw h
  intro c hc z hz
  rcases c_cases hc with rfl | rfl
  · refine ⟨0, by norm_num, ro0_H hz, sg1_ch0 hr hs hz, fun u hu hzu => ⟨ro0_unit hu, ro0_H hzu, sg1_ch0 hr hs hzu⟩⟩
  · refine ⟨1, by norm_num, ro1_H hz, sg1_ch1 hr hs hz, fun u hu hzu => ⟨ro1_unit hu, ro1_H hzu, sg1_ch1 hr hs hzu⟩⟩

theorem sg1'_adj (hr : 1 ≤ r) (hs : 1 ≤ s) {v w : MV} (hv : Valid r s v) (hw : Valid r s w)
    (h : AdjM r s v w) : AdjM r s (sg1' r s v) (sg1' r s w) := by
  refine adjM_map (sg1' r s) (fun c z => if c = 0 then ro0' r s z else ro1' r s z)
    (fun v w hv hw e => by rw [← sg1_sg1' hr hs hv, ← sg1_sg1' hr hs hw, e])
    (fun v hv => sg1'_valid hr hs hv) hr hs ?_ hv hw h
  intro c hc z hz
  rcases c_cases hc with rfl | rfl
  · refine ⟨0, by norm_num, ro0'_H hz, sg1'_ch0 hr hs hz, fun u hu hzu => ⟨ro0'_unit hu, ro0'_H hzu, sg1'_ch0 hr hs hzu⟩⟩
  · refine ⟨1, by norm_num, ro1'_H hz, sg1'_ch1 hr hs hz, fun u hu hzu => ⟨ro1'_unit hu, ro1'_H hzu, sg1'_ch1 hr hs hzu⟩⟩

theorem sg2_adj (hr : 1 ≤ r) (hs : 1 ≤ s) {v w : MV} (hv : Valid r s v) (hw : Valid r s w)
    (h : AdjM r s v w) : AdjM r s (sg2 r s v) (sg2 r s w) := by
  refine adjM_map (sg2 r s) (fun c z => if c = 0 then fi r s z else ps r s z)
    (fun v w hv hw e => by rw [← sg2_sg2 hr hs hv, ← sg2_sg2 hr hs hw, e])
    (fun v hv => sg2_valid hr hs hv) hr hs ?_ hv hw h
  intro c hc z hz
  rcases c_cases hc with rfl | rfl
  · refine ⟨1, by norm_num, fi_H hz, sg2_ch0 hr hs hz, fun u hu hzu => ⟨fi_unit (r := r) hu, fi_H hzu, sg2_ch0 hr hs hzu⟩⟩
  · refine ⟨0, by norm_num, ps_H hz, sg2_ch1 hr hs hz, fun u hu hzu => ⟨ps_unit (r := r) hu, ps_H hzu, sg2_ch1 hr hs hzu⟩⟩

/-- The rotation as a bijection of the model vertices. -/
def E1 (hr : 1 ≤ r) (hs : 1 ≤ s) : MS r s ≃ MS r s where
  toFun v := ⟨sg1 r s v.1, sg1_valid hr hs v.2⟩
  invFun v := ⟨sg1' r s v.1, sg1'_valid hr hs v.2⟩
  left_inv v := Subtype.ext (sg1'_sg1 hr hs v.2)
  right_inv v := Subtype.ext (sg1_sg1' hr hs v.2)

/-- The exchange of the cells as a bijection of the model vertices. -/
def E2 (hr : 1 ≤ r) (hs : 1 ≤ s) : MS r s ≃ MS r s where
  toFun v := ⟨sg2 r s v.1, sg2_valid hr hs v.2⟩
  invFun v := ⟨sg2 r s v.1, sg2_valid hr hs v.2⟩
  left_inv v := Subtype.ext (sg2_sg2 hr hs v.2)
  right_inv v := Subtype.ext (sg2_sg2 hr hs v.2)

theorem E1_adj (hr : 1 ≤ r) (hs : 1 ≤ s) (v w : MS r s) :
    (GM r s).Adj v w ↔ (GM r s).Adj (E1 hr hs v) (E1 hr hs w) := by
  constructor
  · exact fun h => sg1_adj hr hs v.2 w.2 h
  · intro h
    have := sg1'_adj hr hs (sg1_valid hr hs v.2) (sg1_valid hr hs w.2) h
    rwa [sg1'_sg1 hr hs v.2, sg1'_sg1 hr hs w.2] at this

theorem E2_adj (hr : 1 ≤ r) (hs : 1 ≤ s) (v w : MS r s) :
    (GM r s).Adj v w ↔ (GM r s).Adj (E2 hr hs v) (E2 hr hs w) := by
  constructor
  · exact fun h => sg2_adj hr hs v.2 w.2 h
  · intro h
    have := sg2_adj hr hs (sg2_valid hr hs v.2) (sg2_valid hr hs w.2) h
    rwa [sg2_sg2 hr hs v.2, sg2_sg2 hr hs w.2] at this

theorem lit_E1 (hr : 1 ≤ r) (hs : 1 ≤ s) {n : ℕ} {p : ℕ → MS r s} (hp : LiteralPath (GM r s) n p) :
    LiteralPath (GM r s) n (fun i => E1 hr hs (p i)) :=
  Claude4C1.literal_of_equiv (E1 hr hs) (E1_adj hr hs) hp

theorem lit_E2 (hr : 1 ≤ r) (hs : 1 ≤ s) {n : ℕ} {p : ℕ → MS r s} (hp : LiteralPath (GM r s) n p) :
    LiteralPath (GM r s) n (fun i => E2 hr hs (p i)) :=
  Claude4C1.literal_of_equiv (E2 hr hs) (E2_adj hr hs) hp

theorem sg1_seam (l : ℤ) (h : r + 2 * s ≤ l) : sg1 r s (2, (l, 0)) = (2, (l - r - 2 * s, 0)) := by
  simp only [sg1, show ((2 : ℤ) = 0) = False by decide, show ((2 : ℤ) = 1) = False by decide, if_false,
    sh1, if_pos h]

theorem sg2_seam : sg2 r s (2, (s, 0)) = (2, (0, 0)) := by
  simp only [sg2, show ((2 : ℤ) = 0) = False by decide, show ((2 : ℤ) = 1) = False by decide, if_false,
    sh2, le_refl, if_true, sub_self]

/-- **Moving the first corner to the label-0 point.** -/
theorem to_label0 (hr : 2 ≤ r) (hs : 2 ≤ s) {n : ℕ} {p : ℕ → MS r s} (hp : LiteralPath (GM r s) n p) :
    ∃ q : ℕ → MS r s, LiteralPath (GM r s) n q ∧ (q 0).1 = (2, (0, 0)) := by
  have hr1 : (1 : ℤ) ≤ r := by omega
  have hs1 : (1 : ℤ) ≤ s := by omega
  have hc := deg_five hr hs _ hp.2.2.2.2.2.1
  simp only [IsCorner, corners, List.mem_cons, List.not_mem_nil, or_false] at hc
  have k1 := lit_E1 hr1 hs1 hp
  have k2 := lit_E1 hr1 hs1 k1
  have k3 := lit_E1 hr1 hs1 k2
  have k4 := lit_E1 hr1 hs1 k3
  have k5 := lit_E1 hr1 hs1 k4
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨p, hp, h⟩
  · refine ⟨_, lit_E2 hr1 hs1 hp, ?_⟩
    show sg2 r s (p 0).1 = _; rw [h]; exact sg2_seam
  · refine ⟨_, k1, ?_⟩
    show sg1 r s (p 0).1 = _; rw [h, sg1_seam _ (by omega)]; congr 2; ring
  · refine ⟨_, lit_E2 hr1 hs1 k1, ?_⟩
    show sg2 r s (sg1 r s (p 0).1) = _; rw [h, sg1_seam _ (by omega), show r + 3 * s - r - 2 * s = s by ring]; exact sg2_seam
  · refine ⟨_, k2, ?_⟩
    show sg1 r s (sg1 r s (p 0).1) = _; rw [h, sg1_seam _ (by omega), sg1_seam _ (by omega)]; congr 2; ring
  · refine ⟨_, lit_E2 hr1 hs1 k2, ?_⟩
    show sg2 r s (sg1 r s (sg1 r s (p 0).1)) = _
    rw [h, sg1_seam _ (by omega), sg1_seam _ (by omega), show 2 * r + 5 * s - r - 2 * s - r - 2 * s = s by ring]; exact sg2_seam
  · refine ⟨_, k3, ?_⟩
    show sg1 r s (sg1 r s (sg1 r s (p 0).1)) = _
    rw [h, sg1_seam _ (by omega), sg1_seam _ (by omega), sg1_seam _ (by omega)]; congr 2; ring
  · refine ⟨_, lit_E2 hr1 hs1 k3, ?_⟩
    show sg2 r s (sg1 r s (sg1 r s (sg1 r s (p 0).1))) = _
    rw [h, sg1_seam _ (by omega), sg1_seam _ (by omega), sg1_seam _ (by omega),
      show 3 * r + 7 * s - r - 2 * s - r - 2 * s - r - 2 * s = s by ring]; exact sg2_seam
  · refine ⟨_, k4, ?_⟩
    show sg1 r s (sg1 r s (sg1 r s (sg1 r s (p 0).1))) = _
    rw [h, sg1_seam _ (by omega), sg1_seam _ (by omega), sg1_seam _ (by omega), sg1_seam _ (by omega)]; congr 2; ring
  · refine ⟨_, lit_E2 hr1 hs1 k4, ?_⟩
    show sg2 r s (sg1 r s (sg1 r s (sg1 r s (sg1 r s (p 0).1)))) = _
    rw [h, sg1_seam _ (by omega), sg1_seam _ (by omega), sg1_seam _ (by omega), sg1_seam _ (by omega),
      show 4 * r + 9 * s - r - 2 * s - r - 2 * s - r - 2 * s - r - 2 * s = s by ring]; exact sg2_seam
  · refine ⟨_, k5, ?_⟩
    show sg1 r s (sg1 r s (sg1 r s (sg1 r s (sg1 r s (p 0).1)))) = _
    rw [h, sg1_seam _ (by omega), sg1_seam _ (by omega), sg1_seam _ (by omega), sg1_seam _ (by omega),
      sg1_seam _ (by omega)]; congr 2; ring
  · refine ⟨_, lit_E2 hr1 hs1 k5, ?_⟩
    show sg2 r s (sg1 r s (sg1 r s (sg1 r s (sg1 r s (sg1 r s (p 0).1))))) = _
    rw [h, sg1_seam _ (by omega), sg1_seam _ (by omega), sg1_seam _ (by omega), sg1_seam _ (by omega),
      sg1_seam _ (by omega),
      show 5 * r + 11 * s - r - 2 * s - r - 2 * s - r - 2 * s - r - 2 * s - r - 2 * s = s by ring]
    exact sg2_seam

end Claude7D12
