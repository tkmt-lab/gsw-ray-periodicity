import Formal.Claude5O2Phi

/-! O2: invariance under the gluings, cells 2–7 (part 2; split from the generated file at a theorem boundary.) -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

variable {t d : ℤ}

set_option maxHeartbeats 4000000 in
theorem samePoint_phi_2 (ht : 1 ≤ t) (hd : 1 ≤ d) (f : Fin 8) (z w : ℤ × ℤ)
    (hz : CellIn t d 2 z) (hw : CellIn t d f w) (i j m : ℕ) (τ : ℤ × ℤ)
    (hG : (o2Sig t d).Glue (2 : Fin 8) i f j m τ) (hzw : rotN m z + τ = w) :
    Phi t d 2 z = Phi t d f w := by
  have hm := glue_cases hG
  obtain ⟨-, -, -, -, h3, h4⟩ := hG
  simp only [o2GlueTable, List.map_cons, List.map_nil, List.mem_cons, Prod.mk.injEq, Fin.isValue,
    Fin.reduceEq, true_and, false_and, false_or, List.not_mem_nil, or_false] at hm
  rw [rotN_mod6] at h3 h4 hzw
  have hm6 : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize m % 6 = k at h3 h4 hzw hm6
  simp [CellIn, TriIn, Hx] at hz
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [CellIn, TriIn, Hx] at hw
  · interval_cases k <;> simp only [rotN, rot, Sig.pt, o2Sig, o2Poly, walk, Prod.ext_iff, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.length_cons, List.length_nil] at h3 h4 hzw <;>
      norm_num at h3 h4 hzw <;> (try omega)
    rw [phi_2, phi_0, chR_BC2 ht (i := 0) rfl ?_ ?_]
    · ph_close
    · omega
    · omega
  · interval_cases k <;> simp only [rotN, rot, Sig.pt, o2Sig, o2Poly, walk, Prod.ext_iff, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.length_cons, List.length_nil] at h3 h4 hzw <;>
      norm_num at h3 h4 hzw <;> (try omega)
    rw [phi_2, phi_3]
    · ph_close
  · interval_cases k <;> simp only [rotN, rot, Sig.pt, o2Sig, o2Poly, walk, Prod.ext_iff, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.length_cons, List.length_nil] at h3 h4 hzw <;>
      norm_num at h3 h4 hzw <;> (try omega)
    rw [phi_2, phi_1, chR_DC2 ht hd (i := 0) (by norm_num) rfl ?_ ?_ ?_]
    · ph_close
    · omega
    · omega
    · omega

set_option maxHeartbeats 4000000 in
theorem samePoint_phi_3 (ht : 1 ≤ t) (hd : 1 ≤ d) (f : Fin 8) (z w : ℤ × ℤ)
    (hz : CellIn t d 3 z) (hw : CellIn t d f w) (i j m : ℕ) (τ : ℤ × ℤ)
    (hG : (o2Sig t d).Glue (3 : Fin 8) i f j m τ) (hzw : rotN m z + τ = w) :
    Phi t d 3 z = Phi t d f w := by
  have hm := glue_cases hG
  obtain ⟨-, -, -, -, h3, h4⟩ := hG
  simp only [o2GlueTable, List.map_cons, List.map_nil, List.mem_cons, Prod.mk.injEq, Fin.isValue,
    Fin.reduceEq, true_and, false_and, false_or, List.not_mem_nil, or_false] at hm
  rw [rotN_mod6] at h3 h4 hzw
  have hm6 : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize m % 6 = k at h3 h4 hzw hm6
  simp [CellIn, TriIn, Hx] at hz
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [CellIn, TriIn, Hx] at hw
  · interval_cases k <;> simp only [rotN, rot, Sig.pt, o2Sig, o2Poly, walk, Prod.ext_iff, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.length_cons, List.length_nil] at h3 h4 hzw <;>
      norm_num at h3 h4 hzw <;> (try omega)
    rw [phi_3, phi_0, chR_AB2 ht (i := 0) rfl ?_]
    · ph_close
    · omega
  · interval_cases k <;> simp only [rotN, rot, Sig.pt, o2Sig, o2Poly, walk, Prod.ext_iff, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.length_cons, List.length_nil] at h3 h4 hzw <;>
      norm_num at h3 h4 hzw <;> (try omega)
    rw [phi_3, phi_1, chR_AD2 ht hd (i := 0) (by norm_num) rfl ?_ ?_ ?_]
    · ph_close
    · omega
    · omega
    · omega
  · interval_cases k <;> simp only [rotN, rot, Sig.pt, o2Sig, o2Poly, walk, Prod.ext_iff, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.length_cons, List.length_nil] at h3 h4 hzw <;>
      norm_num at h3 h4 hzw <;> (try omega)
    rw [phi_3, phi_2]
    · ph_close

set_option maxHeartbeats 4000000 in
theorem samePoint_phi_4 (ht : 1 ≤ t) (hd : 1 ≤ d) (f : Fin 8) (z w : ℤ × ℤ)
    (hz : CellIn t d 4 z) (hw : CellIn t d f w) (i j m : ℕ) (τ : ℤ × ℤ)
    (hG : (o2Sig t d).Glue (4 : Fin 8) i f j m τ) (hzw : rotN m z + τ = w) :
    Phi t d 4 z = Phi t d f w := by
  have hm := glue_cases hG
  obtain ⟨-, -, -, -, h3, h4⟩ := hG
  simp only [o2GlueTable, List.map_cons, List.map_nil, List.mem_cons, Prod.mk.injEq, Fin.isValue,
    Fin.reduceEq, true_and, false_and, false_or, List.not_mem_nil, or_false] at hm
  rw [rotN_mod6] at h3 h4 hzw
  have hm6 : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize m % 6 = k at h3 h4 hzw hm6
  simp [CellIn, TriIn, Hx] at hz
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [CellIn, TriIn, Hx] at hw
  · interval_cases k <;> simp only [rotN, rot, Sig.pt, o2Sig, o2Poly, walk, Prod.ext_iff, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.length_cons, List.length_nil] at h3 h4 hzw <;>
      norm_num at h3 h4 hzw <;> (try omega)
    rw [phi_4, phi_0, chR_BC2 ht (i := 1) rfl ?_ ?_]
    · ph_close
    · omega
    · omega
  · interval_cases k <;> simp only [rotN, rot, Sig.pt, o2Sig, o2Poly, walk, Prod.ext_iff, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.length_cons, List.length_nil] at h3 h4 hzw <;>
      norm_num at h3 h4 hzw <;> (try omega)
    rw [phi_4, phi_5]
    · ph_close
  · interval_cases k <;> simp only [rotN, rot, Sig.pt, o2Sig, o2Poly, walk, Prod.ext_iff, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.length_cons, List.length_nil] at h3 h4 hzw <;>
      norm_num at h3 h4 hzw <;> (try omega)
    rw [phi_4, phi_1, chR_DC2 ht hd (i := 1) (by norm_num) rfl ?_ ?_ ?_]
    · ph_close
    · omega
    · omega
    · omega

set_option maxHeartbeats 4000000 in
theorem samePoint_phi_5 (ht : 1 ≤ t) (hd : 1 ≤ d) (f : Fin 8) (z w : ℤ × ℤ)
    (hz : CellIn t d 5 z) (hw : CellIn t d f w) (i j m : ℕ) (τ : ℤ × ℤ)
    (hG : (o2Sig t d).Glue (5 : Fin 8) i f j m τ) (hzw : rotN m z + τ = w) :
    Phi t d 5 z = Phi t d f w := by
  have hm := glue_cases hG
  obtain ⟨-, -, -, -, h3, h4⟩ := hG
  simp only [o2GlueTable, List.map_cons, List.map_nil, List.mem_cons, Prod.mk.injEq, Fin.isValue,
    Fin.reduceEq, true_and, false_and, false_or, List.not_mem_nil, or_false] at hm
  rw [rotN_mod6] at h3 h4 hzw
  have hm6 : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize m % 6 = k at h3 h4 hzw hm6
  simp [CellIn, TriIn, Hx] at hz
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [CellIn, TriIn, Hx] at hw
  · interval_cases k <;> simp only [rotN, rot, Sig.pt, o2Sig, o2Poly, walk, Prod.ext_iff, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.length_cons, List.length_nil] at h3 h4 hzw <;>
      norm_num at h3 h4 hzw <;> (try omega)
    rw [phi_5, phi_0, chR_AB2 ht (i := 1) rfl ?_]
    · ph_close
    · omega
  · interval_cases k <;> simp only [rotN, rot, Sig.pt, o2Sig, o2Poly, walk, Prod.ext_iff, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.length_cons, List.length_nil] at h3 h4 hzw <;>
      norm_num at h3 h4 hzw <;> (try omega)
    rw [phi_5, phi_1, chR_AD2 ht hd (i := 1) (by norm_num) rfl ?_ ?_ ?_]
    · ph_close
    · omega
    · omega
    · omega
  · interval_cases k <;> simp only [rotN, rot, Sig.pt, o2Sig, o2Poly, walk, Prod.ext_iff, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.length_cons, List.length_nil] at h3 h4 hzw <;>
      norm_num at h3 h4 hzw <;> (try omega)
    rw [phi_5, phi_4]
    · ph_close

set_option maxHeartbeats 4000000 in
theorem samePoint_phi_6 (ht : 1 ≤ t) (hd : 1 ≤ d) (f : Fin 8) (z w : ℤ × ℤ)
    (hz : CellIn t d 6 z) (hw : CellIn t d f w) (i j m : ℕ) (τ : ℤ × ℤ)
    (hG : (o2Sig t d).Glue (6 : Fin 8) i f j m τ) (hzw : rotN m z + τ = w) :
    Phi t d 6 z = Phi t d f w := by
  have hm := glue_cases hG
  obtain ⟨-, -, -, -, h3, h4⟩ := hG
  simp only [o2GlueTable, List.map_cons, List.map_nil, List.mem_cons, Prod.mk.injEq, Fin.isValue,
    Fin.reduceEq, true_and, false_and, false_or, List.not_mem_nil, or_false] at hm
  rw [rotN_mod6] at h3 h4 hzw
  have hm6 : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize m % 6 = k at h3 h4 hzw hm6
  simp [CellIn, TriIn, Hx] at hz
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [CellIn, TriIn, Hx] at hw
  · interval_cases k <;> simp only [rotN, rot, Sig.pt, o2Sig, o2Poly, walk, Prod.ext_iff, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.length_cons, List.length_nil] at h3 h4 hzw <;>
      norm_num at h3 h4 hzw <;> (try omega)
    rw [phi_6, phi_0, chR_BC2 ht (i := 2) rfl ?_ ?_]
    · ph_close
    · omega
    · omega
  · interval_cases k <;> simp only [rotN, rot, Sig.pt, o2Sig, o2Poly, walk, Prod.ext_iff, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.length_cons, List.length_nil] at h3 h4 hzw <;>
      norm_num at h3 h4 hzw <;> (try omega)
    rw [phi_6, phi_7]
    · ph_close
  · interval_cases k <;> simp only [rotN, rot, Sig.pt, o2Sig, o2Poly, walk, Prod.ext_iff, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.length_cons, List.length_nil] at h3 h4 hzw <;>
      norm_num at h3 h4 hzw <;> (try omega)
    rw [phi_6, phi_1, chR_DC2 ht hd (i := 2) (by norm_num) rfl ?_ ?_ ?_]
    · ph_close
    · omega
    · omega
    · omega

set_option maxHeartbeats 4000000 in
theorem samePoint_phi_7 (ht : 1 ≤ t) (hd : 1 ≤ d) (f : Fin 8) (z w : ℤ × ℤ)
    (hz : CellIn t d 7 z) (hw : CellIn t d f w) (i j m : ℕ) (τ : ℤ × ℤ)
    (hG : (o2Sig t d).Glue (7 : Fin 8) i f j m τ) (hzw : rotN m z + τ = w) :
    Phi t d 7 z = Phi t d f w := by
  have hm := glue_cases hG
  obtain ⟨-, -, -, -, h3, h4⟩ := hG
  simp only [o2GlueTable, List.map_cons, List.map_nil, List.mem_cons, Prod.mk.injEq, Fin.isValue,
    Fin.reduceEq, true_and, false_and, false_or, List.not_mem_nil, or_false] at hm
  rw [rotN_mod6] at h3 h4 hzw
  have hm6 : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize m % 6 = k at h3 h4 hzw hm6
  simp [CellIn, TriIn, Hx] at hz
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [CellIn, TriIn, Hx] at hw
  · interval_cases k <;> simp only [rotN, rot, Sig.pt, o2Sig, o2Poly, walk, Prod.ext_iff, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.length_cons, List.length_nil] at h3 h4 hzw <;>
      norm_num at h3 h4 hzw <;> (try omega)
    rw [phi_7, phi_0, chR_AB2 ht (i := 2) rfl ?_]
    · ph_close
    · omega
  · interval_cases k <;> simp only [rotN, rot, Sig.pt, o2Sig, o2Poly, walk, Prod.ext_iff, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.length_cons, List.length_nil] at h3 h4 hzw <;>
      norm_num at h3 h4 hzw <;> (try omega)
    rw [phi_7, phi_1, chR_AD2 ht hd (i := 2) (by norm_num) rfl ?_ ?_ ?_]
    · ph_close
    · omega
    · omega
    · omega
  · interval_cases k <;> simp only [rotN, rot, Sig.pt, o2Sig, o2Poly, walk, Prod.ext_iff, Fin.isValue,
      Fin.val_zero, Fin.val_one, Fin.val_two, List.length_cons, List.length_nil] at h3 h4 hzw <;>
      norm_num at h3 h4 hzw <;> (try omega)
    rw [phi_7, phi_6]
    · ph_close

theorem samePoint_phi (ht : 1 ≤ t) (hd : 1 ≤ d) (s s' : (o2Sig t d).Site)
    (h : (o2Sig t d).SamePoint s s') : Phi t d s.1.1 s.1.2 = Phi t d s'.1.1 s'.1.2 := by
  obtain ⟨⟨g, z⟩, hz⟩ := s
  obtain ⟨⟨f, w⟩, hw⟩ := s'
  obtain ⟨i, j, m, τ, hG, hzw⟩ := h
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp only at hG hzw hz' hw' ⊢
  fin_cases g
  · exact samePoint_phi_0 ht hd f z w hz' hw' i j m τ hG hzw
  · exact samePoint_phi_1 ht hd f z w hz' hw' i j m τ hG hzw
  · exact samePoint_phi_2 ht hd f z w hz' hw' i j m τ hG hzw
  · exact samePoint_phi_3 ht hd f z w hz' hw' i j m τ hG hzw
  · exact samePoint_phi_4 ht hd f z w hz' hw' i j m τ hG hzw
  · exact samePoint_phi_5 ht hd f z w hz' hw' i j m τ hG hzw
  · exact samePoint_phi_6 ht hd f z w hz' hw' i j m τ hG hzw
  · exact samePoint_phi_7 ht hd f z w hz' hw' i j m τ hG hzw

end Claude5O2
