import Formal.Claude5O2Eqv2

/-! O2: sites with the same model vertex, cells 6–7 (part 2; split from the generated file at a theorem boundary.) -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

variable {t d : ℤ}

theorem eqv_6_0 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (6 : Fin 8) z)
    (hw : (o2Sig t d).InCell (0 : Fin 8) w) (h : Phi t d 6 z = Phi t d 0 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((6 : Fin 8), z), hz⟩ ⟨((0 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_6, phi_0] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · obtain ⟨l, hl0, hl1, hl2, hl3⟩ := hc
    simp only [sp, Prod.ext_iff] at hl2 hl3
    refine Relation.EqvGen.rel _ _ ⟨0, 7, 1, _, gl_6_0, ?_⟩
    ext <;> simp [rotN, rot] <;> omega

theorem eqv_6_1 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (6 : Fin 8) z)
    (hw : (o2Sig t d).InCell (1 : Fin 8) w) (h : Phi t d 6 z = Phi t d 1 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((6 : Fin 8), z), hz⟩ ⟨((1 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_6, phi_1] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · obtain ⟨l, hl0, hl1, hl2, hl3⟩ := hc
    simp only [sp, Prod.ext_iff] at hl2 hl3
    refine Relation.EqvGen.rel _ _ ⟨2, 0, 5, _, gl_6_2, ?_⟩
    ext <;> simp [rotN, rot] <;> omega

theorem eqv_6_2 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (6 : Fin 8) z)
    (hw : (o2Sig t d).InCell (2 : Fin 8) w) (h : Phi t d 6 z = Phi t d 2 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((6 : Fin 8), z), hz⟩ ⟨((2 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_6, phi_2] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_6_3 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (6 : Fin 8) z)
    (hw : (o2Sig t d).InCell (3 : Fin 8) w) (h : Phi t d 6 z = Phi t d 3 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((6 : Fin 8), z), hz⟩ ⟨((3 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_6, phi_3] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_6_4 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (6 : Fin 8) z)
    (hw : (o2Sig t d).InCell (4 : Fin 8) w) (h : Phi t d 6 z = Phi t d 4 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((6 : Fin 8), z), hz⟩ ⟨((4 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_6, phi_4] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_6_5 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (6 : Fin 8) z)
    (hw : (o2Sig t d).InCell (5 : Fin 8) w) (h : Phi t d 6 z = Phi t d 5 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((6 : Fin 8), z), hz⟩ ⟨((5 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_6, phi_5] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_6_6 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (6 : Fin 8) z)
    (hw : (o2Sig t d).InCell (6 : Fin 8) w) (h : Phi t d 6 z = Phi t d 6 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((6 : Fin 8), z), hz⟩ ⟨((6 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_6, phi_6] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · have hzw : z = w := by simp [Prod.ext_iff] at hc2; ext <;> omega
    subst hzw; exact Relation.EqvGen.refl _
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_6_7 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (6 : Fin 8) z)
    (hw : (o2Sig t d).InCell (7 : Fin 8) w) (h : Phi t d 6 z = Phi t d 7 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((6 : Fin 8), z), hz⟩ ⟨((7 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_6, phi_7] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · refine Relation.EqvGen.rel _ _ ⟨1, 2, 5, _, gl_6_1, ?_⟩
    simp [Prod.ext_iff] at hc2; ext <;> simp [rotN, rot] <;> omega
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_7_0 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (7 : Fin 8) z)
    (hw : (o2Sig t d).InCell (0 : Fin 8) w) (h : Phi t d 7 z = Phi t d 0 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((7 : Fin 8), z), hz⟩ ⟨((0 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_7, phi_0] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · obtain ⟨l, hl0, hl1, hl2, hl3⟩ := hc
    simp only [sp, Prod.ext_iff] at hl2 hl3
    refine Relation.EqvGen.rel _ _ ⟨0, 6, 1, _, gl_7_0, ?_⟩
    ext <;> simp [rotN, rot] <;> omega

theorem eqv_7_1 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (7 : Fin 8) z)
    (hw : (o2Sig t d).InCell (1 : Fin 8) w) (h : Phi t d 7 z = Phi t d 1 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((7 : Fin 8), z), hz⟩ ⟨((1 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_7, phi_1] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · obtain ⟨l, hl0, hl1, hl2, hl3⟩ := hc
    simp only [sp, Prod.ext_iff] at hl2 hl3
    refine Relation.EqvGen.rel _ _ ⟨1, 1, 1, _, gl_7_1, ?_⟩
    ext <;> simp [rotN, rot] <;> omega

theorem eqv_7_2 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (7 : Fin 8) z)
    (hw : (o2Sig t d).InCell (2 : Fin 8) w) (h : Phi t d 7 z = Phi t d 2 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((7 : Fin 8), z), hz⟩ ⟨((2 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_7, phi_2] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_7_3 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (7 : Fin 8) z)
    (hw : (o2Sig t d).InCell (3 : Fin 8) w) (h : Phi t d 7 z = Phi t d 3 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((7 : Fin 8), z), hz⟩ ⟨((3 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_7, phi_3] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_7_4 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (7 : Fin 8) z)
    (hw : (o2Sig t d).InCell (4 : Fin 8) w) (h : Phi t d 7 z = Phi t d 4 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((7 : Fin 8), z), hz⟩ ⟨((4 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_7, phi_4] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_7_5 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (7 : Fin 8) z)
    (hw : (o2Sig t d).InCell (5 : Fin 8) w) (h : Phi t d 7 z = Phi t d 5 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((7 : Fin 8), z), hz⟩ ⟨((5 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_7, phi_5] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_7_6 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (7 : Fin 8) z)
    (hw : (o2Sig t d).InCell (6 : Fin 8) w) (h : Phi t d 7 z = Phi t d 6 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((7 : Fin 8), z), hz⟩ ⟨((6 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_7, phi_6] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · refine Relation.EqvGen.rel _ _ ⟨2, 1, 1, _, gl_7_2, ?_⟩
    simp [Prod.ext_iff] at hc2; ext <;> simp [rotN, rot] <;> omega
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_7_7 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (7 : Fin 8) z)
    (hw : (o2Sig t d).InCell (7 : Fin 8) w) (h : Phi t d 7 z = Phi t d 7 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((7 : Fin 8), z), hz⟩ ⟨((7 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_7, phi_7] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · have hzw : z = w := by simp [Prod.ext_iff] at hc2; ext <;> omega
    subst hzw; exact Relation.EqvGen.refl _
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_of_phi (ht : 1 ≤ t) (hd : 1 ≤ d) (a b : (o2Sig t d).Site)
    (h : Phi t d a.1.1 a.1.2 = Phi t d b.1.1 b.1.2) : Relation.EqvGen (o2Sig t d).SamePoint a b := by
  obtain ⟨⟨g, z⟩, hz⟩ := a
  obtain ⟨⟨f, w⟩, hw⟩ := b
  simp only at h
  fin_cases g <;> fin_cases f
  · exact eqv_0_0 ht hd z w hz hw h
  · exact eqv_0_1 ht hd z w hz hw h
  · exact eqv_0_2 ht hd z w hz hw h
  · exact eqv_0_3 ht hd z w hz hw h
  · exact eqv_0_4 ht hd z w hz hw h
  · exact eqv_0_5 ht hd z w hz hw h
  · exact eqv_0_6 ht hd z w hz hw h
  · exact eqv_0_7 ht hd z w hz hw h
  · exact eqv_1_0 ht hd z w hz hw h
  · exact eqv_1_1 ht hd z w hz hw h
  · exact eqv_1_2 ht hd z w hz hw h
  · exact eqv_1_3 ht hd z w hz hw h
  · exact eqv_1_4 ht hd z w hz hw h
  · exact eqv_1_5 ht hd z w hz hw h
  · exact eqv_1_6 ht hd z w hz hw h
  · exact eqv_1_7 ht hd z w hz hw h
  · exact eqv_2_0 ht hd z w hz hw h
  · exact eqv_2_1 ht hd z w hz hw h
  · exact eqv_2_2 ht hd z w hz hw h
  · exact eqv_2_3 ht hd z w hz hw h
  · exact eqv_2_4 ht hd z w hz hw h
  · exact eqv_2_5 ht hd z w hz hw h
  · exact eqv_2_6 ht hd z w hz hw h
  · exact eqv_2_7 ht hd z w hz hw h
  · exact eqv_3_0 ht hd z w hz hw h
  · exact eqv_3_1 ht hd z w hz hw h
  · exact eqv_3_2 ht hd z w hz hw h
  · exact eqv_3_3 ht hd z w hz hw h
  · exact eqv_3_4 ht hd z w hz hw h
  · exact eqv_3_5 ht hd z w hz hw h
  · exact eqv_3_6 ht hd z w hz hw h
  · exact eqv_3_7 ht hd z w hz hw h
  · exact eqv_4_0 ht hd z w hz hw h
  · exact eqv_4_1 ht hd z w hz hw h
  · exact eqv_4_2 ht hd z w hz hw h
  · exact eqv_4_3 ht hd z w hz hw h
  · exact eqv_4_4 ht hd z w hz hw h
  · exact eqv_4_5 ht hd z w hz hw h
  · exact eqv_4_6 ht hd z w hz hw h
  · exact eqv_4_7 ht hd z w hz hw h
  · exact eqv_5_0 ht hd z w hz hw h
  · exact eqv_5_1 ht hd z w hz hw h
  · exact eqv_5_2 ht hd z w hz hw h
  · exact eqv_5_3 ht hd z w hz hw h
  · exact eqv_5_4 ht hd z w hz hw h
  · exact eqv_5_5 ht hd z w hz hw h
  · exact eqv_5_6 ht hd z w hz hw h
  · exact eqv_5_7 ht hd z w hz hw h
  · exact eqv_6_0 ht hd z w hz hw h
  · exact eqv_6_1 ht hd z w hz hw h
  · exact eqv_6_2 ht hd z w hz hw h
  · exact eqv_6_3 ht hd z w hz hw h
  · exact eqv_6_4 ht hd z w hz hw h
  · exact eqv_6_5 ht hd z w hz hw h
  · exact eqv_6_6 ht hd z w hz hw h
  · exact eqv_6_7 ht hd z w hz hw h
  · exact eqv_7_0 ht hd z w hz hw h
  · exact eqv_7_1 ht hd z w hz hw h
  · exact eqv_7_2 ht hd z w hz hw h
  · exact eqv_7_3 ht hd z w hz hw h
  · exact eqv_7_4 ht hd z w hz hw h
  · exact eqv_7_5 ht hd z w hz hw h
  · exact eqv_7_6 ht hd z w hz hw h
  · exact eqv_7_7 ht hd z w hz hw h

end Claude5O2
