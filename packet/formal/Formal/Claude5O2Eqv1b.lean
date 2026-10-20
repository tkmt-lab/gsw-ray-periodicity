import Formal.Claude5O2Eqv1

/-! O2: sites with the same model vertex, cells 2–3 (part 2; split from the generated file at a theorem boundary.) -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

variable {t d : ℤ}

theorem eqv_2_0 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (2 : Fin 8) z)
    (hw : (o2Sig t d).InCell (0 : Fin 8) w) (h : Phi t d 2 z = Phi t d 0 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((2 : Fin 8), z), hz⟩ ⟨((0 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_2, phi_0] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · obtain ⟨l, hl0, hl1, hl2, hl3⟩ := hc
    simp only [sp, Prod.ext_iff] at hl2 hl3
    refine Relation.EqvGen.rel _ _ ⟨0, 1, 3, _, gl_2_0, ?_⟩
    ext <;> simp [rotN, rot] <;> omega

theorem eqv_2_1 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (2 : Fin 8) z)
    (hw : (o2Sig t d).InCell (1 : Fin 8) w) (h : Phi t d 2 z = Phi t d 1 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((2 : Fin 8), z), hz⟩ ⟨((1 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_2, phi_1] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · obtain ⟨l, hl0, hl1, hl2, hl3⟩ := hc
    simp only [sp, Prod.ext_iff] at hl2 hl3
    refine Relation.EqvGen.rel _ _ ⟨2, 6, 3, _, gl_2_2, ?_⟩
    ext <;> simp [rotN, rot] <;> omega

theorem eqv_2_2 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (2 : Fin 8) z)
    (hw : (o2Sig t d).InCell (2 : Fin 8) w) (h : Phi t d 2 z = Phi t d 2 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((2 : Fin 8), z), hz⟩ ⟨((2 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_2, phi_2] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · have hzw : z = w := by simp [Prod.ext_iff] at hc2; ext <;> omega
    subst hzw; exact Relation.EqvGen.refl _
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_2_3 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (2 : Fin 8) z)
    (hw : (o2Sig t d).InCell (3 : Fin 8) w) (h : Phi t d 2 z = Phi t d 3 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((2 : Fin 8), z), hz⟩ ⟨((3 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_2, phi_3] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · refine Relation.EqvGen.rel _ _ ⟨1, 2, 5, _, gl_2_1, ?_⟩
    simp [Prod.ext_iff] at hc2; ext <;> simp [rotN, rot] <;> omega
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_2_4 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (2 : Fin 8) z)
    (hw : (o2Sig t d).InCell (4 : Fin 8) w) (h : Phi t d 2 z = Phi t d 4 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((2 : Fin 8), z), hz⟩ ⟨((4 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_2, phi_4] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_2_5 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (2 : Fin 8) z)
    (hw : (o2Sig t d).InCell (5 : Fin 8) w) (h : Phi t d 2 z = Phi t d 5 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((2 : Fin 8), z), hz⟩ ⟨((5 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_2, phi_5] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_2_6 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (2 : Fin 8) z)
    (hw : (o2Sig t d).InCell (6 : Fin 8) w) (h : Phi t d 2 z = Phi t d 6 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((2 : Fin 8), z), hz⟩ ⟨((6 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_2, phi_6] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_2_7 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (2 : Fin 8) z)
    (hw : (o2Sig t d).InCell (7 : Fin 8) w) (h : Phi t d 2 z = Phi t d 7 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((2 : Fin 8), z), hz⟩ ⟨((7 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_2, phi_7] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_3_0 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (3 : Fin 8) z)
    (hw : (o2Sig t d).InCell (0 : Fin 8) w) (h : Phi t d 3 z = Phi t d 0 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((3 : Fin 8), z), hz⟩ ⟨((0 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_3, phi_0] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · obtain ⟨l, hl0, hl1, hl2, hl3⟩ := hc
    simp only [sp, Prod.ext_iff] at hl2 hl3
    refine Relation.EqvGen.rel _ _ ⟨0, 0, 3, _, gl_3_0, ?_⟩
    ext <;> simp [rotN, rot] <;> omega

theorem eqv_3_1 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (3 : Fin 8) z)
    (hw : (o2Sig t d).InCell (1 : Fin 8) w) (h : Phi t d 3 z = Phi t d 1 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((3 : Fin 8), z), hz⟩ ⟨((1 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_3, phi_1] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · obtain ⟨l, hl0, hl1, hl2, hl3⟩ := hc
    simp only [sp, Prod.ext_iff] at hl2 hl3
    refine Relation.EqvGen.rel _ _ ⟨1, 7, 5, _, gl_3_1, ?_⟩
    ext <;> simp [rotN, rot] <;> omega

theorem eqv_3_2 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (3 : Fin 8) z)
    (hw : (o2Sig t d).InCell (2 : Fin 8) w) (h : Phi t d 3 z = Phi t d 2 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((3 : Fin 8), z), hz⟩ ⟨((2 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_3, phi_2] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · refine Relation.EqvGen.rel _ _ ⟨2, 1, 1, _, gl_3_2, ?_⟩
    simp [Prod.ext_iff] at hc2; ext <;> simp [rotN, rot] <;> omega
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_3_3 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (3 : Fin 8) z)
    (hw : (o2Sig t d).InCell (3 : Fin 8) w) (h : Phi t d 3 z = Phi t d 3 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((3 : Fin 8), z), hz⟩ ⟨((3 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_3, phi_3] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · have hzw : z = w := by simp [Prod.ext_iff] at hc2; ext <;> omega
    subst hzw; exact Relation.EqvGen.refl _
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_3_4 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (3 : Fin 8) z)
    (hw : (o2Sig t d).InCell (4 : Fin 8) w) (h : Phi t d 3 z = Phi t d 4 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((3 : Fin 8), z), hz⟩ ⟨((4 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_3, phi_4] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_3_5 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (3 : Fin 8) z)
    (hw : (o2Sig t d).InCell (5 : Fin 8) w) (h : Phi t d 3 z = Phi t d 5 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((3 : Fin 8), z), hz⟩ ⟨((5 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_3, phi_5] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_3_6 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (3 : Fin 8) z)
    (hw : (o2Sig t d).InCell (6 : Fin 8) w) (h : Phi t d 3 z = Phi t d 6 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((3 : Fin 8), z), hz⟩ ⟨((6 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_3, phi_6] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · simp [Tr] at hc

theorem eqv_3_7 (ht : 1 ≤ t) (hd : 1 ≤ d) (z w : ℤ × ℤ) (hz : (o2Sig t d).InCell (3 : Fin 8) z)
    (hw : (o2Sig t d).InCell (7 : Fin 8) w) (h : Phi t d 3 z = Phi t d 7 w) :
    Relation.EqvGen (o2Sig t d).SamePoint ⟨((3 : Fin 8), z), hz⟩ ⟨((7 : Fin 8), w), hw⟩ := by
  have hz' := (inCell_iff (by omega) (by omega) _ _).1 hz
  have hw' := (inCell_iff (by omega) (by omega) _ _).1 hw
  simp [CellIn, TriIn, Hx] at hz' hw'
  rw [phi_3, phi_7] at h
  have hc := ch_eq ht hd (by norm_num) (by norm_num) (by simp [Dom, Hx, Rh]; omega)
    (by simp [Dom, Hx, Rh]; omega) h
  rcases hc with ⟨hc1, hc2⟩ | hc | hc
  · simp at hc1
  · simp [Tr] at hc
  · simp [Tr] at hc

end Claude5O2
