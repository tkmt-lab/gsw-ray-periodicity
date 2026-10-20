import Formal.Claude5O2DegGen

/-! O2 model: six neighbours on sheet-1 seams (part 2; split from the generated file at a theorem boundary.) -/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

variable {t d : ℤ}

theorem deg_S1_0_0 (ht : 2 ≤ t) (hd : 2 ≤ d) (v : MS t d) {ρ : ℤ × ℤ} (hρ : Hx t d ρ)
    (hc : ρ.2 = 0 ∧ 0 < ρ.1 ∧ ρ.1 < t) (hv : v.1 = ch t d 1 ρ) : deg (GM t d) v ≠ 5 := by
  have ht1 : (1 : ℤ) ≤ t := by omega
  have hd1 : (1 : ℤ) ≤ d := by omega
  obtain ⟨ρ1, ρ2⟩ := ρ
  simp only [Hx] at hρ hc
  have hvB : v.1 = ch t d (0 + 2) (ρ1, 0) := by
    rw [hv, chR_AD (z := (ρ1, 0)) ht1 hd1 (i := 0) (by norm_num) (by simp only) (by simp only; omega) (by simp only; omega)]
    congr 1; simp only [sp]; ext <;> simp only <;> omega
  refine deg_ne_five_of6 v (ch t d 1 ((ρ1, ρ2) + (1, 0))) (ch t d 1 ((ρ1, ρ2) + (-1, 0))) (ch t d 1 ((ρ1, ρ2) + (0, 1))) (ch t d 1 ((ρ1, ρ2) + (-1, 1))) (ch t d (0 + 2) ((ρ1, 0) + (0, 1))) (ch t d (0 + 2) ((ρ1, 0) + (-1, 1))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hvB
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hvB
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])

theorem deg_S1_0_1 (ht : 2 ≤ t) (hd : 2 ≤ d) (v : MS t d) {ρ : ℤ × ℤ} (hρ : Hx t d ρ)
    (hc : ρ.2 = 0 ∧ t < ρ.1 ∧ ρ.1 < 2 * t) (hv : v.1 = ch t d 1 ρ) : deg (GM t d) v ≠ 5 := by
  have ht1 : (1 : ℤ) ≤ t := by omega
  have hd1 : (1 : ℤ) ≤ d := by omega
  obtain ⟨ρ1, ρ2⟩ := ρ
  simp only [Hx] at hρ hc
  have hvB : v.1 = ch t d (0 + 2) (t, ρ1 - t) := by
    rw [hv, chR_DC (z := (t, ρ1 - t)) ht1 hd1 (i := 0) (by norm_num) (by simp only) (by simp only; omega) (by simp only; omega)]
    congr 1; simp only [sp]; ext <;> simp only <;> omega
  refine deg_ne_five_of6 v (ch t d 1 ((ρ1, ρ2) + (1, 0))) (ch t d 1 ((ρ1, ρ2) + (-1, 0))) (ch t d 1 ((ρ1, ρ2) + (0, 1))) (ch t d 1 ((ρ1, ρ2) + (-1, 1))) (ch t d (0 + 2) ((t, ρ1 - t) + (-1, 0))) (ch t d (0 + 2) ((t, ρ1 - t) + (-1, 1))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hvB
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hvB
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])

theorem deg_S1_1_0 (ht : 2 ≤ t) (hd : 2 ≤ d) (v : MS t d) {ρ : ℤ × ℤ} (hρ : Hx t d ρ)
    (hc : ρ.1 + ρ.2 = 2 * t + d ∧ 0 < (ρ.2 - d) ∧ (ρ.2 - d) < t) (hv : v.1 = ch t d 1 ρ) : deg (GM t d) v ≠ 5 := by
  have ht1 : (1 : ℤ) ≤ t := by omega
  have hd1 : (1 : ℤ) ≤ d := by omega
  obtain ⟨ρ1, ρ2⟩ := ρ
  simp only [Hx] at hρ hc
  have hvB : v.1 = ch t d (1 + 2) ((ρ2 - d), 0) := by
    rw [hv, chR_AD (z := ((ρ2 - d), 0)) ht1 hd1 (i := 1) (by norm_num) (by simp only) (by simp only; omega) (by simp only; omega)]
    congr 1; simp only [sp]; ext <;> simp only <;> omega
  refine deg_ne_five_of6 v (ch t d 1 ((ρ1, ρ2) + (-1, 1))) (ch t d 1 ((ρ1, ρ2) + (1, -1))) (ch t d 1 ((ρ1, ρ2) + (-1, 0))) (ch t d 1 ((ρ1, ρ2) + (0, -1))) (ch t d (1 + 2) (((ρ2 - d), 0) + (0, 1))) (ch t d (1 + 2) (((ρ2 - d), 0) + (-1, 1))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hvB
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hvB
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])

theorem deg_S1_1_1 (ht : 2 ≤ t) (hd : 2 ≤ d) (v : MS t d) {ρ : ℤ × ℤ} (hρ : Hx t d ρ)
    (hc : ρ.1 + ρ.2 = 2 * t + d ∧ t < (ρ.2 - d) ∧ (ρ.2 - d) < 2 * t) (hv : v.1 = ch t d 1 ρ) : deg (GM t d) v ≠ 5 := by
  have ht1 : (1 : ℤ) ≤ t := by omega
  have hd1 : (1 : ℤ) ≤ d := by omega
  obtain ⟨ρ1, ρ2⟩ := ρ
  simp only [Hx] at hρ hc
  have hvB : v.1 = ch t d (1 + 2) (t, (ρ2 - d) - t) := by
    rw [hv, chR_DC (z := (t, (ρ2 - d) - t)) ht1 hd1 (i := 1) (by norm_num) (by simp only) (by simp only; omega) (by simp only; omega)]
    congr 1; simp only [sp]; ext <;> simp only <;> omega
  refine deg_ne_five_of6 v (ch t d 1 ((ρ1, ρ2) + (-1, 1))) (ch t d 1 ((ρ1, ρ2) + (1, -1))) (ch t d 1 ((ρ1, ρ2) + (-1, 0))) (ch t d 1 ((ρ1, ρ2) + (0, -1))) (ch t d (1 + 2) ((t, (ρ2 - d) - t) + (-1, 0))) (ch t d (1 + 2) ((t, (ρ2 - d) - t) + (-1, 1))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hvB
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hvB
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])

theorem deg_S1_2_0 (ht : 2 ≤ t) (hd : 2 ≤ d) (v : MS t d) {ρ : ℤ × ℤ} (hρ : Hx t d ρ)
    (hc : ρ.1 = -d ∧ 0 < (2 * t + d - ρ.2) ∧ (2 * t + d - ρ.2) < t) (hv : v.1 = ch t d 1 ρ) : deg (GM t d) v ≠ 5 := by
  have ht1 : (1 : ℤ) ≤ t := by omega
  have hd1 : (1 : ℤ) ≤ d := by omega
  obtain ⟨ρ1, ρ2⟩ := ρ
  simp only [Hx] at hρ hc
  have hvB : v.1 = ch t d (2 + 2) ((2 * t + d - ρ2), 0) := by
    rw [hv, chR_AD (z := ((2 * t + d - ρ2), 0)) ht1 hd1 (i := 2) (by norm_num) (by simp only) (by simp only; omega) (by simp only; omega)]
    congr 1; simp only [sp]; ext <;> simp only <;> omega
  refine deg_ne_five_of6 v (ch t d 1 ((ρ1, ρ2) + (0, -1))) (ch t d 1 ((ρ1, ρ2) + (0, 1))) (ch t d 1 ((ρ1, ρ2) + (1, 0))) (ch t d 1 ((ρ1, ρ2) + (1, -1))) (ch t d (2 + 2) (((2 * t + d - ρ2), 0) + (0, 1))) (ch t d (2 + 2) (((2 * t + d - ρ2), 0) + (-1, 1))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hvB
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hvB
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])

theorem deg_S1_2_1 (ht : 2 ≤ t) (hd : 2 ≤ d) (v : MS t d) {ρ : ℤ × ℤ} (hρ : Hx t d ρ)
    (hc : ρ.1 = -d ∧ t < (2 * t + d - ρ.2) ∧ (2 * t + d - ρ.2) < 2 * t) (hv : v.1 = ch t d 1 ρ) : deg (GM t d) v ≠ 5 := by
  have ht1 : (1 : ℤ) ≤ t := by omega
  have hd1 : (1 : ℤ) ≤ d := by omega
  obtain ⟨ρ1, ρ2⟩ := ρ
  simp only [Hx] at hρ hc
  have hvB : v.1 = ch t d (2 + 2) (t, (2 * t + d - ρ2) - t) := by
    rw [hv, chR_DC (z := (t, (2 * t + d - ρ2) - t)) ht1 hd1 (i := 2) (by norm_num) (by simp only) (by simp only; omega) (by simp only; omega)]
    congr 1; simp only [sp]; ext <;> simp only <;> omega
  refine deg_ne_five_of6 v (ch t d 1 ((ρ1, ρ2) + (0, -1))) (ch t d 1 ((ρ1, ρ2) + (0, 1))) (ch t d 1 ((ρ1, ρ2) + (1, 0))) (ch t d 1 ((ρ1, ρ2) + (1, -1))) (ch t d (2 + 2) ((t, (2 * t + d - ρ2) - t) + (-1, 0))) (ch t d (2 + 2) ((t, (2 * t + d - ρ2) - t) + (-1, 1))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact ch_valid ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega)
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hv
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hvB
  · exact adj_of_unit ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [unit_iff]) hvB
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_1R ht1 hd1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk_add_mk, Prod.ext_iff, ne_eq, not_and] at he ⊢; omega)
  · exact ne_same ht1 (by norm_num) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Dom, Hx, Rh] <;> omega) (by simp [Prod.ext_iff])

end Claude5O2
