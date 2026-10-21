import Formal.Claude5E10Suff2
import Formal.Claude5E10R0Ok
import Formal.Claude5E10R1Ok
import Formal.Claude5E10R2Ok
import Formal.Claude5E10R3Ok
import Formal.Claude5E10R4Ok
import Formal.Claude5E10R5Ok

/-!
# E10 model: the classification for `r ≥ 2`

Written by a Claude worker (2026-10-20, E10 bridge session).

With the twist `w = j m + k` (`0 ≤ k < m`, `j ∈ {0, 1, 2}`) and `p ≡ k (mod m)`, the model has a
literal path iff `k ∈ {1, r + 1, r + s + 1, m − 1, r − 1, r + s − 1}` (`model_classify`): the
paths go straight up the tube (`pathR`, `pathL`), and otherwise `k` lies in one of the six
regions whose line-state tables forbid literal paths.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

theorem wrap_val {x V : ℤ} (h : (x < 3 * (2 * r + s) ∧ x = V) ∨ (3 * (2 * r + s) ≤ x ∧ x - 3 * (2 * r + s) = V)) :
    wrap r s x = V := by
  unfold wrap; split_ifs <;> omega

theorem model_suff (H : Hyp p r s w) (hr2 : 2 ≤ r) {k j : ℤ} (hk0 : 0 ≤ k)
    (hk1 : k < 2 * r + s) (hj0 : 0 ≤ j) (hj2 : j ≤ 2) (hw : w = j * (2 * r + s) + k)
    (hpos : k = 1 ∨ k = r + 1 ∨ k = r + s + 1 ∨ k = 2 * r + s - 1 ∨ k = r - 1 ∨ k = r + s - 1) :
    ∃ n q, LiteralPath (GM p r s w) n q := by
  have hr := H.hr; have hs := H.hs
  have hP : 0 < 3 * (2 * r + s) := by omega
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, (J : ℤ) = j := ⟨j.toNat, by omega⟩
  have hJ2 : J ≤ 2 := by omega
  subst hJ
  interval_cases J <;> simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero] at hw <;>
    rcases hpos with h | h | h | h | h | h <;> subst h
  -- j = 0
  · exact pathR H (u₀ := 0) (a := 0) (by simp [IsArc]) (by simp [IsArc])
      ((wrap_val (V := 1) (by omega)).trans
        (emod_eq_of hP (q := 0) (b := 1) (by omega) (by omega) (by omega)).symm)
  · exact pathR H (u₀ := 2 * r + s) (a := r + s) (by simp [IsArc]) (by simp [IsArc])
      ((wrap_val (V := 2 * r + s + 1) (by omega)).trans
        (emod_eq_of hP (q := 0) (b := 2 * r + s + 1) (by omega) (by omega) (by omega)).symm)
  · exact pathR H (u₀ := r + s) (a := 0) (by simp [IsArc]) (by simp [IsArc])
      ((wrap_val (V := r + s + 1) (by omega)).trans
        (emod_eq_of hP (q := 0) (b := r + s + 1) (by omega) (by omega) (by omega)).symm)
  · exact pathL H hr2 (u₀ := 2 * r + s) (a := 0) (by simp [IsArc]) (by simp [IsArc])
      ((wrap_val (V := 2 * r + s - 1) (by omega)).trans
        (emod_eq_of hP (q := 0) (b := 2 * r + s - 1) (by omega) (by omega) (by omega)).symm)
  · exact pathL H hr2 (u₀ := 2 * r + s) (a := r + s) (by simp [IsArc]) (by simp [IsArc])
      ((wrap_val (V := 2 * r + s - 1) (by omega)).trans
        (emod_eq_of hP (q := 0) (b := 2 * r + s - 1) (by omega) (by omega) (by omega)).symm)
  · exact pathL H hr2 (u₀ := r + s) (a := 0) (by simp [IsArc]) (by simp [IsArc])
      ((wrap_val (V := r + s - 1) (by omega)).trans
        (emod_eq_of hP (q := 0) (b := r + s - 1) (by omega) (by omega) (by omega)).symm)
  -- j = 1
  · exact pathR H (u₀ := 2 * r + s) (a := 0) (by simp [IsArc]) (by simp [IsArc])
      ((wrap_val (V := 2 * r + s + 1) (by omega)).trans
        (emod_eq_of hP (q := 0) (b := 2 * r + s + 1) (by omega) (by omega) (by omega)).symm)
  · exact pathR H (u₀ := 4 * r + 2 * s) (a := r + s) (by simp [IsArc]) (by simp [IsArc])
      ((wrap_val (V := 4 * r + 2 * s + 1) (by omega)).trans
        (emod_eq_of hP (q := 0) (b := 4 * r + 2 * s + 1) (by omega) (by omega) (by omega)).symm)
  · exact pathR H (u₀ := 3 * r + 2 * s) (a := 0) (by simp [IsArc]) (by simp [IsArc])
      ((wrap_val (V := 3 * r + 2 * s + 1) (by omega)).trans
        (emod_eq_of hP (q := 0) (b := 3 * r + 2 * s + 1) (by omega) (by omega) (by omega)).symm)
  · exact pathL H hr2 (u₀ := 4 * r + 2 * s) (a := 0) (by simp [IsArc]) (by simp [IsArc])
      ((wrap_val (V := 4 * r + 2 * s - 1) (by omega)).trans
        (emod_eq_of hP (q := 0) (b := 4 * r + 2 * s - 1) (by omega) (by omega) (by omega)).symm)
  · exact pathL H hr2 (u₀ := 4 * r + 2 * s) (a := r + s) (by simp [IsArc]) (by simp [IsArc])
      ((wrap_val (V := 4 * r + 2 * s - 1) (by omega)).trans
        (emod_eq_of hP (q := 0) (b := 4 * r + 2 * s - 1) (by omega) (by omega) (by omega)).symm)
  · exact pathL H hr2 (u₀ := 3 * r + 2 * s) (a := 0) (by simp [IsArc]) (by simp [IsArc])
      ((wrap_val (V := 3 * r + 2 * s - 1) (by omega)).trans
        (emod_eq_of hP (q := 0) (b := 3 * r + 2 * s - 1) (by omega) (by omega) (by omega)).symm)
  -- j = 2
  · exact pathR H (u₀ := 4 * r + 2 * s) (a := 0) (by simp [IsArc]) (by simp [IsArc])
      ((wrap_val (V := 4 * r + 2 * s + 1) (by omega)).trans
        (emod_eq_of hP (q := 0) (b := 4 * r + 2 * s + 1) (by omega) (by omega) (by omega)).symm)
  · exact pathR H (u₀ := 0) (a := r + s) (by simp [IsArc]) (by simp [IsArc])
      ((wrap_val (V := 1) (by omega)).trans
        (emod_eq_of hP (q := 0) (b := 1) (by omega) (by omega) (by omega)).symm)
  · exact pathR H (u₀ := 5 * r + 3 * s) (a := 0) (by simp [IsArc]) (by simp [IsArc])
      ((wrap_val (V := 5 * r + 3 * s + 1) (by omega)).trans
        (emod_eq_of hP (q := 0) (b := 5 * r + 3 * s + 1) (by omega) (by omega) (by omega)).symm)
  · exact pathL H hr2 (u₀ := 0) (a := 0) (by simp [IsArc]) (by simp [IsArc])
      ((wrap_val (V := 6 * r + 3 * s - 1) (by omega)).trans
        (emod_eq_of hP (q := -1) (b := 6 * r + 3 * s - 1) (by omega) (by omega) (by omega)).symm)
  · exact pathL H hr2 (u₀ := 0) (a := r + s) (by simp [IsArc]) (by simp [IsArc])
      ((wrap_val (V := 6 * r + 3 * s - 1) (by omega)).trans
        (emod_eq_of hP (q := -1) (b := 6 * r + 3 * s - 1) (by omega) (by omega) (by omega)).symm)
  · exact pathL H hr2 (u₀ := 5 * r + 3 * s) (a := 0) (by simp [IsArc]) (by simp [IsArc])
      ((wrap_val (V := 5 * r + 3 * s - 1) (by omega)).trans
        (emod_eq_of hP (q := 0) (b := 5 * r + 3 * s - 1) (by omega) (by omega) (by omega)).symm)

theorem model_nec (H : Hyp p r s w) (hr2 : 2 ≤ r) {k j b : ℤ} (hk0 : 0 ≤ k)
    (hk1 : k < 2 * r + s) (hw : w = j * (2 * r + s) + k) (hp : p = k + (2 * r + s) * b)
    (hneg : ¬ (k = 1 ∨ k = r + 1 ∨ k = r + s + 1 ∨ k = 2 * r + s - 1 ∨ k = r - 1 ∨ k = r + s - 1))
    {n : ℕ} {q : ℕ → MS p r s} : ¬ LiteralPath (GM p r s w) n q := by
  have hs := H.hs
  have TW : Tw p r s w k := ⟨⟨j, by rw [hw]; ring⟩, ⟨b, hp⟩⟩
  have hdeg := deg_five_corner H
  by_cases h0 : k = 0
  · exact R0.no_path H TW ⟨hr2, hs, h0⟩ hdeg
  by_cases h1 : 2 ≤ k ∧ k ≤ r - 2
  · exact R1.no_path H TW ⟨hr2, hs, h1.1, h1.2⟩ hdeg
  by_cases h2 : k = r
  · exact R2.no_path H TW ⟨hr2, hs, h2, by omega⟩ hdeg
  by_cases h3 : r + 2 ≤ k ∧ k ≤ r + s - 2
  · exact R3.no_path H TW ⟨hr2, hs, h3.1, h3.2⟩ hdeg
  by_cases h4 : k = r + s
  · exact R4.no_path H TW ⟨hr2, hs, h4, by omega⟩ hdeg
  · exact R5.no_path H TW ⟨hr2, hs, by omega, by omega⟩ hdeg

/-- **Model classification** (`r ≥ 2`). -/
theorem model_classify (H : Hyp p r s w) (hr2 : 2 ≤ r) {k j b : ℤ} (hk0 : 0 ≤ k)
    (hk1 : k < 2 * r + s) (hj0 : 0 ≤ j) (hj2 : j ≤ 2) (hw : w = j * (2 * r + s) + k)
    (hp : p = k + (2 * r + s) * b) :
    (∃ n q, LiteralPath (GM p r s w) n q) ↔
      (k = 1 ∨ k = r + 1 ∨ k = r + s + 1 ∨ k = 2 * r + s - 1 ∨ k = r - 1 ∨ k = r + s - 1) := by
  constructor
  · rintro ⟨n, q, hq⟩
    by_contra hneg
    exact model_nec H hr2 hk0 hk1 hw hp hneg hq
  · exact model_suff H hr2 hk0 hk1 hj0 hj2 hw

end Claude5E10
