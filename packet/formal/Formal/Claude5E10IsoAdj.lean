import Formal.Claude5E10IsoMain

/-!
# E10: adjacency under the transfer, and literal paths (`e10_iff_gm_of`)

Written by a Claude worker (2026-10-20, E10 bridge session).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

/-- A unit step of the tube chart is a unit step inside one sector. -/
theorem tube_step_sites (H : Hyp p r s w) {z u : ℤ × ℤ} (hz : HT p z) (hzu : HT p (z + u))
    (hu : u ∈ unitVec) : ∃ (f : Fin 5) (ζ : ℤ × ℤ), CD p r s f ζ ∧ CD p r s f (ζ + u) ∧
      Phi p r s w f ζ = ch p r s w 2 z ∧ Phi p r s w f (ζ + u) = ch p r s w 2 (z + u) := by
  have hr := H.hr; have hs := H.hs
  have us := unit_small hu
  obtain ⟨u1, u2⟩ := u
  obtain ⟨z1, z2⟩ := z
  simp only at us
  simp only [HT, Prod.mk_add_mk] at hz hzu
  have hu' := ht_unit hu
  simp only [ht] at hu'
  have hdec := emod_decomp (show 0 < 3 * (2 * r + s) by omega) z1
  set q := z1 / (3 * (2 * r + s))
  set x := z1 % (3 * (2 * r + s))
  have hrep : ∀ a b : ℤ, ch p r s w 2 (z1 + a, z2 + b) = ch p r s w 2 (x + a, z1 + z2 - x + b) := by
    intro a b
    have : ((z1 + a, z2 + b) : ℤ × ℤ) = (x + a, z1 + z2 - x + b) + q • per r s := by
      simp only [per, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
      constructor <;> linarith [hdec.1]
    rw [this, chT_shift]
  have h0 := hrep 0 0
  have hU := hrep u1 u2
  simp only [add_zero] at h0
  rw [show ((z1, z2) + (u1, u2) : ℤ × ℤ) = (z1 + u1, z2 + u2) by rfl, hU]
  rw [h0]
  -- choose the sector by the residue x (and the step)
  have hx := hdec.2
  rcases (show (0 ≤ x + u1 ∧ x + u1 ≤ 2 * r + s ∧ x ≤ 2 * r + s) ∨
      (2 * r + s ≤ x + u1 ∧ 2 * r + s ≤ x ∧ x + u1 ≤ 2 * (2 * r + s) ∧ x ≤ 2 * (2 * r + s)) ∨
      (2 * (2 * r + s) ≤ x + u1 ∧ 2 * (2 * r + s) ≤ x) ∨ (x = 0 ∧ u1 = -1) by omega)
    with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩
  · refine ⟨2, (x, z1 + z2 - x), ?_, ?_, ?_, ?_⟩
    · show SD p r s _; simp only [SD]; omega
    · show SD p r s _; simp only [SD, Prod.mk_add_mk]; omega
    · show ch p r s w 2 (_ + soff r s 2) = _; congr 1; ext <;> simp [soff] <;> ring_nf
    · show ch p r s w 2 (_ + soff r s 2) = _; congr 1; ext <;> simp [soff] <;> ring_nf
  · refine ⟨3, (x - (2 * r + s), z1 + z2 - x + (2 * r + s)), ?_, ?_, ?_, ?_⟩
    · show SD p r s _; simp only [SD]; omega
    · show SD p r s _; simp only [SD, Prod.mk_add_mk]; omega
    · show ch p r s w 2 (_ + soff r s 3) = _; congr 1; ext <;> simp [soff] <;> ring_nf
    · show ch p r s w 2 (_ + soff r s 3) = _; congr 1; ext <;> simp [soff] <;> ring_nf
  · refine ⟨4, (x - 2 * (2 * r + s), z1 + z2 - x + 2 * (2 * r + s)), ?_, ?_, ?_, ?_⟩
    · show SD p r s _; simp only [SD]; omega
    · show SD p r s _; simp only [SD, Prod.mk_add_mk]; omega
    · show ch p r s w 2 (_ + soff r s 4) = _; congr 1; ext <;> simp [soff] <;> ring_nf
    · show ch p r s w 2 (_ + soff r s 4) = _; congr 1; ext <;> simp [soff] <;> ring_nf
  · -- x = 0 and a step to the left: the right edge of the last sector
    refine ⟨4, (x + (2 * r + s), z1 + z2 - x - (2 * r + s)), ?_, ?_, ?_, ?_⟩
    · show SD p r s _; simp only [SD]; omega
    · show SD p r s _; simp only [SD, Prod.mk_add_mk]; omega
    · show ch p r s w 2 (_ + soff r s 4) = _
      rw [show ((x + (2 * r + s), z1 + z2 - x - (2 * r + s)) + soff r s 4 : ℤ × ℤ) =
        (x, z1 + z2 - x) + (1 : ℤ) • per r s by ext <;> simp [soff, per] <;> ring, chT_shift]
    · show ch p r s w 2 (_ + soff r s 4) = _
      rw [show ((x + (2 * r + s), z1 + z2 - x - (2 * r + s)) + (u1, u2) + soff r s 4 : ℤ × ℤ) =
        (x + u1, z1 + z2 - x + u2) + (1 : ℤ) • per r s by ext <;> simp [soff, per] <;> ring, chT_shift]

end Claude5E10
