import Formal.Claude5E10IsoAdj2

/-!
# E10: tools for the generated case-by-case transfer proofs

Written by a Claude worker (2026-10-20, E10 bridge session).

* `ph_LS`, `ph_US`, `ph_SS` : a gluing that carries a cap side (resp. a sector edge) onto a
  sector edge preserves `Phi` when the two tube chart points differ by a period;
* `cpt_sec_lt`, `cpt_sec_eq` : the canonical point of a sector point;
* `eqv_of_val` : equal sites are related.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

theorem phi_cap0 (z : ℤ × ℤ) : Phi p r s w 0 z = ch p r s w 0 z := by simp [Phi]
theorem phi_cap1 (z : ℤ × ℤ) : Phi p r s w 1 z = ch p r s w 1 z := by simp [Phi]
theorem phi_sec {f : Fin 5} (hf : 2 ≤ f.val) (z : ℤ × ℤ) :
    Phi p r s w f z = ch p r s w 2 (z + soff r s f) := by
  simp [Phi, show f.val ≠ 0 by omega, show f.val ≠ 1 by omega]

theorem ph_LS (H : Hyp p r s w) {i : ℕ} (hi : i < 6) {f : Fin 5} (hf : 2 ≤ f.val) {z z' : ℤ × ℤ}
    (hz : HL r s z) (hs : OnSide r s 0 i z) (t : ℤ)
    (he : z' + soff r s f = gmap p r s w 0 i z + t • per r s) :
    Phi p r s w 0 z = Phi p r s w f z' := by
  rw [phi_cap0, phi_sec hf, he, chT_shift, (gmapL_ch H hi hz hs).1]

theorem ph_US (H : Hyp p r s w) {i : ℕ} (hi : i < 6) {f : Fin 5} (hf : 2 ≤ f.val) {z z' : ℤ × ℤ}
    (hz : HU r s z) (hs : OnSide r s 1 i z) (t : ℤ)
    (he : z' + soff r s f = gmap p r s w 1 i z + t • per r s) :
    Phi p r s w 1 z = Phi p r s w f z' := by
  rw [phi_cap1, phi_sec hf, he, chT_shift, (gmapU_ch H hi hz hs).1]

theorem ph_SS {f f' : Fin 5} (hf : 2 ≤ f.val) (hf' : 2 ≤ f'.val) {z z' : ℤ × ℤ} (t : ℤ)
    (he : z' + soff r s f' = z + soff r s f + t • per r s) :
    Phi p r s w f z = Phi p r s w f' z' := by
  rw [phi_sec hf, phi_sec hf', he, chT_shift]

theorem eqv_of_val {a b : (e10Sig p r s).Site} (h : a.1 = b.1) :
    Relation.EqvGen (e10Sig p r s).SamePoint a b := by
  have : a = b := Subtype.ext h
  subst this; exact Relation.EqvGen.refl _

theorem eqv_step {a b : (e10Sig p r s).Site} (h : (e10Sig p r s).SamePoint a b) :
    Relation.EqvGen (e10Sig p r s).SamePoint a b := Relation.EqvGen.rel _ _ h

/-- The canonical point of a sector point off its right edge, and on it. -/
theorem cpt_lt2 (H : Hyp p r s w) {z : ℤ × ℤ} (hz : SD p r s z) (hx : z.1 < 2 * r + s) :
    cpt r s (Phi p r s w 2 z) = (2, z) := by
  have hr := H.hr; have hs := H.hs
  obtain ⟨z1, z2⟩ := z
  simp only [SD] at hz hx
  have e : (z1, z2) + soff r s 2 = (z1 + 0, z2 - 0) := by ext <;> simp [soff] <;> ring
  rw [phi_sec (by decide), e, chT, cpt_T]
  simp only
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  split_ifs <;> first | omega | (ext <;> simp <;> ring)

theorem cpt_eq2 (H : Hyp p r s w) {z : ℤ × ℤ} (hz : SD p r s z) (hx : z.1 = 2 * r + s) :
    cpt r s (Phi p r s w 2 z) = (3, (0, z.2 + (2 * r + s))) := by
  have hr := H.hr; have hs := H.hs
  obtain ⟨z1, z2⟩ := z
  simp only [SD] at hz hx
  subst hx
  have e : (2 * r + s, z2) + soff r s 2 = ((2 * r + s) + 3 * (2 * r + s) * 0, z2 + (2 * r + s) - ((2 * r + s) + 3 * (2 * r + s) * 0)) := by
    ext <;> simp [soff] <;> ring
  rw [phi_sec (by decide), e, chT, cpt_T]
  simp only
  rw [show ((2 * r + s) + 3 * (2 * r + s) * 0) % (3 * (2 * r + s)) = (2 * r + s) by
    rw [emod_eq_of (by omega) (q := 0) (b := (2 * r + s)) (by ring) (by omega) (by omega)]]
  split_ifs <;> first | omega | (ext <;> simp <;> ring)

theorem cpt_lt3 (H : Hyp p r s w) {z : ℤ × ℤ} (hz : SD p r s z) (hx : z.1 < 2 * r + s) :
    cpt r s (Phi p r s w 3 z) = (3, z) := by
  have hr := H.hr; have hs := H.hs
  obtain ⟨z1, z2⟩ := z
  simp only [SD] at hz hx
  have e : (z1, z2) + soff r s 3 = (z1 + (2 * r + s), z2 - (2 * r + s)) := by ext <;> simp [soff] <;> ring
  rw [phi_sec (by decide), e, chT, cpt_T]
  simp only
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  split_ifs <;> first | omega | (ext <;> simp <;> ring)

theorem cpt_eq3 (H : Hyp p r s w) {z : ℤ × ℤ} (hz : SD p r s z) (hx : z.1 = 2 * r + s) :
    cpt r s (Phi p r s w 3 z) = (4, (0, z.2 + (2 * r + s))) := by
  have hr := H.hr; have hs := H.hs
  obtain ⟨z1, z2⟩ := z
  simp only [SD] at hz hx
  subst hx
  have e : (2 * r + s, z2) + soff r s 3 = (2 * (2 * r + s) + 3 * (2 * r + s) * 0, z2 + (2 * r + s) - (2 * (2 * r + s) + 3 * (2 * r + s) * 0)) := by
    ext <;> simp [soff] <;> ring
  rw [phi_sec (by decide), e, chT, cpt_T]
  simp only
  rw [show (2 * (2 * r + s) + 3 * (2 * r + s) * 0) % (3 * (2 * r + s)) = 2 * (2 * r + s) by
    rw [emod_eq_of (by omega) (q := 0) (b := 2 * (2 * r + s)) (by ring) (by omega) (by omega)]]
  split_ifs <;> first | omega | (ext <;> simp <;> ring)

theorem cpt_lt4 (H : Hyp p r s w) {z : ℤ × ℤ} (hz : SD p r s z) (hx : z.1 < 2 * r + s) :
    cpt r s (Phi p r s w 4 z) = (4, z) := by
  have hr := H.hr; have hs := H.hs
  obtain ⟨z1, z2⟩ := z
  simp only [SD] at hz hx
  have e : (z1, z2) + soff r s 4 = (z1 + 2 * (2 * r + s), z2 - 2 * (2 * r + s)) := by ext <;> simp [soff] <;> ring
  rw [phi_sec (by decide), e, chT, cpt_T]
  simp only
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  split_ifs <;> first | omega | (ext <;> simp <;> ring)

theorem cpt_eq4 (H : Hyp p r s w) {z : ℤ × ℤ} (hz : SD p r s z) (hx : z.1 = 2 * r + s) :
    cpt r s (Phi p r s w 4 z) = (2, (0, z.2 + (2 * r + s))) := by
  have hr := H.hr; have hs := H.hs
  obtain ⟨z1, z2⟩ := z
  simp only [SD] at hz hx
  subst hx
  have e : (2 * r + s, z2) + soff r s 4 = (0 + 3 * (2 * r + s) * 1, z2 + (2 * r + s) - (0 + 3 * (2 * r + s) * 1)) := by
    ext <;> simp [soff] <;> ring
  rw [phi_sec (by decide), e, chT, cpt_T]
  simp only
  rw [show (0 + 3 * (2 * r + s) * 1) % (3 * (2 * r + s)) = 0 by
    rw [emod_eq_of (by omega) (q := 1) (b := 0) (by ring) (by omega) (by omega)]]
  split_ifs <;> first | omega | (ext <;> simp <;> ring)

end Claude5E10
