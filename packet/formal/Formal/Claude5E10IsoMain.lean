import Formal.Claude5E10IsoBase

/-!
# E10: `IsoOK` makes the spec graph isomorphic to the model (`iso_of`)

Written by a Claude worker (2026-10-20, E10 bridge session).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

section

variable (H : Hyp p r s w) (I : IsoOK p r s w)
include H I

theorem phi_eqv {a b : (e10Sig p r s).Site} (h : Relation.EqvGen (e10Sig p r s).SamePoint a b) :
    Phi p r s w a.1.1 a.1.2 = Phi p r s w b.1.1 b.1.2 := by
  induction h with
  | rel x y hxy => exact I.same x y hxy
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem dom_of_cd {f : Fin 5} {z : ℤ × ℤ} (h : CD p r s f z) :
    ∃ c, c < 3 ∧ Dom p r s c (z + (if f.val < 2 then 0 else soff r s f)) ∧
      ch p r s w c (z + (if f.val < 2 then 0 else soff r s f)) = Phi p r s w f z := by
  have hf := f.isLt
  by_cases h0 : f.val = 0
  · refine ⟨0, by norm_num, ?_, ?_⟩ <;> simp only [h0, show 0 < 2 by norm_num, ite_true, add_zero]
    · simpa [CD, h0, Dom] using h
    · simp [Phi, h0]
  by_cases h1 : f.val = 1
  · refine ⟨1, by norm_num, ?_, ?_⟩ <;> simp only [h1, show 1 < 2 by norm_num, ite_true, add_zero]
    · simpa [CD, h1, Dom] using h
    · simp [Phi, h1]
  · refine ⟨2, by norm_num, ?_, ?_⟩ <;> simp only [show ¬ f.val < 2 by omega, ite_false]
    · simp only [CD, h0, h1, ite_false, SD] at h
      simp only [Dom, HT, soff, Prod.fst_add, Prod.snd_add]; constructor <;> linarith [h.2.2.1, h.2.2.2]
    · simp [Phi, h0, h1]

theorem phi_valid (a : (e10Sig p r s).Site) : Valid p r s (Phi p r s w a.1.1 a.1.2) := by
  obtain ⟨c, hc, hd, he⟩ := dom_of_cd H I ((I.incell _ _).1 a.2)
  rw [← he]; exact ch_valid H.hp H.hr H.hs H.hw0 H.hw1 hc hd

/-- The model vertex of a site. -/
def siteM (a : (e10Sig p r s).Site) : MS p r s := ⟨Phi p r s w a.1.1 a.1.2, phi_valid H I a⟩

/-- The model vertex of a vertex. -/
def vphi : (e10Sig p r s).Vertex → MS p r s :=
  Quot.lift (siteM H I) (fun _ _ h => Subtype.ext (phi_eqv H I h))

theorem vphi_vtx (a : (e10Sig p r s).Site) : (vphi H I ((e10Sig p r s).vtx a)).1 = Phi p r s w a.1.1 a.1.2 :=
  rfl

/-- The canonical site of a model vertex. -/
def canonSite (v : MS p r s) : (e10Sig p r s).Site :=
  ⟨cpt r s v.1, (I.incell _ _).2 (cpt_dom H v.2)⟩

theorem vphi_canon (v : MS p r s) : vphi H I ((e10Sig p r s).vtx (canonSite H I v)) = v :=
  Subtype.ext (cpt_phi H v.2)

theorem eqv_canon (a : (e10Sig p r s).Site) :
    Relation.EqvGen (e10Sig p r s).SamePoint a (canonSite H I (siteM H I a)) :=
  I.canon a _

theorem vphi_injective : Function.Injective (vphi H I) := by
  intro v x h
  induction v using Quot.ind
  induction x using Quot.ind
  rename_i a b
  have e : siteM H I a = siteM H I b := h
  apply Quot.sound
  have h1 := eqv_canon H I a
  have h2 := eqv_canon H I b
  rw [e] at h1
  exact Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.symm _ _ h2)

theorem vphi_surjective : Function.Surjective (vphi H I) :=
  fun v => ⟨_, vphi_canon H I v⟩

/-- The vertex bijection. -/
noncomputable def vEquiv : (e10Sig p r s).Vertex ≃ MS p r s :=
  Equiv.ofBijective (vphi H I) ⟨vphi_injective H I, vphi_surjective H I⟩

end

end Claude5E10
