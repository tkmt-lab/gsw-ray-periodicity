import Formal.Claude5E10SigDef

/-!
# E10 as a Theorem 1a signature: its vertices are the model vertices

Written by a Claude worker (2026-10-21, E10 bridge session).

* `vΦ` : the vertex of a site of `e10S Q` at `t` is the model vertex `ch (qc f) z`
  (well defined by `rec_sound`);
* `vΦ_inj` : sites of one model vertex are joined by records (`cap_rec`, `tube_cases`);
* `vΦ_surj` : every model vertex has a site;
* `vE` : the bijection.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge2 (Aff Chart)

variable {Q : RP} {t : ℕ}

theorem rtgt_lt {n : ℕ} (hn : n < 75) : rtgt n < 5 := by unfold rtgt; split_ifs <;> omega

theorem qc_ge {f : ℕ} (hf : 2 ≤ f) : qc f = 2 := by unfold qc; split_ifs <;> omega

theorem tag_ch2 {p r s w : ℤ} (z : ℤ × ℤ) : (ch p r s w 2 z).1 = 2 := rfl

section

variable (H : Hyp (Q.p t) (Q.r t) (Q.s t) (Q.w t))
include H

theorem hm_of : 0 ≤ 2 * Q.r t + Q.s t := by have := H.hr; have := H.hs; omega

theorem site_qd (x : ClaudeChallenge2.Site (e10S Q) t) :
    QD (Q.p t) (Q.r t) (Q.s t) x.1.1.val x.1.2 :=
  (Q.mem_iff x.1.1.isLt t (hm_of H) x.1.2).1 x.2

/-- The model vertex of a site. -/
def sF (x : ClaudeChallenge2.Site (e10S Q) t) : MS (Q.p t) (Q.r t) (Q.s t) :=
  ⟨ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) (qc x.1.1.val) x.1.2,
    ch_valid H.hp H.hr H.hs H.hw0 H.hw1 (qc_lt _) (dom_qd (site_qd H x))⟩

theorem sound {x y : ClaudeChallenge2.Site (e10S Q) t}
    (h : ClaudeChallenge2.SamePoint (e10S Q) t x y) : sF H x = sF H y := by
  obtain ⟨n, h1, h2, h3⟩ := h
  apply Subtype.ext
  show ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) (qc x.1.1.val) x.1.2 =
    ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) (qc y.1.1.val) y.1.2
  have e1 : x.1.1.val = rsrc n.val := congrArg Fin.val h1
  have e2 : y.1.1.val = rtgt n.val := congrArg Fin.val h2
  have e3 : recMap (Q.p t) (Q.r t) (Q.s t) (Q.w t) n.val x.1.2 = y.1.2 := by
    rw [← Q.rec_eval]; exact h3
  have q1 := site_qd H x
  have q2 := site_qd H y
  rw [e1] at q1 ⊢
  rw [e2, ← e3] at q2 ⊢
  exact rec_sound H n.isLt q1 q2

/-- The model vertex of a vertex. -/
def vΦ : ClaudeChallenge2.Vertex (e10S Q) t → MS (Q.p t) (Q.r t) (Q.s t) :=
  Quot.lift (sF H) (fun a b h => by
    induction h with
    | rel _ _ h => exact sound H h
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2)

theorem vΦ_vtx (x : ClaudeChallenge2.Site (e10S Q) t) : vΦ H (ClaudeChallenge2.vtx x) = sF H x :=
  rfl

theorem samep_of {x y : ClaudeChallenge2.Site (e10S Q) t} (n : ℕ) (hn : n < 75)
    (h1 : x.1.1.val = rsrc n) (h2 : y.1.1.val = rtgt n)
    (h3 : recMap (Q.p t) (Q.r t) (Q.s t) (Q.w t) n x.1.2 = y.1.2) :
    ClaudeChallenge2.SamePoint (e10S Q) t x y := by
  refine ⟨⟨n, hn⟩, Fin.ext h1, Fin.ext h2, ?_⟩
  show ClaudeChallenge2.rotN (RP.rrot n) x.1.2 + ((Q.rdA n).1.eval t, (Q.rdA n).2.eval t) = y.1.2
  rw [Q.rec_eval]; exact h3

theorem site_ext {x y : ClaudeChallenge2.Site (e10S Q) t} (h1 : x.1.1.val = y.1.1.val)
    (h2 : x.1.2 = y.1.2) : x = y :=
  Subtype.ext (Prod.ext (Fin.ext h1) h2)

theorem tube_conn {x y : ClaudeChallenge2.Site (e10S Q) t} (hx : 2 ≤ x.1.1.val)
    (hy : 2 ≤ y.1.1.val)
    (h : ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) 2 x.1.2 = ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) 2 y.1.2) :
    Relation.EqvGen (ClaudeChallenge2.SamePoint (e10S Q) t) x y := by
  rcases tube_cases H.hr H.hs hx hy x.1.1.isLt y.1.1.isLt (site_qd H x) (site_qd H y) h with
    ⟨e1, e2⟩ | ⟨n, hn, ⟨a, b, c⟩ | ⟨a, b, c⟩⟩
  · rw [site_ext H e1 e2]; exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.rel _ _ (samep_of H n (by omega) a.symm b.symm c)
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (samep_of H n (by omega) a.symm b.symm c))

theorem cap_conn {x : ClaudeChallenge2.Site (e10S Q) t} (hx : x.1.1.val < 2)
    (hb : ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) x.1.1.val x.1.2 ≠ ((x.1.1.val : ℤ), x.1.2)) :
    ∃ y : ClaudeChallenge2.Site (e10S Q) t, 2 ≤ y.1.1.val ∧
      ClaudeChallenge2.SamePoint (e10S Q) t x y := by
  obtain ⟨n, hn, h1, h2, h3⟩ := cap_rec H hx (site_qd H x) hb
  let y : ClaudeChallenge2.Site (e10S Q) t :=
    ⟨(⟨rtgt n, rtgt_lt hn⟩, recMap (Q.p t) (Q.r t) (Q.s t) (Q.w t) n x.1.2),
      (Q.mem_iff (rtgt_lt hn) t (hm_of H) _).2 h3⟩
  exact ⟨y, h2, samep_of H n hn h1.symm rfl rfl⟩

/-- A cap site and a sector site of one model vertex are joined. -/
theorem conn_ct {x y : ClaudeChallenge2.Site (e10S Q) t} (hx : x.1.1.val < 2) (hy : 2 ≤ y.1.1.val)
    (h : sF H x = sF H y) : Relation.EqvGen (ClaudeChallenge2.SamePoint (e10S Q) t) x y := by
  have h' : ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) (qc x.1.1.val) x.1.2 =
      ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) (qc y.1.1.val) y.1.2 := congrArg Subtype.val h
  rw [qc_cap hx, qc_ge hy] at h'
  have hb : ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) x.1.1.val x.1.2 ≠ ((x.1.1.val : ℤ), x.1.2) := by
    intro e
    have := congrArg Prod.fst (e.symm.trans h')
    simp only [tag_ch2] at this
    omega
  obtain ⟨y', hy', hs⟩ := cap_conn H hx hb
  have e2 := (sound H hs).symm.trans h
  have e2' : ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) (qc y'.1.1.val) y'.1.2 =
      ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) (qc y.1.1.val) y.1.2 := congrArg Subtype.val e2
  rw [qc_ge hy', qc_ge hy] at e2'
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hs) (tube_conn H hy' hy e2')

/-- **Sites of one model vertex are joined.** -/
theorem conn {x y : ClaudeChallenge2.Site (e10S Q) t} (h : sF H x = sF H y) :
    Relation.EqvGen (ClaudeChallenge2.SamePoint (e10S Q) t) x y := by
  have h' : ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) (qc x.1.1.val) x.1.2 =
      ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) (qc y.1.1.val) y.1.2 := congrArg Subtype.val h
  by_cases hx : x.1.1.val < 2 <;> by_cases hy : y.1.1.val < 2
  · rw [qc_cap hx, qc_cap hy] at h'
    have qx := site_qd H x
    have qy := site_qd H y
    rcases (show x.1.1.val = 0 ∨ x.1.1.val = 1 by omega) with e | e <;>
      rcases (show y.1.1.val = 0 ∨ y.1.1.val = 1 by omega) with e' | e' <;>
      rw [e] at qx h' <;> rw [e'] at qy h'
    · rw [site_ext H (by rw [e, e']) (chL_inj H.hr H.hs qx qy h')]; exact Relation.EqvGen.refl _
    · exact absurd h' (chL_ne_U H.hp)
    · exact absurd h'.symm (chL_ne_U H.hp)
    · rw [site_ext H (by rw [e, e']) (chU_inj H.hr H.hs H.hw0 H.hw1 qx qy h')]
      exact Relation.EqvGen.refl _
  · exact conn_ct H hx (by omega) h
  · exact Relation.EqvGen.symm _ _ (conn_ct H hy (by omega) h.symm)
  · rw [qc_ge (by omega), qc_ge (by omega)] at h'
    exact tube_conn H (by omega) (by omega) h'

theorem vΦ_inj : Function.Injective (vΦ H) := by
  intro a b h
  induction a using Quot.ind
  induction b using Quot.ind
  exact Quot.sound (conn H h)

theorem vΦ_surj : Function.Surjective (vΦ H) := by
  have hp := H.hp; have hr := H.hr; have hs := H.hs
  rintro ⟨⟨k, z⟩, hv⟩
  rcases hv with ⟨hk, hz⟩ | ⟨hk, hz⟩ | ⟨hk, h0, h1, h2, h3⟩ <;> simp only at hk <;> subst hk
  · have hq : QD (Q.p t) (Q.r t) (Q.s t) 0 z := by
      show HL _ _ z; simp only [HL]; simp only [IL] at hz; omega
    refine ⟨ClaudeChallenge2.vtx ⟨(⟨0, by show 0 < 5; omega⟩, z), (Q.mem_iff (by omega) t (hm_of H) z).2 hq⟩,
      Subtype.ext ?_⟩
    exact chL_I (p := Q.p t) (w := Q.w t) hz
  · have hq : QD (Q.p t) (Q.r t) (Q.s t) 1 z := by
      show HU _ _ z; simp only [HU]; simp only [IU] at hz; omega
    refine ⟨ClaudeChallenge2.vtx ⟨(⟨1, by show 1 < 5; omega⟩, z), (Q.mem_iff (by omega) t (hm_of H) z).2 hq⟩,
      Subtype.ext ?_⟩
    exact chU_I (p := Q.p t) (w := Q.w t) hz
  · obtain ⟨u, h⟩ := z
    simp only at h0 h1 h2 h3
    obtain ⟨τ, c, hc, hτ⟩ := tube_place (p := Q.p t) hr hs u
    have hq := hτ (u, h - u) (by show 0 ≤ u + (h - u) ∧ u + (h - u) ≤ 2 * Q.p t; omega) (Or.inl rfl)
    refine ⟨ClaudeChallenge2.vtx ⟨(⟨2 + c, by show 2 + c < 5; omega⟩, (u, h - u) + τ • per (Q.r t) (Q.s t)),
      (Q.mem_iff (by omega) t (hm_of H) _).2 hq⟩, Subtype.ext ?_⟩
    show ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) (qc (2 + c)) ((u, h - u) + τ • per (Q.r t) (Q.s t)) = _
    rw [qc_sec, chT_shift, chT]
    simp only [add_sub_cancel]
    rw [Int.emod_eq_of_lt h0 h1]

/-- **The bijection.** -/
noncomputable def vE : ClaudeChallenge2.Vertex (e10S Q) t ≃ MS (Q.p t) (Q.r t) (Q.s t) :=
  Equiv.ofBijective (vΦ H) ⟨vΦ_inj H, vΦ_surj H⟩

theorem vE_apply (v : ClaudeChallenge2.Vertex (e10S Q) t) : vE H v = vΦ H v := rfl

end

end Claude5E10
