import Formal.Claude5E10SigIso
import Formal.Claude5E10Ray

/-!
# E10 as a Theorem 1a signature: adjacency, `Valid`, `TrianglesInCharts`

Written by a Claude worker (2026-10-21, E10 bridge session).

* `adj_iff'` : the bijection `vE` preserves adjacency (`chart_pair`);
* `valid_e10S` : `e10S Q` satisfies Theorem 1a's assumptions at every `t` with `Hyp`
  (`two_common`, chart injectivity, `deg_cases`, `deg_five_corner` with `corner_site`, `tri` with
  `chart_tri`);
* `path_iff` : literal paths of `e10S Q` at `t` are those of the model.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge2 (Aff Chart)

variable {Q : RP} {t : ℕ}

section

variable (H : Hyp (Q.p t) (Q.r t) (Q.s t) (Q.w t))
include H

theorem adjraw_fwd {a b : ClaudeChallenge2.Vertex (e10S Q) t}
    (h : ClaudeChallenge2.AdjRaw (e10S Q) t a b) (hne : a ≠ b) :
    AdjM (Q.p t) (Q.r t) (Q.s t) (Q.w t) (vΦ H a).1 (vΦ H b).1 := by
  obtain ⟨x, y, rfl, rfl, hf, u, hu, hy⟩ := h
  have qy := site_qd H y
  rw [← hf, hy] at qy
  refine ⟨fun e => hne (vΦ_inj H (Subtype.ext e)), qc x.1.1.val, qc_lt _, x.1.2, u,
    dom_qd (site_qd H x), dom_qd qy, hu, rfl, ?_⟩
  show _ = ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) (qc y.1.1.val) y.1.2
  rw [← hf, hy]

theorem adjM_valid {v x : MV} (h : AdjM (Q.p t) (Q.r t) (Q.s t) (Q.w t) v x) :
    Valid (Q.p t) (Q.r t) (Q.s t) x := by
  obtain ⟨-, c, hc, z, u, -, d2, -, -, rfl⟩ := h
  exact ch_valid H.hp H.hr H.hs H.hw0 H.hw1 hc d2

/-- The site of a signature chart point. -/
def mkSite (f : ℕ) (hf : f < 5) (y : ℤ × ℤ) (hq : QD (Q.p t) (Q.r t) (Q.s t) f y) :
    ClaudeChallenge2.Site (e10S Q) t :=
  ⟨(⟨f, hf⟩, y), (Q.mem_iff hf t (hm_of H) y).2 hq⟩

theorem vtx_mkSite {f : ℕ} {hf : f < 5} {y : ℤ × ℤ} {hq : QD (Q.p t) (Q.r t) (Q.s t) f y}
    {a : ClaudeChallenge2.Vertex (e10S Q) t}
    (h : ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) (qc f) y = (vΦ H a).1) :
    ClaudeChallenge2.vtx (mkSite H f hf y hq) = a :=
  vΦ_inj H (Subtype.ext h)

/-- **Adjacency is preserved.** -/
theorem adj_iff' (a b : ClaudeChallenge2.Vertex (e10S Q) t) :
    (ClaudeChallenge2.graph (e10S Q) t).Adj a b ↔
      (GM (Q.p t) (Q.r t) (Q.s t) (Q.w t)).Adj (vE H a) (vE H b) := by
  constructor
  · rintro ⟨hne, h | h⟩
    · exact adjraw_fwd H h hne
    · exact adjM_symm (adjraw_fwd H h (Ne.symm hne))
  · intro hA
    obtain ⟨hne, c, hc, z, u, d1, d2, hu, e1, e2⟩ := hA
    obtain ⟨f, hf, y, q1, q2, c1, c2⟩ := chart_pair H hc d1 d2 hu
    refine ⟨fun e => hne (by rw [e]), Or.inl ⟨mkSite H f hf y q1, mkSite H f hf (y + u) q2,
      vtx_mkSite H (c1.trans e1), vtx_mkSite H (c2.trans e2), rfl, u, hu, rfl⟩⟩

/-- **Theorem 1a's assumptions hold.** -/
theorem valid_e10S :
    ClaudeChallenge2.Valid (e10S Q) t ∧ ClaudeChallenge2.TrianglesInCharts (e10S Q) t := by
  have hm := hm_of H
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- two common neighbours
    intro b c hbc
    have hA := (adj_iff' H b c).1 hbc
    obtain ⟨y, z, hyz, hP⟩ := two_common H hA
    have hy := adjM_valid H ((hP y).2 (Or.inl rfl)).1
    have hz := adjM_valid H ((hP z).2 (Or.inr rfl)).1
    refine ⟨(vE H).symm ⟨y, hy⟩, (vE H).symm ⟨z, hz⟩, fun e => hyz ?_, fun v => ?_⟩
    · have := congrArg (fun v => (vE H v).1) e
      simpa using this
    · rw [adj_iff' H b v, adj_iff' H c v, gm_adj, gm_adj, hP, Equiv.eq_symm_apply,
        Equiv.eq_symm_apply, Subtype.ext_iff, Subtype.ext_iff]
  · -- charts are injective
    intro f z z' h h' e
    have e' := congrArg (fun v => (vΦ H v).1) e
    change ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) (qc f.val) z =
      ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) (qc f.val) z' at e'
    have q := (Q.mem_iff f.isLt t hm z).1 h
    have q' := (Q.mem_iff f.isLt t hm z').1 h'
    by_cases hf : f.val < 2
    · rw [qc_cap hf] at e'
      rcases (show f.val = 0 ∨ f.val = 1 by omega) with e0 | e0 <;> rw [e0] at q q' e'
      · exact chL_inj H.hr H.hs q q' e'
      · exact chU_inj H.hr H.hs H.hw0 H.hw1 q q' e'
    · rw [qc_ge (by omega)] at e'
      exact sec_inj H.hr H.hs (by omega) f.isLt q q' e'
  · -- degrees
    intro v
    have hd := Claude4C1.deg_of_equiv (vE H) (adj_iff' H) v
    show ClaudeChallenge.deg _ v = 5 ∨ ClaudeChallenge.deg _ v = 6
    rw [hd]
    rcases deg_cases H (vE H v) with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · -- degree five means marked
    intro v h5
    have hd := Claude4C1.deg_of_equiv (vE H) (adj_iff' H) v
    have h5' : ClaudeChallenge.deg (GM (Q.p t) (Q.r t) (Q.s t) (Q.w t)) (vE H v) = 5 := by
      rw [← hd]; exact h5
    obtain ⟨k, hk, hq, hch⟩ := corner_site H (deg_five_corner H _ h5')
    have ce := Q.corn_eval k t
    have hk2 : cornF k < 2 := by unfold cornF; split_ifs <;> omega
    have hmem : (Q.chartA (cornF k)).Mem t ((Q.cornA k).1.eval t, (Q.cornA k).2.eval t) := by
      rw [ce]; exact (Q.mem_iff (by omega) t hm _).2 hq
    refine ⟨⟨k, hk⟩, hmem, vΦ_inj H (Subtype.ext ?_)⟩
    show ch (Q.p t) (Q.r t) (Q.s t) (Q.w t) (qc (cornF k))
      ((Q.cornA k).1.eval t, (Q.cornA k).2.eval t) = (vΦ H v).1
    rw [ce, qc_cap hk2]; exact hch
  · -- triangles
    intro a b c hab hac hbc
    have A := (adj_iff' H a b).1 hab
    have B := (adj_iff' H a c).1 hac
    have C := (adj_iff' H b c).1 hbc
    obtain ⟨c', a', b', e', ⟨hc', da, cha⟩, ⟨-, db, chb⟩, ⟨-, de, che⟩, u1, u2, u3⟩ := tri H A B C
    obtain ⟨f, hf, τ, qa, qb, qe, ca, cb, cc'⟩ := chart_tri H hc' da db de u1 u2 u3
    refine ⟨⟨f, hf⟩, a' + τ, b' + τ, e' + τ, (Q.mem_iff hf t hm _).2 qa,
      (Q.mem_iff hf t hm _).2 qb, (Q.mem_iff hf t hm _).2 qe,
      vtx_mkSite (hq := qa) H (ca.trans cha), vtx_mkSite (hq := qb) H (cb.trans chb),
      vtx_mkSite (hq := qe) H (cc'.trans che), ?_, ?_, ?_⟩
    · rw [show b' + τ - (a' + τ) = b' - a' by abel]; exact u1
    · rw [show e' + τ - (a' + τ) = e' - a' by abel]; exact u2
    · rw [show e' + τ - (b' + τ) = e' - b' by abel]; exact u3

/-- **Literal paths of the signature are those of the model.** -/
theorem path_iff :
    ClaudeChallenge2.PathExists (e10S Q) t ↔
      ∃ n q, ClaudeChallenge.LiteralPath (GM (Q.p t) (Q.r t) (Q.s t) (Q.w t)) n q := by
  show (∃ n q, ClaudeChallenge.LiteralPath (ClaudeChallenge2.graph (e10S Q) t) n q) ↔ _
  exact Claude4C1.exists_literal_iff (vE H) (adj_iff' H)

end

/-- Theorem 1a for the affine E10 families, in terms of the model (proved in `Claude5E10T1a`). -/
def T1aGM : Prop :=
  ∀ (Q : RP) (t₁ : ℕ), (∀ t, t₁ ≤ t → Hyp (Q.p t) (Q.r t) (Q.s t) (Q.w t)) →
    EvPer (fun t => ∃ n q, ClaudeChallenge.LiteralPath (GM (Q.p t) (Q.r t) (Q.s t) (Q.w t)) n q)

end Claude5E10
