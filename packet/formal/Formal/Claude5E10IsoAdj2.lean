import Formal.Claude5E10IsoAdj

/-!
# E10: literal paths in the spec surface are literal paths in the model (`e10_iff_gm_of`)

Written by a Claude worker (2026-10-20, E10 bridge session).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

/-- The model chart of a cell, and the chart point of a cell point. -/
def cc (f : Fin 5) : ℕ := if f.val = 0 then 0 else if f.val = 1 then 1 else 2
def cz (r s : ℤ) (f : Fin 5) (z : ℤ × ℤ) : ℤ × ℤ := if f.val < 2 then z else z + soff r s f

theorem cz_sub (f : Fin 5) (z z' : ℤ × ℤ) : cz r s f z' - cz r s f z = z' - z := by
  unfold cz; split_ifs <;> abel

theorem cc_lt (f : Fin 5) : cc f < 3 := by unfold cc; split_ifs <;> omega

theorem chart_of_cd {f : Fin 5} {z : ℤ × ℤ} (h : CD p r s f z) :
    Dom p r s (cc f) (cz r s f z) ∧ ch p r s w (cc f) (cz r s f z) = Phi p r s w f z := by
  have hf := f.isLt
  by_cases h0 : f.val = 0
  · simp only [cc, cz, h0, show 0 < 2 by norm_num, ite_true]
    exact ⟨by simpa [CD, h0, Dom] using h, by simp [Phi, h0]⟩
  by_cases h1 : f.val = 1
  · simp only [cc, cz, h1, show (1 : ℕ) ≠ 0 by norm_num, show 1 < 2 by norm_num, ite_true, ite_false]
    exact ⟨by simpa [CD, h1, Dom] using h, by simp [Phi, h1]⟩
  · simp only [cc, cz, h0, h1, show ¬ f.val < 2 by omega, ite_false]
    refine ⟨?_, by simp [Phi, h0, h1]⟩
    simp only [CD, h0, h1, ite_false, SD] at h
    show HT p _
    simp only [HT, soff, Prod.fst_add, Prod.snd_add]; constructor <;> linarith [h.2.2.1, h.2.2.2]

section

variable (H : Hyp p r s w) (I : IsoOK p r s w)
include H I

theorem adj_fwd {v x : (e10Sig p r s).Vertex} (h : (e10Graph p r s).Adj v x) :
    (GM p r s w).Adj (vphi H I v) (vphi H I x) := by
  obtain ⟨hne, a, b, rfl, rfl, hab⟩ := h
  have hne' : (vphi H I ((e10Sig p r s).vtx a)).1 ≠ (vphi H I ((e10Sig p r s).vtx b)).1 :=
    fun e => hne (vphi_injective H I (Subtype.ext e))
  have key : ∀ a b : (e10Sig p r s).Site, b.1.1 = a.1.1 → b.1.2 - a.1.2 ∈ unitVec →
      Phi p r s w a.1.1 a.1.2 ≠ Phi p r s w b.1.1 b.1.2 →
      AdjM p r s w (Phi p r s w a.1.1 a.1.2) (Phi p r s w b.1.1 b.1.2) := by
    rintro ⟨⟨f, z⟩, hz⟩ ⟨⟨f', z'⟩, hz'⟩ e hu hn
    simp only at e hu hn ⊢
    subst e
    obtain ⟨d1, e1⟩ := chart_of_cd (w := w) ((I.incell _ _).1 hz)
    obtain ⟨d2, e2⟩ := chart_of_cd (w := w) ((I.incell _ _).1 hz')
    refine ⟨hn, cc f', cc_lt f', cz r s f' z, cz r s f' z' - cz r s f' z, d1, by simpa using d2,
      by rw [cz_sub (r := r) (s := s) f' z z']; exact hu, e1, by simpa using e2⟩
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key a b h1 h2 hne'
  · exact adjM_symm (key b a h1 h2 (fun e => hne' e.symm))

theorem adj_bwd {v x : (e10Sig p r s).Vertex} (h : (GM p r s w).Adj (vphi H I v) (vphi H I x)) :
    (e10Graph p r s).Adj v x := by
  obtain ⟨hne, c, hc, z, u, h1, h2, hu, e1, e2⟩ := h
  refine ⟨fun e => hne (by rw [e]), ?_⟩
  -- two sites of one cell a unit apart with the given images
  have : ∃ (f : Fin 5) (ζ : ℤ × ℤ), CD p r s f ζ ∧ CD p r s f (ζ + u) ∧
      Phi p r s w f ζ = ch p r s w c z ∧ Phi p r s w f (ζ + u) = ch p r s w c (z + u) := by
    rcases c_cases hc with rfl | rfl | rfl
    · exact ⟨0, z, by simpa [CD, Dom] using h1, by simpa [CD, Dom] using h2, by simp [Phi], by simp [Phi]⟩
    · exact ⟨1, z, by simpa [CD, Dom] using h1, by simpa [CD, Dom] using h2, by simp [Phi], by simp [Phi]⟩
    · exact tube_step_sites H h1 h2 hu
  obtain ⟨f, ζ, d1, d2, p1, p2⟩ := this
  let a : (e10Sig p r s).Site := ⟨(f, ζ), (I.incell _ _).2 d1⟩
  let b : (e10Sig p r s).Site := ⟨(f, ζ + u), (I.incell _ _).2 d2⟩
  refine ⟨a, b, vphi_injective H I (Subtype.ext ?_), vphi_injective H I (Subtype.ext ?_),
    Or.inl ⟨rfl, by simpa [a, b] using hu⟩⟩
  · rw [vphi_vtx, ← e1]; exact p1
  · rw [vphi_vtx, ← e2]; exact p2

theorem adj_iff (v x : (e10Sig p r s).Vertex) :
    (e10Graph p r s).Adj v x ↔ (GM p r s w).Adj (vEquiv H I v) (vEquiv H I x) :=
  ⟨adj_fwd H I, adj_bwd H I⟩

/-- **Transfer.** -/
theorem e10_iff_gm_of :
    (∃ n q, LiteralPath (e10Graph p r s) n q) ↔ (∃ n q, LiteralPath (GM p r s w) n q) :=
  Claude4C1.exists_literal_iff (vEquiv H I) (adj_iff H I)

end

end Claude5E10
