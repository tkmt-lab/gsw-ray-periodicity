import Formal.Claude5E10Assemble3

/-!
# E10 model: `assemble` — reduced tables give a line-state invariant

Written by a Claude worker (2026-10-20, E10 bridge session).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w k : ℤ}

theorem avoid_cap {T : Tabs} (R : RedOK p r s w k T) {c : ℕ} (hc : c < 2) {d : ℤ × ℤ}
    {E ε : ℤ} {z : ℤ × ℤ} (h : T.cap r s c d E ε) (hz : CornerPos p r s w c z) :
    cross d z ≠ E + ε := by
  intro he
  obtain ⟨t, -, ht⟩ := h
  have hZ := (corner_Zi (p := p) (w := w) hc t z).2 hz
  have e1 := state_iter (r := r) (s := s) c t d z
  rw [he, ρS_snd_add] at e1
  have e2 := congrArg Prod.snd e1
  have e3 := congrArg Prod.fst e1
  simp only at e2 e3
  apply R.avoidC c hc _ _ ε (Zi r s c t z) ht hZ
  rw [e3, ← e2]

theorem avoid_tube {T : Tabs} (H : Hyp p r s w) (TW : Tw p r s w k) (R : RedOK p r s w k T)
    {d : ℤ × ℤ} {E ε : ℤ} {z : ℤ × ℤ} (h : T.tube r s d E ε ∨ Hz p d E ε)
    (hz : CornerPos p r s w 2 z) : cross d z ≠ E + ε := by
  intro he
  have hp := H.hp
  rcases h with ⟨f, Q, h0, hE⟩ | hh
  · obtain ⟨qp, hqp⟩ := TW.qp
    rcases tube_corner H TW hz with ⟨h1, cc, X, hcc, hx⟩ | ⟨h1, cc, X, hcc, hx⟩
    · apply (R.avoidT d f ε h0 cc hcc).1
      refine ⟨-(d.1 + d.2) * X - Q, ?_⟩
      have : z.2 = -z.1 := by omega
      simp only [cross] at he
      rw [this, hx, hE] at he
      linear_combination -he
    · apply (R.avoidT d f ε h0 cc hcc).2
      refine ⟨d.1 * (2 * qp - X) - d.2 * X - Q, ?_⟩
      have : z.2 = 2 * p - z.1 := by omega
      simp only [cross] at he
      rw [this, hx, hE, hqp] at he
      linear_combination -he
  · have h1 : z.1 + z.2 = 0 ∨ z.1 + z.2 = 2 * p := by
      rcases tube_corner H TW hz with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    simp only [Hz] at hh
    rcases hh with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      simp only [cross] at he <;> omega

/-- **Reduced tables give a line-state invariant.** -/
theorem assemble {T : Tabs} (H : Hyp p r s w) (TW : Tw p r s w k) (R : RedOK p r s w k T) :
    InvOK p r s w (T.GG p r s) where
  start := by
    intro c a b e hc ha h1 h2 h3 u1 u2 u3
    rcases c_cases hc with rfl | rfl | rfl
    · have := start_cap R (by norm_num : (0 : ℕ) < 2) ha (by simpa [CapDom, Dom] using h2)
        (by simpa [CapDom, Dom] using h3) u1 u2 u3
      simpa [Tabs.GG] using this
    · have := start_cap R (by norm_num : (1 : ℕ) < 2) ha (by simpa [CapDom, Dom] using h2)
        (by simpa [CapDom, Dom] using h3) u1 u2 u3
      simpa [Tabs.GG] using this
    · have := start_tube H TW R ha (by simpa [Dom] using h2) (by simpa [Dom] using h3) u1 u2 u3
      simpa [Tabs.GG] using this
  avoid := by
    intro c d E ε z hc h hz
    rcases c_cases hc with rfl | rfl | rfl
    · exact avoid_cap R (by norm_num) (by simpa [Tabs.GG] using h) hz
    · exact avoid_cap R (by norm_num) (by simpa [Tabs.GG] using h) hz
    · exact avoid_tube H TW R (by simpa [Tabs.GG] using h) hz
  capT := by
    intro c j hc hj d E ε zE zO h h1 h2 h3 h4 h5 h6 h7 h8
    exact capT_GG R hc hj h h1 h2 h3 h4 h5 h6 h7 h8
  Tcap := by
    intro c j hc hj d' E ε yE yO t h h1 h2 h3 h4 h5 h6 h7 h8
    exact Tcap_GG R hc hj h h1 h2 h3 h4 h5 h6 h7 h8

end Claude5E10
