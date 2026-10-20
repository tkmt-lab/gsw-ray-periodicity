import Formal.Claude5D14StartD

/-!
# D14: no literal path for `r, s ≥ 2`

Written by a Claude worker (2026-10-20, D14 bridge session), adapting `Claude5O2Nec.lean`.  The
first vertex of a literal path has degree five, so it is a label corner (`deg_five`); the first
triangle lies in one chart (`place`), at a corner of that cell polygon (`corner_pos`); the start
lemmas `st*` finish.
-/

set_option linter.unusedVariables false

namespace Claude5D14

open ClaudeChallenge Claude2Aligned

theorem no_path_gm (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) :
    ¬ ∃ n p, LiteralPath (GM (r : ℤ) (s : ℤ)) n p := by
  rintro ⟨n, p, hp⟩
  have hr2 := two_le_of_two hr; have hs2 := two_le_of_two hs
  have hr1 := one_le_of_two hr; have hs1 := one_le_of_two hs
  have h4 := hp.1
  have hc := deg_five hr2 hs2 (p 0) hp.2.2.2.2.2.1
  have a01 : AdjM (r : ℤ) (s : ℤ) (p 0).1 (p 1).1 := hp.2.2.2.1 0 (by omega)
  have a02 : AdjM (r : ℤ) (s : ℤ) (p 0).1 (p 2).1 := hp.2.2.2.2.1 0 (by omega)
  have a12 : AdjM (r : ℤ) (s : ℤ) (p 1).1 (p 2).1 := hp.2.2.2.1 1 (by omega)
  obtain ⟨c, a, b, q, ha, hb, hq, u0, hap⟩ := place hr1 hs1 a01 a02 a12
  have hcp := corner_pos hr1 hs1 ha.1 ha.2.1 (by rw [ha.2.2]; exact hc)
  obtain ⟨a1, a2⟩ := a
  rcases c_cases ha.1 with rfl | rfl
  · simp only [IsCornerPos] at hcp
    rcases hcp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact st0_0 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_1 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_2 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_3 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_4 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_5 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_6 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_7 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_8 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_9 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_10 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_11 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
  · simp only [IsCornerPos] at hcp
    rcases hcp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact st1_0 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_1 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_2 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_3 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_4 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_5 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_6 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_7 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_8 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_9 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_10 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_11 r s hr hs hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1

/-- **D14 absence** (`r, s ≥ 2`). -/
theorem d14_no_path (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) :
    ¬ ∃ n p, LiteralPath (d14Graph (r : ℤ) (s : ℤ)) n p := by
  rw [d14_iff_gm (one_le_of_two hr) (one_le_of_two hs)]
  exact no_path_gm r s hr hs

end Claude5D14
