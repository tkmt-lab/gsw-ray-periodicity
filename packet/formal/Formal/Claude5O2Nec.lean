import Formal.Claude5O2StartA
import Formal.Claude5O2StartB
import Formal.Claude5O2StartD

/-!
# O2: no literal path for `t, d ≥ 2`

Written by a Claude worker (2026-10-20, O2 bridge session).  The first vertex of a literal path
has degree five, so it is a corner (`deg_five`); the first triangle lies in one chart (`place`),
at a corner of that chart (`corner_pos`); the start lemmas `st*` finish.
-/

set_option linter.unusedVariables false

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

theorem no_path_gm (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) :
    ¬ ∃ n p, LiteralPath (GM (t : ℤ) (d : ℤ)) n p := by
  rintro ⟨n, p, hp⟩
  have ht2 := two_le_of_two ht; have hd2 := two_le_of_two hd
  have ht1 := one_le_of_two ht; have hd1 := one_le_of_two hd
  have h4 := hp.1
  have hc := deg_five ht2 hd2 (p 0) hp.2.2.2.2.2.1
  have a01 : AdjM (t : ℤ) (d : ℤ) (p 0).1 (p 1).1 := hp.2.2.2.1 0 (by omega)
  have a02 : AdjM (t : ℤ) (d : ℤ) (p 0).1 (p 2).1 := hp.2.2.2.2.1 0 (by omega)
  have a12 : AdjM (t : ℤ) (d : ℤ) (p 1).1 (p 2).1 := hp.2.2.2.1 1 (by omega)
  obtain ⟨c, a, b, q, ha, hb, hq, u0, hap⟩ := place ht2 hd2 a01 a02 a12
  have hcp := corner_pos ht1 hd1 ha.1 ha.2.1 (by rw [ha.2.2]; exact hc)
  have hcl := ha.1
  obtain ⟨a1, a2⟩ := a
  rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩
  · simp only [IsCornerPos] at hcp
    rcases hcp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact st0_0 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_1 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_2 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_3 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_4 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_5 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_6 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_7 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st0_8 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
  · simp only [IsCornerPos] at hcp
    rcases hcp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact st1_0 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_1 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_2 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_3 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_4 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_5 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_6 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_7 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st1_8 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
  · have hi : i < 3 := by omega
    simp only [IsCornerPos] at hcp
    obtain ⟨h1 | h1, h2 | h2⟩ := hcp <;> subst h1 <;> subst h2 <;> interval_cases i
    · exact st2_0 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st3_0 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st4_0 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st2_1 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st3_1 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st4_1 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st2_3 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st3_3 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st4_3 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st2_2 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st3_2 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1
    · exact st4_2 t d ht hd hp ha.2.2.symm hb.2.2.symm hq.2.2.symm u0 hap hb.2.1 hq.2.1

/-- **O2 absence** (`t, d ≥ 2`). -/
theorem o2_no_path (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) :
    ¬ ∃ n p, LiteralPath (o2Graph (t : ℤ) (d : ℤ)) n p := by
  rw [o2_iff_gm (one_le_of_two ht) (one_le_of_two hd)]
  exact no_path_gm t d ht hd

end Claude5O2
