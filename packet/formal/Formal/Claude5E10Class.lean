import Formal.Claude5E10MClass
import Formal.Claude5E10GZ0C
import Formal.Claude5E10GZ1C
import Formal.Claude5E10GZ2C
import Formal.Claude5E10GLt0C
import Formal.Claude5E10GLt1C
import Formal.Claude5E10GLt2C
import Formal.Claude5E10GEq0C
import Formal.Claude5E10GEq1C
import Formal.Claude5E10GEq2C
import Formal.Claude5E10GGt0C
import Formal.Claude5E10GGt1C
import Formal.Claude5E10GGt2C

/-!
# E10: the spec surface is the model, and the classification for `r ≥ 2`

Written by a Claude worker (2026-10-20, E10 bridge session).

* `e10_iff_gm` : for `p, r, s ≥ 1`, literal paths in E10(p,r,s) correspond to literal paths in
  the model with twist `w = p mod 3m` (case by case over `k = p mod m` and `j = (p div m) mod 3`);
* `e10_classify` : for `r ≥ 2`, a literal path exists iff `p mod m` is one of
  `1, r + 1, r + s + 1, m − 1, r − 1, r + s − 1`.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

theorem twist_eq {p m : ℤ} (hm : 0 < m) :
    p % (3 * m) = (p / m % 3) * m + p % m ∧ 0 ≤ p / m % 3 ∧ p / m % 3 < 3 := by
  have h1 := Int.mul_ediv_add_emod p m
  have h2 := Int.mul_ediv_add_emod (p / m) 3
  have a1 := Int.emod_nonneg p (show m ≠ 0 by omega)
  have a2 := Int.emod_lt_of_pos p hm
  have b1 := Int.emod_nonneg (p / m) (show (3 : ℤ) ≠ 0 by omega)
  have b2 := Int.emod_lt_of_pos (p / m) (show (0 : ℤ) < 3 by omega)
  refine ⟨?_, b1, b2⟩
  generalize p % m = k at h1 a1 a2 ⊢
  generalize p / m % 3 = j at h2 b1 b2 ⊢
  generalize p / m / 3 = q at h2
  generalize p / m = d at h1 h2
  have hlt : j * m + k < 3 * m := by nlinarith
  have hge : 0 ≤ j * m + k := by nlinarith
  exact emod_eq_of (by omega) (q := q) (b := j * m + k) (by rw [← h1, ← h2]; ring) hge hlt

theorem e10_iff_gm {p r s : ℤ} (hp : 1 ≤ p) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    (∃ n q, LiteralPath (e10Graph p r s) n q) ↔
      (∃ n q, LiteralPath (GM p r s (p % (3 * (2 * r + s)))) n q) := by
  have hm : 0 < 2 * r + s := by omega
  obtain ⟨hw, hj0, hj3⟩ := twist_eq (p := p) hm
  have H : Hyp p r s (p % (3 * (2 * r + s))) :=
    ⟨hp, hr, hs, Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  have hk0 := Int.emod_nonneg p (show 2 * r + s ≠ 0 by omega)
  have hk1 := Int.emod_lt_of_pos p hm
  set k := p % (2 * r + s) with hk
  set j := p / (2 * r + s) % 3 with hj
  have hkk : p % (2 * r + s) = k := rfl
  have hjj : p / (2 * r + s) % 3 = j := rfl
  set w := p % (3 * (2 * r + s))
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with e | e | e <;> rw [e] at hjj hw <;>
    rcases (show k = 0 ∨ (0 < k ∧ k < r) ∨ k = r ∨ r < k by omega) with c | c | c | c
  · exact e10_iff_gm_of H (GZ0.isoOK H hr hs hp hkk c hjj hw)
  · exact e10_iff_gm_of H (GLt0.isoOK H hr hs hp hkk c hjj hw)
  · exact e10_iff_gm_of H (GEq0.isoOK H hr hs hp hkk c hjj hw)
  · exact e10_iff_gm_of H (GGt0.isoOK H hr hs hp hkk c hjj hw)
  · exact e10_iff_gm_of H (GZ1.isoOK H hr hs hp hkk c hjj hw)
  · exact e10_iff_gm_of H (GLt1.isoOK H hr hs hp hkk c hjj hw)
  · exact e10_iff_gm_of H (GEq1.isoOK H hr hs hp hkk c hjj hw)
  · exact e10_iff_gm_of H (GGt1.isoOK H hr hs hp hkk c hjj hw)
  · exact e10_iff_gm_of H (GZ2.isoOK H hr hs hp hkk c hjj hw)
  · exact e10_iff_gm_of H (GLt2.isoOK H hr hs hp hkk c hjj hw)
  · exact e10_iff_gm_of H (GEq2.isoOK H hr hs hp hkk c hjj hw)
  · exact e10_iff_gm_of H (GGt2.isoOK H hr hs hp hkk c hjj hw)

/-- **Classification for `r ≥ 2`** (in terms of `p mod m`). -/
theorem e10_classify {p r s : ℤ} (hp : 1 ≤ p) (hr : 2 ≤ r) (hs : 1 ≤ s) :
    (∃ n q, LiteralPath (e10Graph p r s) n q) ↔
      (p % (2 * r + s) = 1 ∨ p % (2 * r + s) = r + 1 ∨ p % (2 * r + s) = r + s + 1 ∨
        p % (2 * r + s) = 2 * r + s - 1 ∨ p % (2 * r + s) = r - 1 ∨ p % (2 * r + s) = r + s - 1) := by
  have hm : 0 < 2 * r + s := by omega
  rw [e10_iff_gm hp (by omega) hs]
  obtain ⟨hw, hj0, hj3⟩ := twist_eq (p := p) hm
  have H : Hyp p r s (p % (3 * (2 * r + s))) :=
    ⟨hp, by omega, hs, Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  exact model_classify H hr (Int.emod_nonneg _ (by omega)) (Int.emod_lt_of_pos _ hm) hj0
    (by omega) hw (b := p / (2 * r + s)) (by have := Int.mul_ediv_add_emod p (2 * r + s); linarith)

end Claude5E10
