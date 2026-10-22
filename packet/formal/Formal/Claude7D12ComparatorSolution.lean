import Formal.ClaudeChallengeSpec
import Formal.Claude2AlignedSpec
import Formal.Claude7D12Spec
import Formal.Claude7D12Main

/-! Solution module for `lake comparator`: proves the challenge theorems
`ClaudeChallengeD12.classification` and `ClaudeChallengeD12.main` of
`Formal/Claude7D12ComparatorChallenge.lean` (D12 = Graver's D12(r,s)).  The definitions come from
`Formal.ClaudeChallengeSpec`, `Formal.Claude2AlignedSpec` and `Formal.Claude7D12Spec`, which have
the same definitions as the challenge; `PathExists` is restated here verbatim.

Proof (namespace `Claude7D12`): `d12Graph r s` is isomorphic to a seam-circle model (two
hexagons glued along their boundary circle with the corners shifted by `s`, `d12_iff_gm`).
Necessity (`d12_no_path`, `r, s ≥ 2`): every corner is moved to the label-0 point by an
automorphism (`to_label0`); the ten first triangles there (`no_label0`) give strips that repeat a
vertex before any corner at an odd index — finitely many polyhedral leaves in `(r, s)`
(`n*_kill`) and, for four starts and `s ≥ r + 2`, strips winding `Q` laps around the sphere
(induction on the laps, `sp*_K*`).  Sufficiency (`path_gm`): explicit literal paths for
`r = 1`, `s = 1`, `r = 3s ± 1`, `s = r ± 1` and the winding paths for `s = q r ± 1`, `q ≥ 2`,
whose points are shown distinct (`inj_laps`).  On rays the condition is eventually periodic
(`evper_cond`). -/

namespace ClaudeChallengeD12

open ClaudeChallenge Claude2Aligned

/-- A literal path exists in D12(r,s). -/
def PathExists (r s : ℤ) : Prop := ∃ n p, LiteralPath (d12Graph r s) n p

/-- **D12 classification**: for `r, s ≥ 1`, a literal path exists iff `r ∣ s - 1` or
`r ∣ s + 1` or `|r - 3s| = 1`. -/
theorem classification (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    PathExists r s ↔
      ((r : ℤ) ∣ (s : ℤ) - 1 ∨ (r : ℤ) ∣ (s : ℤ) + 1 ∨ |(r : ℤ) - 3 * (s : ℤ)| = 1) := by
  exact Claude7D12.d12_classification r s hr hs

/-- **D12 on rays**: on every integer ray `(r₀ + a n, s₀ + b n)` with `r₀, s₀ ≥ 1`, `a, b ≥ 0`,
literal-path existence in D12 is eventually periodic. -/
theorem main (r₀ s₀ a b : ℕ) (hr : 1 ≤ r₀) (hs : 1 ≤ s₀) :
    ∃ n₀ P : ℕ, 0 < P ∧ ∀ n : ℕ, n₀ ≤ n →
      (PathExists (r₀ + a * n) (s₀ + b * n) ↔
        PathExists (r₀ + a * (n + P)) (s₀ + b * (n + P))) := by
  obtain ⟨n₀, P, hP, h⟩ := Claude7D12.d12_rays r₀ s₀ a b hr hs
  refine ⟨n₀, P, hP, fun n hn => ?_⟩
  have h' := h n hn
  simp only [PathExists]
  push_cast at h' ⊢
  exact h'

end ClaudeChallengeD12
