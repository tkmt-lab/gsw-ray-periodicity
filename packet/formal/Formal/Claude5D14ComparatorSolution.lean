import Formal.ClaudeChallengeSpec
import Formal.Claude2AlignedSpec
import Formal.Claude5D14Spec
import Formal.Claude5D14Main

/-! Solution module for `lake comparator`: proves the challenge theorem `ClaudeChallengeD14.main`
of `Formal/Claude5D14ComparatorChallenge.lean` (D14 = Graver's D14(r,s)).  The definitions come
from `Formal.ClaudeChallengeSpec`, `Formal.Claude2AlignedSpec` and `Formal.Claude5D14Spec`, which
have the same definitions as the challenge; `PathExists` is restated here verbatim.

Proof: `d14Graph r s` is isomorphic to a "seam circle" graph (`Claude5D14.d14_iff_gm`): the two
hexagonal cells are the two charts, and a boundary point is recorded by its arclength on the
common seam circle.  There no edge has three common neighbours (`Claude5D14.no_three`), and for
`r, s ≥ 2` degree five means one of the twelve label corners (`Claude5D14.deg_five`) and each of
the 120 starts of a literal path lies on one of twelve closed strips whose odd-indexed points are
never corners (`Claude5D14.no_path_gm`).  For `r = 1` or `s = 1` explicit literal paths exist
(`Claude5D14.pe_R1`, `Claude5D14.pe_S1`), so on rays path existence is eventually constant
(`Claude5D14.d14_rays`). -/

namespace ClaudeChallengeD14

open ClaudeChallenge Claude2Aligned

/-- A literal path exists in D14(r,s). -/
def PathExists (r s : ℤ) : Prop := ∃ n p, LiteralPath (d14Graph r s) n p

/-- **D14 on rays**: on every integer ray `(r₀ + a n, s₀ + b n)` with `r₀, s₀ ≥ 1`, `a, b ≥ 0`,
literal-path existence in D14 is eventually periodic. -/
theorem main (r₀ s₀ a b : ℕ) (hr : 1 ≤ r₀) (hs : 1 ≤ s₀) :
    ∃ n₀ P : ℕ, 0 < P ∧ ∀ n : ℕ, n₀ ≤ n →
      (PathExists (r₀ + a * n) (s₀ + b * n) ↔
        PathExists (r₀ + a * (n + P)) (s₀ + b * (n + P))) := by
  obtain ⟨n₀, P, hP, h⟩ := Claude5D14.d14_rays r₀ s₀ a b hr hs
  refine ⟨n₀, P, hP, fun n hn => ?_⟩
  have h' := h n hn
  simp only [Claude5D14.PE] at h'
  push_cast at h'
  exact h'

end ClaudeChallengeD14
