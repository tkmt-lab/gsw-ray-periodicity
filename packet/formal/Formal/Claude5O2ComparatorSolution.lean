import Formal.Claude5O2Spec
import Formal.Claude5O2Main

/-! Solution module for `lake comparator`: proves the challenge theorems
`ClaudeChallengeO2.classification` and `ClaudeChallengeO2.main` of
`Formal/Claude5O2ComparatorChallenge.lean` (O2 = Graver's O2(t,d)).  The definitions come from
`Formal.ClaudeChallengeSpec`, `Formal.Claude2AlignedSpec` and `Formal.Claude5O2Spec`, which have
the same definitions as the challenge; `PathExists` is restated here verbatim.

Proof: `o2Graph t d` is isomorphic to a "pillow and pockets" graph (`Claude5O2.o2_iff_gm`): the two
hexagons are the same hexagon on two sheets sewn along the `d`-sides, with a rhombus inserted in
each `2t`-side.  There, for `t, d ≥ 2`, no edge has three common neighbours
(`Claude5O2.no_three`), degree five means corner (`Claude5O2.deg_five`), and each of the 120
starts of a literal path lies on one of ten closed strips whose odd-indexed points are never
corners (`Claude5O2.no_path_gm`).  For `t = 1` or `d = 1` explicit literal paths exist
(`Claude5O2.pe_T1`, `Claude5O2.pe_D1`), so on rays path existence is eventually constant
(`Claude5O2.o2_rays`). -/

namespace ClaudeChallengeO2

open ClaudeChallenge Claude2Aligned

/-- A literal path exists in O2(t,d). -/
def PathExists (t d : ℤ) : Prop := ∃ n p, LiteralPath (o2Graph t d) n p

/-- **O2 absence**: for `t, d ≥ 2`, O2(t,d) has no literal path. -/
theorem classification (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) : ¬ PathExists t d := by
  exact Claude5O2.o2_no_path t d ht hd

/-- **O2 on rays**: on every integer ray `(t₀ + a n, d₀ + b n)` with `t₀, d₀ ≥ 1`, `a, b ≥ 0`,
literal-path existence in O2 is eventually periodic. -/
theorem main (t₀ d₀ a b : ℕ) (ht : 1 ≤ t₀) (hd : 1 ≤ d₀) :
    ∃ n₀ P : ℕ, 0 < P ∧ ∀ n : ℕ, n₀ ≤ n →
      (PathExists (t₀ + a * n) (d₀ + b * n) ↔
        PathExists (t₀ + a * (n + P)) (d₀ + b * (n + P))) := by
  obtain ⟨n₀, P, hP, h⟩ := Claude5O2.o2_rays t₀ d₀ a b ht hd
  refine ⟨n₀, P, hP, fun n hn => ?_⟩
  have h' := h n hn
  simp only [Claude5O2.PE] at h'
  push_cast at h'
  exact h'

end ClaudeChallengeO2
