import Formal.Claude4C1Main

/-! Solution module for `lake comparator`: proves the challenge theorems
`ClaudeChallengeC1.classification` and `ClaudeChallengeC1.main` of
`Formal/Claude4C1ComparatorChallenge.lean` (C1 = Graver's truncated tetrahedron).  The definitions
come from `Formal.ClaudeChallengeSpec`, `Formal.Claude2AlignedSpec` and `Formal.Claude4C1Spec`,
which have the same definitions as the challenge; `PathExists` is restated here verbatim.

Proof: `c1Graph r s` is isomorphic to a graph on the lattice points of the truncated simplex
surface in `ℤ⁴` (`Claude4C1.c1_iff_g4`); there, no edge has three common neighbours, degrees are
5 exactly at the twelve corners, the forced walks from a corner are explicit strips whose
odd-indexed vertices are never corners when `s ≥ 2` (`Claude4C1.c1_no_path`), and for `s = 1`
an explicit strip of `4r + 2` vertices is a literal path (`Claude4C1.c1_path_s1`).  On rays,
`s = 1` is eventually constant (`Claude4C1.c1_rays`). -/

namespace ClaudeChallengeC1

open ClaudeChallenge Claude2Aligned

/-- A literal path exists in C1(r,s). -/
def PathExists (r s : ℤ) : Prop := ∃ n p, LiteralPath (c1Graph r s) n p

/-- **C1 classification**: for `r, s ≥ 1`, a literal path exists iff `s = 1`. -/
theorem classification (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) : PathExists r s ↔ s = 1 := by
  exact Claude4C1.c1_classification r s hr hs

/-- **C1 on rays**: on every integer ray `(r₀ + a t, s₀ + b t)` with `r₀, s₀ ≥ 1`, `a, b ≥ 0`,
literal-path existence in C1 is eventually periodic. -/
theorem main (r₀ s₀ a b : ℕ) (hr : 1 ≤ r₀) (hs : 1 ≤ s₀) :
    ∃ t₀ P : ℕ, 0 < P ∧ ∀ t : ℕ, t₀ ≤ t →
      (PathExists (r₀ + a * t) (s₀ + b * t) ↔
        PathExists (r₀ + a * (t + P)) (s₀ + b * (t + P))) := by
  obtain ⟨t₀, P, hP, h⟩ := Claude4C1.c1_rays r₀ s₀ a b hr hs
  refine ⟨t₀, P, hP, fun t ht => ?_⟩
  have h' := h t ht
  push_cast at h'
  exact h'

end ClaudeChallengeC1
