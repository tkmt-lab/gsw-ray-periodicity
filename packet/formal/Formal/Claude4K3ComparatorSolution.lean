import Formal.Claude4K3NoThree
import Formal.Claude4K3BndPath

/-! Solution module for `lake comparator`: proves the challenge theorem `ClaudeChallengeK3.main`
of `Formal/Claude4K3ComparatorChallenge.lean` (K3 on rays, version 2: `r₀, s₀ ≥ 1`).  The
definitions come from `Formal.ClaudeChallengeSpec` and `Formal.Claude2AlignedSpec`, which have the
same definitions as the challenge; `PathExists` is restated here verbatim.

Proof: the K3 classification `Claude4K3.k3_statement` (from `Claude4K3.noThree`: no edge of
K3(r,s), `r, s ≥ 2`, has three common neighbours), explicit literal paths in the boundary families
K3(1, s) and K3(r, 1) (`Claude4K3.pe_R1`, `Claude4K3.pe_S1`), and the ray arithmetic
`Claude4K3.main_of_K3Statement`. -/

namespace ClaudeChallengeK3

open ClaudeChallenge Claude2Aligned

/-- A literal path exists in K3(r,s). -/
def PathExists (r s : ℤ) : Prop := ∃ n p, LiteralPath (k3Graph r s) n p

/-- **K3 on rays**: on every integer ray `(r₀ + a t, s₀ + b t)` with `r₀, s₀ ≥ 1`, `a, b ≥ 0`,
literal-path existence in K3 is eventually periodic. -/
theorem main (r₀ s₀ a b : ℕ) (hr : 1 ≤ r₀) (hs : 1 ≤ s₀) :
    ∃ t₀ P : ℕ, 0 < P ∧ ∀ t : ℕ, t₀ ≤ t →
      (PathExists (r₀ + a * t) (s₀ + b * t) ↔
        PathExists (r₀ + a * (t + P)) (s₀ + b * (t + P))) := by
  obtain ⟨t₀, P, hP, h⟩ := Claude4K3.main_of_K3Statement Claude4K3.k3_statement Claude4K3.pe_R1
    Claude4K3.pe_S1 r₀ s₀ a b hr hs
  refine ⟨t₀, P, hP, fun t ht => ?_⟩
  have h' := h t ht
  push_cast at h'
  exact h'

end ClaudeChallengeK3

