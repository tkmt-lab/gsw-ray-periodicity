import Formal.Claude3Thm1a

/-! Solution module for `lake comparator`: proves the challenge theorem `ClaudeChallenge2.main`
of `Formal/Claude3ComparatorChallenge.lean` (Theorem 1a, specification version 2). The
definitions come from `Formal.Claude3ChallengeSpec`, which has the same definitions as the
challenge. -/

namespace ClaudeChallenge2

theorem main (S : Sig) (t₁ : ℕ) (hval : ∀ t, t₁ ≤ t → Valid S t ∧ TrianglesInCharts S t) :
    ∃ t₀ P : ℕ, 0 < P ∧ ∀ t, t₀ ≤ t → (PathExists S t ↔ PathExists S (t + P)) :=
  State.main_statement S t₁ hval

end ClaudeChallenge2
