import Formal.ClaudePosMain
import Formal.GCNegCriterion

/-!
# The primitive case of `ClaudeChallenge.main`

Combines the main team's necessity (`R002.GCNeg.primitive_criterion_necessary`) with the
coordinator side's sufficiency (`ClaudePos.criterion_sufficient`), both stated on the
coordinator's independent challenge graph `ClaudeChallenge.gcGraph`.
The nonprimitive case (gcd > 1) is not covered here.
-/

namespace ClaudeMain

theorem main_primitive (k l : ℕ) (hl : 0 < l) (hlk : l < k) (hp : Nat.gcd k l = 1) :
    (∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) n p) ↔
      ClaudeChallenge.criterion k l :=
  ⟨R002.GCNeg.primitive_criterion_necessary k l hlk hl hp,
    ClaudePos.criterion_sufficient k l hl hlk⟩

end ClaudeMain
