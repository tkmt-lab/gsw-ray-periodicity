import Formal.Claude5E10SigAdj
import Formal.Claude3Thm1a

/-!
# E10: Theorem 1a applied to the signature `e10S Q`

Written by a Claude worker (2026-10-21, E10 bridge session).  Kept small: importing Theorem 1a
(`ClaudeChallenge2.State.main_statement`) is the memory-heavy part.

* `t1a_gm : T1aGM` : on an affine family with `Hyp` eventually, path existence in the model is
  eventually periodic.
-/

namespace Claude5E10

theorem t1a_gm : T1aGM := by
  intro Q t₁ hH
  obtain ⟨t₀, P, hP, h⟩ := ClaudeChallenge2.State.main_statement (e10S Q) t₁
    (fun t ht => valid_e10S (hH t ht))
  refine ⟨max t₀ t₁, P, hP, fun t ht => ?_⟩
  beta_reduce
  rw [← path_iff (hH t (by omega)), ← path_iff (hH (t + P) (by omega))]
  exact h t (by omega)

end Claude5E10
