import Formal.Claude3StateCond
import Formal.Claude3StateExtract

/-!
# Theorem 1a, G5: the reduction theorem

Written by a Claude worker (2026-10-20, Theorem 1a, parts G4/G5).

* `reduction : ReductionStatement` : under `Valid S t` and `TrianglesInCharts S t`,
  `PathExists S t ↔ ∃ X ⊆ St stLo stHi t, Cond t X` (paper `lem:mso-path`, both directions).
* `reduction_core : ReductionCoreStatement` : the same with `CondCore` (no connectivity).
* `reduction_eventually` : the form used for `MainStatement`: under the hypothesis of
  `MainStatement`, the equivalence holds for all `t ≥ t₁`.
* `geo_trianglesInCharts_iff` : the geometry files' `Geo.TrianglesInCharts` is the spec's.
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo

theorem geo_trianglesInCharts_iff (S : Sig) (t : ℕ) :
    Geo.TrianglesInCharts S t ↔ ClaudeChallenge2.TrianglesInCharts S t := Iff.rfl

/-- **G5, the reduction theorem.** -/
theorem reduction : ReductionStatement := fun _ _ hV hTC =>
  ⟨cond_of_pathExists hV hTC, fun ⟨_, hX, hC⟩ => pathExists_of_cond hV hX hC⟩

/-- The reduction theorem with the conditions without connectivity. -/
theorem reduction_core : ReductionCoreStatement := fun _ _ hV hTC =>
  ⟨fun h => by
    obtain ⟨X, hX, hC⟩ := cond_of_pathExists hV hTC h
    exact ⟨X, hX, hC.core⟩,
   fun ⟨_, hX, hC⟩ => pathExists_of_condCore hV hX hC⟩

/-- Under the hypothesis of `MainStatement`, the reduction holds for all large `t`. -/
theorem reduction_eventually (S : Sig) (t₁ : ℕ)
    (h : ∀ t, t₁ ≤ t → Valid S t ∧ ClaudeChallenge2.TrianglesInCharts S t) :
    ∀ t, t₁ ≤ t →
      (PathExists S t ↔ ∃ X ⊆ R002.Claude3Fold.St (stLo (S := S)) stHi t, Cond t X) :=
  fun t ht => reduction S t (h t ht).1 (h t ht).2

end ClaudeChallenge2.State
