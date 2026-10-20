import Mathlib.Order.RelClasses
import Mathlib.Tactic

/-! AH's termination measure, for accelerated blocks, not individual zero-loser
Rauzy steps. The link from permutations and affine lengths to these blocks is
NOT formalised here. The bounded scan to the next positive-slope loser must be
grouped with that subtraction before invoking the measure theorem. -/
namespace R002

abbrev InductionRank := ℕ × (ℕ × ℕ)

def inductionRankLT : InductionRank → InductionRank → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

theorem inductionRank_wellFounded : WellFounded inductionRankLT :=
  Nat.lt_wfRel.wf.prod_lex (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)

theorem inductionRank_slope {s s' n n' c c' : ℕ} (h : s' < s) :
    inductionRankLT (s', n', c') (s, n, c) :=
  Prod.Lex.left _ _ h

theorem inductionRank_labels {s n n' c c' : ℕ} (h : n' < n) :
    inductionRankLT (s, n', c') (s, n, c) :=
  Prod.Lex.right _ (Prod.Lex.left _ _ h)

theorem inductionRank_constant {s n c c' : ℕ} (h : c' < c) :
    inductionRankLT (s, n, c') (s, n, c) :=
  Prod.Lex.right _ (Prod.Lex.right _ h)

/-- Subtracting a positive-slope loser from a winner reduces total slope.
The constants and label counts may change arbitrarily in this case. -/
theorem induction_subtract_positive (a b rest n n' c c' : ℕ)
    (hb : 0 < b) (hba : b ≤ a) :
    inductionRankLT (a - b + b + rest, n', c') (a + b + rest, n, c) := by
  apply inductionRank_slope
  omega

/-- A full constant-suffix acceleration replaces the positive winner slope by 0. -/
theorem induction_accelerate_constant (a rest n n' c c' : ℕ) (ha : 0 < a) :
    inductionRankLT (rest, n', c') (a + rest, n, c) := by
  apply inductionRank_slope
  omega

/-- The constant-constant subtraction decreases constant mass when slopes
and active-label counts are unchanged. -/
theorem induction_subtract_constant (w l rest s n : ℕ)
    (hl : 0 < l) (hlw : l ≤ w) :
    inductionRankLT (s, n, w - l + l + rest) (s, n, w + l + rest) := by
  apply inductionRank_constant
  omega

/-- Erasing a label with non-increasing slope sum is a strict rank decrease. -/
theorem induction_erase (s s' n c c' : ℕ) (hs : s' ≤ s) :
    inductionRankLT (s', n, c') (s, n + 1, c) := by
  rcases lt_or_eq_of_le hs with h | h
  · exact inductionRank_slope h
  · subst s'
    exact inductionRank_labels (by omega)

/-- Every block relation whose actual rank decreases is well-founded.
This is a conditional interface: no IET transition correspondence is hidden. -/
theorem induction_blocks_wellFounded {α : Type*} (rank : α → InductionRank)
    (step : α → α → Prop)
    (decreases : ∀ x y, step x y → inductionRankLT (rank x) (rank y)) :
    WellFounded step := by
  exact (InvImage.wf rank inductionRank_wellFounded).mono decreases

/-- A deterministic block process has some finite index at which it stops.
The result is not a uniform numerical bound across all parameter values. -/
theorem induction_no_infinite_run {α : Type*} (rank : α → InductionRank)
    (step : α → α → Prop)
    (decreases : ∀ x y, step x y → inductionRankLT (rank x) (rank y))
    (run : ℕ → α) : ∃ n, ¬ step (run (n + 1)) (run n) := by
  classical
  by_contra h
  push Not at h
  have wf := induction_blocks_wellFounded rank step decreases
  have impossible : ∀ x, Acc step x → ∀ n, run n = x → False := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      intro n hn
      exact ih (run (n + 1)) (by simpa [hn] using h n) (n + 1) rfl
  exact impossible (run 0) (wf.apply (run 0)) 0 rfl

/-- Length of an arbitrary branch of a finitely branching symbolic tree. -/
inductive InductionBranch {α : Type*} (children : α → List α) : α → ℕ → Prop
  | zero (x : α) : InductionBranch children x 0
  | step {x y : α} {n : ℕ} : y ∈ children x →
      InductionBranch children y n → InductionBranch children x (n + 1)

/-- Finite branching upgrades termination to a uniform depth bound for all
symbolic residue branches rooted at the same state. The concrete affine IET
compiler must still be shown to supply such a finite child list and decrease. -/
theorem induction_uniform_depth {α : Type*} (rank : α → InductionRank)
    (children : α → List α)
    (decreases : ∀ x y, y ∈ children x → inductionRankLT (rank y) (rank x)) :
    ∀ x, ∃ B : ℕ, ∀ n, InductionBranch children x n → n ≤ B := by
  classical
  intro x
  induction x using (InvImage.wf rank inductionRank_wellFounded).induction with
  | h x ih =>
    let bound : α → ℕ := fun y =>
      if hy : y ∈ children x then Classical.choose (ih y (decreases x y hy)) else 0
    have hb : ∀ y, y ∈ children x → ∀ n, InductionBranch children y n → n ≤ bound y := by
      intro y hy n hn
      simpa only [bound, dite_eq_left hy] using
        (Classical.choose_spec (ih y (decreases x y hy)) n hn)
    refine ⟨(children x).toFinset.sup bound + 1, ?_⟩
    intro n hn
    cases hn with
    | zero => omega
    | step hy hm =>
      exact Nat.succ_le_succ ((hb _ hy _ hm).trans
        (Finset.le_sup (by simpa only [List.mem_toFinset] using hy)))

#print axioms inductionRank_wellFounded
#print axioms induction_subtract_positive
#print axioms induction_accelerate_constant
#print axioms induction_subtract_constant
#print axioms induction_erase
#print axioms induction_blocks_wellFounded
#print axioms induction_no_infinite_run
#print axioms induction_uniform_depth
end R002
