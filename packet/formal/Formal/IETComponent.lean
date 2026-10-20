import Formal.AffineInduction
import Mathlib.Data.List.Perm.Basic

/-! The actual terminal-component branch of the two-row IET compiler.
This does not formalise subtraction, ties, acceleration, or surface geometry. -/
namespace R002

structure IETRows (α : Type*) where
  top : List α
  bottom : List α

def ietComponentChildren {α : Type*} [DecidableEq α] (s : IETRows α) : List (IETRows α) :=
  match s.top.reverse, s.bottom.reverse with
  | a :: xs, b :: ys => if a = b then [⟨xs.reverse, ys.reverse⟩] else []
  | _, _ => []

def ietComponentRank {α : Type*} (slope : α → ℕ) (s : IETRows α) : InductionRank :=
  ((s.top.map slope).sum, s.top.length, 0)

/-- Removing a common last label preserves the two-row permutation invariant. -/
theorem iet_component_perm {α : Type*} [DecidableEq α] {s c : IETRows α}
    (hp : s.top.Perm s.bottom) (hc : c ∈ ietComponentChildren s) :
    c.top.Perm c.bottom := by
  unfold ietComponentChildren at hc
  cases ht : s.top.reverse with
  | nil => simp [ht] at hc
  | cons a xs =>
    cases hb : s.bottom.reverse with
    | nil => simp [ht, hb] at hc
    | cons b ys =>
      by_cases h : a = b
      · subst b
        simp [ht, hb] at hc
        subst c
        have hh : (a :: xs).Perm (a :: ys) := by
          simpa [ht, hb] using (List.reverse_perm s.top).trans (hp.trans (List.reverse_perm s.bottom).symm)
        exact (List.reverse_perm xs).trans (hh.cons_inv.trans (List.reverse_perm ys).symm)
      · simp [ht, hb, h] at hc

/-- This concrete child list decreases the existing lexicographic rank. -/
theorem iet_component_rank {α : Type*} [DecidableEq α] (slope : α → ℕ)
    {s c : IETRows α} (hc : c ∈ ietComponentChildren s) :
    inductionRankLT (ietComponentRank slope c) (ietComponentRank slope s) := by
  unfold ietComponentChildren at hc
  cases ht : s.top.reverse with
  | nil => simp [ht] at hc
  | cons a xs =>
    cases hb : s.bottom.reverse with
    | nil => simp [ht, hb] at hc
    | cons b ys =>
      by_cases h : a = b
      · simp [ht, hb, h] at hc
        subst c
        have hs : s.top = xs.reverse ++ [a] := by
          have := congrArg List.reverse ht
          simpa using this
        simp only [ietComponentRank, hs, List.map_append, List.map_cons,
          List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
          List.length_append, List.length_singleton]
        exact induction_erase _ _ _ _ _ (by omega)
      · simp [ht, hb, h] at hc

/-- The abstract finite-branch theorem now applies to this concrete branch. -/
theorem iet_component_uniform_depth {α : Type*} [DecidableEq α] (slope : α → ℕ)
    (s : IETRows α) : ∃ B : ℕ, ∀ n, InductionBranch ietComponentChildren s n → n ≤ B :=
  induction_uniform_depth (ietComponentRank slope) ietComponentChildren
    (fun _ _ h => iet_component_rank slope h) s

#print axioms iet_component_perm
#print axioms iet_component_rank
#print axioms iet_component_uniform_depth
end R002
