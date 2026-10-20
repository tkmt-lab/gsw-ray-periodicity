import Formal.Claude3ComparatorSolution

/-!
# Theorem 1a, residue-class variant

Written by Claude (coordinator), 2026-10-20.

The paper's Theorem 1a also allows the hypotheses to hold on finitely many residue classes
separately: for each class `c` modulo `m` a fixed signature `S c` describes the members
`m t + c` of the family. If, on each class, the decision agrees with literal-path existence for
`S c` and the signatures are valid for all large `t`, then the decision is eventually periodic
in the original parameter. This follows from `ClaudeChallenge2.main` on each class.
-/

namespace ClaudeChallenge2

/-- Iterating an eventual period. -/
theorem iter_period {A : ℕ → Prop} {t₀ P : ℕ} (h : ∀ t, t₀ ≤ t → (A t ↔ A (t + P))) :
    ∀ k t, t₀ ≤ t → (A t ↔ A (t + k * P)) := by
  intro k
  induction k with
  | zero => intro t _; simp
  | succ k ih =>
    intro t ht
    rw [ih t ht, h (t + k * P) (by omega), show t + k * P + P = t + (k + 1) * P by ring]

/-- **Theorem 1a, residue-class variant.** `D n` is the decision for the family member with
parameter `n`; on the class `c` modulo `m` it is literal-path existence for `S c`. -/
theorem main_residue (D : ℕ → Prop) (m : ℕ) (hm : 0 < m) (S : Fin m → Sig) (t₁ : ℕ)
    (hval : ∀ c t, t₁ ≤ t → Valid (S c) t ∧ TrianglesInCharts (S c) t)
    (hD : ∀ c : Fin m, ∀ t, t₁ ≤ t → (D (m * t + c) ↔ PathExists (S c) t)) :
    ∃ n₀ Q : ℕ, 0 < Q ∧ ∀ n, n₀ ≤ n → (D n ↔ D (n + Q)) := by
  choose t₀ P hP hper using fun c => main (S c) t₁ (hval c)
  set T := t₁ + ∑ c, t₀ c with hTdef
  set Q₀ := ∏ c, P c with hQdef
  have hQ₀ : 0 < Q₀ := Finset.prod_pos fun c _ => hP c
  refine ⟨m * T, m * Q₀, Nat.mul_pos hm hQ₀, fun n hn => ?_⟩
  set c : Fin m := ⟨n % m, Nat.mod_lt _ hm⟩
  set t := n / m
  have hn' : n = m * t + c := (Nat.div_add_mod n m).symm
  have hT : T ≤ t := (Nat.le_div_iff_mul_le hm).2 (by rw [mul_comm]; exact hn)
  have ht₁ : t₁ ≤ t := le_trans (Nat.le_add_right _ _) hT
  have ht₀ : t₀ c ≤ t :=
    le_trans (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c))
      (Nat.le_add_left _ _)) hT
  obtain ⟨k, hk⟩ : P c ∣ Q₀ := Finset.dvd_prod_of_mem _ (Finset.mem_univ c)
  have hnQ : n + m * Q₀ = m * (t + Q₀) + c := by rw [hn']; ring
  rw [hnQ, hn', hD c t ht₁, hD c (t + Q₀) (by omega), hk, mul_comm (P c) k]
  exact iter_period (hper c) k t ht₀

end ClaudeChallenge2
