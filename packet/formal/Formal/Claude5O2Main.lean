import Formal.Claude5O2Nec
import Formal.Claude5O2SuffT1D
import Formal.Claude5O2SuffD1D

/-!
# O2: classification and rays

Written by a Claude worker (2026-10-20, O2 bridge session).

* `o2_no_path` (`Claude5O2Nec`) : no literal path for `t, d ≥ 2`;
* `pe_T1`, `pe_D1` : explicit literal paths in O2(1, d), `d ≥ 3`, and O2(t, 1), `t ≥ 3`;
* `o2_rays` : on every ray with natural starts `≥ 1` and natural slopes, path existence is
  eventually constant (period 1 from `n = 3` on).
-/

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

/-- Path existence for natural parameters. -/
def PE (t d : ℕ) : Prop := ∃ n p, LiteralPath (o2Graph (t : ℤ) (d : ℤ)) n p

theorem pe_T1 (d : ℕ) (hd : 3 ≤ d) : PE 1 d :=
  (o2_iff_gm (by norm_num) (by exact_mod_cast (show 1 ≤ d by omega))).2 (fT1_lit 1 d rfl hd)

theorem pe_D1 (t : ℕ) (ht : 3 ≤ t) : PE t 1 :=
  (o2_iff_gm (by exact_mod_cast (show 1 ≤ t by omega)) (by norm_num)).2 (fD1_lit t 1 ht rfl)

theorem not_pe (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) : ¬ PE t d := o2_no_path t d ht hd

/-- **O2 on rays.** -/
theorem o2_rays (t₀ d₀ a b : ℕ) (ht : 1 ≤ t₀) (hd : 1 ≤ d₀) :
    ∃ n₀ P : ℕ, 0 < P ∧ ∀ n : ℕ, n₀ ≤ n →
      (PE (t₀ + a * n) (d₀ + b * n) ↔ PE (t₀ + a * (n + P)) (d₀ + b * (n + P))) := by
  refine ⟨3, 1, by norm_num, fun n hn => ?_⟩
  by_cases hA : a = 0 ∧ t₀ = 1
  · obtain ⟨rfl, rfl⟩ := hA
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · have h1 : 3 ≤ d₀ + b * n := by nlinarith
      have h2 : 3 ≤ d₀ + b * (n + 1) := by nlinarith
      simp only [zero_mul, add_zero]
      exact iff_of_true (pe_T1 _ h1) (pe_T1 _ h2)
  by_cases hB : b = 0 ∧ d₀ = 1
  · obtain ⟨rfl, rfl⟩ := hB
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have h1 : 3 ≤ t₀ + a * n := by nlinarith
      have h2 : 3 ≤ t₀ + a * (n + 1) := by nlinarith
      simp only [zero_mul, add_zero]
      exact iff_of_true (pe_D1 _ h1) (pe_D1 _ h2)
  have hT : ∀ m, 3 ≤ m → 2 ≤ t₀ + a * m := by
    intro m hm
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · omega
    · nlinarith
  have hD : ∀ m, 3 ≤ m → 2 ≤ d₀ + b * m := by
    intro m hm
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · omega
    · nlinarith
  exact iff_of_false (not_pe _ _ (hT n hn) (hD n hn)) (not_pe _ _ (hT _ (by omega)) (hD _ (by omega)))

end Claude5O2
