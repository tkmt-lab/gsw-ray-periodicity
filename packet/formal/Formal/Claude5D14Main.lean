import Formal.Claude5D14Nec
import Formal.Claude5D14SuffR1
import Formal.Claude5D14SuffS1

/-!
# D14: absence for `r, s ≥ 2`, paths on the boundary, and rays

Written by a Claude worker (2026-10-20, D14 bridge session).

* `d14_no_path` (`Claude5D14Nec`) : no literal path for `r, s ≥ 2`;
* `pe_R1`, `pe_S1` : explicit literal paths in D14(1, s), `s ≥ 2`, and D14(r, 1), `r ≥ 2`;
* `d14_rays` : on every ray with natural starts `≥ 1` and natural slopes, path existence is
  eventually constant (period 1 from `n = 2` on).
-/

namespace Claude5D14

open ClaudeChallenge Claude2Aligned

/-- Path existence for natural parameters. -/
def PE (r s : ℕ) : Prop := ∃ n p, LiteralPath (d14Graph (r : ℤ) (s : ℤ)) n p

theorem pe_R1 (s : ℕ) (hs : 2 ≤ s) : PE 1 s :=
  (d14_iff_gm (by norm_num) (by exact_mod_cast (show 1 ≤ s by omega))).2 (fR1_lit 1 s rfl hs)

theorem pe_S1 (r : ℕ) (hr : 2 ≤ r) : PE r 1 :=
  (d14_iff_gm (by exact_mod_cast (show 1 ≤ r by omega)) (by norm_num)).2 (fS1_lit r 1 hr rfl)

theorem not_pe (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) : ¬ PE r s := d14_no_path r s hr hs

/-- **D14 on rays.** -/
theorem d14_rays (r₀ s₀ a b : ℕ) (hr : 1 ≤ r₀) (hs : 1 ≤ s₀) :
    ∃ n₀ P : ℕ, 0 < P ∧ ∀ n : ℕ, n₀ ≤ n →
      (PE (r₀ + a * n) (s₀ + b * n) ↔ PE (r₀ + a * (n + P)) (s₀ + b * (n + P))) := by
  refine ⟨2, 1, by norm_num, fun n hn => ?_⟩
  by_cases hA : a = 0 ∧ r₀ = 1
  · obtain ⟨rfl, rfl⟩ := hA
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · have h1 : 2 ≤ s₀ + b * n := by nlinarith
      have h2 : 2 ≤ s₀ + b * (n + 1) := by nlinarith
      simp only [zero_mul, add_zero]
      exact iff_of_true (pe_R1 _ h1) (pe_R1 _ h2)
  by_cases hB : b = 0 ∧ s₀ = 1
  · obtain ⟨rfl, rfl⟩ := hB
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have h1 : 2 ≤ r₀ + a * n := by nlinarith
      have h2 : 2 ≤ r₀ + a * (n + 1) := by nlinarith
      simp only [zero_mul, add_zero]
      exact iff_of_true (pe_S1 _ h1) (pe_S1 _ h2)
  have hR : ∀ m, 2 ≤ m → 2 ≤ r₀ + a * m := by
    intro m hm
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · omega
    · nlinarith
  have hS : ∀ m, 2 ≤ m → 2 ≤ s₀ + b * m := by
    intro m hm
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · omega
    · nlinarith
  exact iff_of_false (not_pe _ _ (hR n hn) (hS n hn)) (not_pe _ _ (hR _ (by omega)) (hS _ (by omega)))

end Claude5D14
