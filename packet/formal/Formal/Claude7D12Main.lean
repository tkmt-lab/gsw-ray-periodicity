import Formal.Claude7D12Nec
import Formal.Claude7D12Suff
import Formal.Claude7D12Ray

/-!
# D12: the closed classification and the rays

Written by a Claude worker (2026-10-22, D12 bridge session).

* `d12_classification` : for `r, s ≥ 1`, a literal path exists in `d12Graph r s` iff
  `r ∣ s - 1 ∨ r ∣ s + 1 ∨ |r - 3s| = 1` (in `ℤ`);
* `d12_rays` : along every ray `(r₀ + a n, s₀ + b n)`, `r₀, s₀ ≥ 1`, literal-path existence is
  eventually periodic (the condition is, `evper_cond`).
-/

namespace Claude7D12

open ClaudeChallenge Claude2Aligned

/-- **D12 classification.** -/
theorem d12_classification (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    (∃ n p, LiteralPath (d12Graph (r : ℤ) (s : ℤ)) n p) ↔
      ((r : ℤ) ∣ (s : ℤ) - 1 ∨ (r : ℤ) ∣ (s : ℤ) + 1 ∨ |(r : ℤ) - 3 * (s : ℤ)| = 1) := by
  constructor
  · intro h
    by_contra hc
    simp only [not_or] at hc
    obtain ⟨n1, n2, n3⟩ := hc
    have hr2 : 2 ≤ r := by
      by_contra h'
      have : r = 1 := by omega
      subst this; exact n1 (by simp)
    have hs2 : 2 ≤ s := by
      by_contra h'
      have : s = 1 := by omega
      subst this; exact n1 (by simp)
    exact d12_no_path r s hr2 hs2 n1 n2 n3 h
  · intro h
    rw [d12_iff_gm (by exact_mod_cast hr) (by exact_mod_cast hs)]
    exact path_gm r s hr hs h

/-- **D12 on rays.** -/
theorem d12_rays (r₀ s₀ a b : ℕ) (hr : 1 ≤ r₀) (hs : 1 ≤ s₀) :
    ∃ n₀ P : ℕ, 0 < P ∧ ∀ n : ℕ, n₀ ≤ n →
      ((∃ m p, LiteralPath (d12Graph ((r₀ + a * n : ℕ) : ℤ) ((s₀ + b * n : ℕ) : ℤ)) m p) ↔
        (∃ m p, LiteralPath (d12Graph ((r₀ + a * (n + P) : ℕ) : ℤ) ((s₀ + b * (n + P) : ℕ) : ℤ)) m p)) := by
  obtain ⟨n₀, T, hT, h⟩ := evper_cond r₀ s₀ a b hr
  refine ⟨n₀, T, hT, fun n hn => ?_⟩
  rw [d12_classification _ _ (by nlinarith) (by nlinarith), d12_classification _ _ (by nlinarith) (by nlinarith)]
  exact h n hn

end Claude7D12
