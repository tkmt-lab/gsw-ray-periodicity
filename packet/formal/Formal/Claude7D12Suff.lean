import Formal.Claude7D12PR1
import Formal.Claude7D12PS1
import Formal.Claude7D12PAp
import Formal.Claude7D12PAm
import Formal.Claude7D12PQp
import Formal.Claude7D12PQm
import Formal.Claude7D12QT00L
import Formal.Claude7D12QT01L
import Formal.Claude7D12QT30L
import Formal.Claude7D12QT31L
import Formal.Claude7D12Iso

/-!
# D12 model: sufficiency — a literal path whenever the condition holds

Written by a Claude worker (2026-10-22, D12 bridge session).

For `r, s ≥ 1` with `r ∣ s - 1 ∨ r ∣ s + 1 ∨ |r - 3s| = 1` an explicit literal path:
`r = 1` (`pR1_lit`), `s = 1` (`pS1_lit`), `r = 3s + 1` (`pAp_lit`), `r = 3s - 1` (`pAm_lit`),
`s = r ± 1` (`pQp_lit`, `pQm_lit`), and the winding paths `s = q r ± 1`, `q ≥ 2`
(`q0_t0_lit`, `q0_t1_lit`, `q3_t0_lit`, `q3_t1_lit`).
-/

set_option linter.style.longLine false

namespace Claude7D12

open ClaudeChallenge Claude2Aligned

/-- A natural witness of an integer divisibility with a positive quotient. -/
theorem nat_quot {r s : ℕ} {c : ℤ} (hr : 1 ≤ r) (h : (r : ℤ) ∣ (s : ℤ) + c) (hpos : 0 < (s : ℤ) + c) :
    ∃ k : ℕ, 1 ≤ k ∧ (s : ℤ) + c = r * k := by
  obtain ⟨k, hk⟩ := h
  have hk0 : 0 < k := by
    by_contra hk0
    have : (r : ℤ) * k ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
    omega
  exact ⟨k.toNat, by omega, by rw [hk]; congr 1; omega⟩

/-- **Sufficiency in the model.** -/
theorem path_gm (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (h : (r : ℤ) ∣ (s : ℤ) - 1 ∨ (r : ℤ) ∣ (s : ℤ) + 1 ∨ |(r : ℤ) - 3 * (s : ℤ)| = 1) :
    ∃ n q, LiteralPath (GM (r : ℤ) (s : ℤ)) n q := by
  rcases Nat.eq_or_lt_of_le hr with h1 | h1
  · exact pR1_lit r s h1.symm hs
  rcases Nat.eq_or_lt_of_le hs with h2 | h2
  · exact pS1_lit r s hr h2.symm
  rcases h with h | h | h
  · obtain ⟨k, hk1, hk⟩ := nat_quot (c := -1) hr (by simpa [sub_eq_add_neg] using h) (by omega)
    have hk' : s = r * k + 1 := by have : (s : ℤ) = r * k + 1 := by linarith
                                   exact_mod_cast this
    rcases Nat.eq_or_lt_of_le hk1 with hk2 | hk2
    · subst hk2; exact pQp_lit r s (by omega) (by rw [hk']; ring)
    obtain ⟨Q, hQ | hQ⟩ := Nat.even_or_odd' k
    · obtain ⟨Qp, rfl⟩ : ∃ Qp, Q = Qp + 1 := ⟨Q - 1, by omega⟩
      exact q0_t0_lit r s Qp (by omega) (by rw [hk', hQ]; ring)
    · obtain ⟨Qp, rfl⟩ : ∃ Qp, Q = Qp + 1 := ⟨Q - 1, by omega⟩
      exact q0_t1_lit r s Qp (by omega) (by rw [hk', hQ]; ring)
  · obtain ⟨k, hk1, hk⟩ := nat_quot (c := 1) hr h (by omega)
    have hk' : s + 1 = r * k := by exact_mod_cast hk
    rcases Nat.eq_or_lt_of_le hk1 with hk2 | hk2
    · subst hk2; exact pQm_lit r s (by omega) (by rw [hk']; ring)
    obtain ⟨Q, hQ | hQ⟩ := Nat.even_or_odd' k
    · obtain ⟨Qp, rfl⟩ : ∃ Qp, Q = Qp + 1 := ⟨Q - 1, by omega⟩
      exact q3_t0_lit r s Qp (by omega) (by rw [hk', hQ]; ring)
    · obtain ⟨Qp, rfl⟩ : ∃ Qp, Q = Qp + 1 := ⟨Q - 1, by omega⟩
      exact q3_t1_lit r s Qp (by omega) (by rw [hk', hQ]; ring)
  · rcases abs_eq (by norm_num : (0 : ℤ) ≤ 1) |>.1 h with h | h
    · exact pAp_lit r s (by omega) (by omega)
    · exact pAm_lit r s (by omega) (by omega)

end Claude7D12
