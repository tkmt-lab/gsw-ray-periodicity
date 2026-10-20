import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Arithmetic core of the R002 integer-GC obstruction.
This file contains no graph, surface, or path-validity theorem. -/

namespace R002

/-- Both coordinates are divisible by the integer scale. -/
def InScaledLattice (k : ℤ) (v : ℤ × ℤ) : Prop := k ∣ v.1 ∧ k ∣ v.2

/-- The forced triangular-strip recurrence gives two explicit arithmetic rows. -/
theorem strip_coordinates (p : ℕ → ℤ × ℤ)
    (h0 : p 0 = (0, 0)) (h1 : p 1 = (1, 0)) (h2 : p 2 = (0, 1))
    (hs : ∀ n, p (n + 3) = p (n + 1) + p (n + 2) - p n) (t : ℕ) :
    p (2 * t) = (0, (t : ℤ)) ∧
    p (2 * t + 1) = (1, (t : ℤ)) ∧
    p (2 * t + 2) = (0, (t : ℤ) + 1) := by
  induction t with
  | zero => simpa using And.intro h0 (And.intro h1 h2)
  | succ t ih =>
    obtain ⟨he, ho, hn⟩ := ih
    have h3 : p (2 * t + 3) = (1, (t : ℤ) + 1) := by
      rw [hs, ho, hn, he]
      ext <;> simp
    have h4 : p (2 * t + 4) = (0, (t : ℤ) + 2) := by
      have h := hs (2 * t + 1)
      have e1 : 2 * t + 1 + 1 = 2 * t + 2 := by omega
      have e2 : 2 * t + 1 + 2 = 2 * t + 3 := by omega
      have e3 : 2 * t + 1 + 3 = 2 * t + 4 := by omega
      rw [e1, e2, e3, hn, h3, ho] at h
      rw [h]
      ext <;> simp
      omega
    simpa [Nat.mul_succ, Nat.cast_add, Nat.cast_one, add_assoc] using
      And.intro hn (And.intro h3 h4)

/-- No integer scale at least two divides the first coordinate of the odd row. -/
theorem odd_row_not_scaled (k t : ℤ) (hk : 2 ≤ k) :
    ¬ InScaledLattice k (1, t) := by
  intro h
  have hd : k ∣ 1 := h.1
  obtain ⟨a, ha⟩ := hd
  have : a ≤ 0 ∨ 1 ≤ a := by omega
  rcases this with hneg | hpos
  · have : k * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) hneg
    omega
  · have : 2 ≤ k * a := by nlinarith
    omega

/-- The even row lies in the scaled lattice exactly at divisible heights. -/
theorem even_row_scaled_iff (k t : ℤ) :
    InScaledLattice k (0, t) ↔ k ∣ t := by
  simp [InScaledLattice]

/-- The odd-index exclusion for any sequence satisfying the recurrence. -/
theorem strip_odd_not_scaled (p : ℕ → ℤ × ℤ)
    (h0 : p 0 = (0, 0)) (h1 : p 1 = (1, 0)) (h2 : p 2 = (0, 1))
    (hs : ∀ n, p (n + 3) = p (n + 1) + p (n + 2) - p n)
    (k : ℤ) (hk : 2 ≤ k) (t : ℕ) :
    ¬ InScaledLattice k (p (2 * t + 1)) := by
  rw [(strip_coordinates p h0 h1 h2 hs t).2.1]
  exact odd_row_not_scaled k t hk

theorem strip_even_scaled_iff (p : ℕ → ℤ × ℤ)
    (h0 : p 0 = (0, 0)) (h1 : p 1 = (1, 0)) (h2 : p 2 = (0, 1))
    (hs : ∀ n, p (n + 3) = p (n + 1) + p (n + 2) - p n)
    (k : ℤ) (t : ℕ) :
    InScaledLattice k (p (2 * t)) ↔ k ∣ (t : ℤ) := by
  rw [(strip_coordinates p h0 h1 h2 hs t).1]
  exact even_row_scaled_iff k t

/-- A concrete sequence witnesses that the initial values and recurrence are consistent. -/
def explicitStrip (n : ℕ) : ℤ × ℤ := (n % 2, n / 2)

theorem explicitStrip_initial :
    explicitStrip 0 = (0, 0) ∧ explicitStrip 1 = (1, 0) ∧
    explicitStrip 2 = (0, 1) := by
  norm_num [explicitStrip]

theorem explicitStrip_recurrence (n : ℕ) :
    explicitStrip (n + 3) =
      explicitStrip (n + 1) + explicitStrip (n + 2) - explicitStrip n := by
  ext <;> simp [explicitStrip] <;> omega

/-- Two adjacent integral heights cannot both be multiples of a scale at least two. -/
theorem adjacent_heights_not_both_scaled (k h : ℤ) (hk : 2 ≤ k) :
    ¬ (k ∣ h ∧ k ∣ h + 1) := by
  intro hh
  have hd : k ∣ 1 := by
    simpa using dvd_sub hh.2 hh.1
  exact odd_row_not_scaled k 0 hk ⟨hd, dvd_zero k⟩

#print axioms strip_coordinates
#print axioms strip_odd_not_scaled
#print axioms strip_even_scaled_iff
#print axioms explicitStrip_recurrence
#print axioms adjacent_heights_not_both_scaled

end R002
