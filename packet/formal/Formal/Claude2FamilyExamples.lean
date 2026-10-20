import Formal.Claude2FamilyRays

/-!
# Second paper §6.3: the K3 and E10 rays, decided for every `t` from the closed conditions

* `k3_example`  : `K3Pos (43+2t) (170+5t) ↔ t = 40 ∨ t = 42`.
* `e10_example` : `E10Pos (200+5t) (17+2t) (23+t) ↔ t = 3 ∨ t = 10 ∨ t = 17 ∨ t = 34`.

Method (the determinant lemma of §6.1): a divisibility `M ∣ X` with `M, X` affine in `t` gives
`M ∣ u X + v M = c` for a nonzero constant `c`, hence `M ≤ |c|`, which bounds `t`; the finitely
many remaining `t` are evaluated by `norm_num`.  These are statements about the predicates,
i.e. they are the paper's examples *given* the family classifications (§5.1).
-/

namespace Claude2

theorem bound_of_dvd {M X : ℤ} (u v c : ℤ) (h : M ∣ X) (hc : u * X + v * M = c) (hc0 : c ≠ 0) :
    M ≤ |c| := by
  have h1 : M ∣ c := by rw [← hc]; exact dvd_add (dvd_mul_of_dvd_right h u) (dvd_mul_left M v)
  exact Int.le_of_dvd (abs_pos.2 hc0) ((dvd_abs M c).2 h1)

/-- §6.3: on the ray K3(43+2t, 170+5t) the closed condition holds exactly at `t = 40, 42`. -/
theorem k3_example (t : ℕ) : K3Pos (43 + 2 * t) (170 + 5 * t) ↔ t = 40 ∨ t = 42 := by
  rw [k3Pos_iff]
  unfold K3Z
  push_cast
  constructor
  · rintro (h | h)
    · have hb := bound_of_dvd 2 (-5) 123 h (by ring) (by norm_num)
      have ht : t ≤ 40 := by norm_num at hb; omega
      interval_cases t <;> (revert h; norm_num)
    · have hb := bound_of_dvd 2 (-5) 127 h (by ring) (by norm_num)
      have ht : t ≤ 42 := by norm_num at hb; omega
      interval_cases t <;> (revert h; norm_num)
  · rintro (rfl | rfl) <;> norm_num

/-- §6.3: on the ray E10(200+5t, 17+2t, 23+t) the closed condition holds exactly at
`t = 3, 10, 17, 34`. -/
theorem e10_example (t : ℕ) :
    E10Pos (200 + 5 * t) (17 + 2 * t) (23 + t) ↔ t = 3 ∨ t = 10 ∨ t = 17 ∨ t = 34 := by
  rw [e10Pos_iff]
  unfold E10Z
  push_cast
  constructor
  · rintro ((h | h) | (h | h) | (h | h))
    · have hb := bound_of_dvd 1 1 (-142) h (by ring) (by norm_num)
      have ht : t ≤ 17 := by norm_num at hb; omega
      interval_cases t <;> (revert h; norm_num)
    · have hb := bound_of_dvd 1 1 (-144) h (by ring) (by norm_num)
      have ht : t ≤ 17 := by norm_num at hb; omega
      interval_cases t <;> (revert h; norm_num)
    · have hb := bound_of_dvd 5 3 (-739) h (by ring) (by norm_num)
      have ht : t ≤ 136 := by norm_num at hb; omega
      interval_cases t <;> (revert h; norm_num)
    · have hb := bound_of_dvd 5 3 (-749) h (by ring) (by norm_num)
      have ht : t ≤ 138 := by norm_num at hb; omega
      interval_cases t <;> (revert h; norm_num)
    · have hb := bound_of_dvd 5 2 (-681) h (by ring) (by norm_num)
      have ht : t ≤ 124 := by norm_num at hb; omega
      interval_cases t <;> (revert h; norm_num)
    · have hb := bound_of_dvd 5 2 (-691) h (by ring) (by norm_num)
      have ht : t ≤ 126 := by norm_num at hb; omega
      interval_cases t <;> (revert h; norm_num)
  · rintro (rfl | rfl | rfl | rfl) <;> norm_num

end Claude2

#print axioms Claude2.k3_example
#print axioms Claude2.e10_example
