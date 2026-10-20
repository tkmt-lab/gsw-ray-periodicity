import Formal.Claude2FamilyRays

/-!
# Explicit periods for K3 and E10 on rays with a constant modulus

Complement to `Claude2FamilyRays` (§5.1/§6.1 of the second paper).  When the modulus grows the
condition is eventually constant (`k3_ray_const`, `e10_ray_const`).  When it is constant the
condition is periodic with the modulus as an explicit period, from the first `t` of the domain on:

* `k3_ray_period`  : `r = b` constant (`b ≥ 2`): period `b`.
* `e10_ray_period` : `m = 2r + s` constant (`2a₂ + a₃ = 0`): period `m = 2b₂ + b₃`.
-/

namespace Claude2

open ClaudeCor

theorem dvd_iff_of_sub {M X X' : ℤ} (k : ℤ) (h : X' - X = k * M) : M ∣ X' ↔ M ∣ X := by
  rw [show X' = X + M * k by linear_combination h]
  exact dvd_add_left (dvd_mul_right M k)

theorem k3Z_shift (R S k : ℤ) : K3Z R (S + k * R) ↔ K3Z R S :=
  or_congr (dvd_iff_of_sub k (by ring)) (dvd_iff_of_sub k (by ring))

theorem e10Z_shift (P R S a₁ a₂ a₃ : ℤ) (h : 2 * a₂ + a₃ = 0) :
    E10Z (P + a₁ * (2 * R + S)) (R + a₂ * (2 * R + S)) (S + a₃ * (2 * R + S)) ↔ E10Z P R S := by
  have hM : 2 * (R + a₂ * (2 * R + S)) + (S + a₃ * (2 * R + S)) = 2 * R + S := by
    linear_combination (2 * R + S) * h
  unfold E10Z
  rw [hM]
  exact or_congr (or_congr (dvd_iff_of_sub (-a₁) (by ring)) (dvd_iff_of_sub (-a₁) (by ring)))
    (or_congr (or_congr (dvd_iff_of_sub (a₂ - a₁) (by ring)) (dvd_iff_of_sub (a₂ - a₁) (by ring)))
      (or_congr (dvd_iff_of_sub (a₂ + a₃ - a₁) (by ring))
        (dvd_iff_of_sub (a₂ + a₃ - a₁) (by ring))))

/-- **K3, constant `r = b ≥ 2`**: along `s = c t + d`, from the first `T` with `s ≥ 2` on, the
condition is periodic with period `b`. -/
theorem k3_ray_period (b c d : ℤ) (hb : 2 ≤ b) (T : ℕ)
    (h : ∀ t : ℕ, T ≤ t → 2 ≤ c * t + d) :
    ∀ t : ℕ, T ≤ t → (K3Pos b.toNat (c * t + d).toNat ↔
      K3Pos b.toNat (c * (t + b.toNat : ℕ) + d).toNat) := by
  intro t ht
  have h1 := h t ht
  have h2 := h (t + b.toNat) (by omega)
  rw [k3Pos_toNat (by linarith) (by linarith), k3Pos_toNat (by linarith) (by linarith)]
  have e : c * ((t + b.toNat : ℕ) : ℤ) + d = (c * t + d) + c * b := by
    push_cast; rw [Int.toNat_of_nonneg (by linarith)]; ring
  rw [e, k3Z_shift]

/-- **E10, constant `m = 2r + s`** (`2a₂ + a₃ = 0`): from the first `T` of the domain on, the
condition is periodic with period `m = 2b₂ + b₃`. -/
theorem e10_ray_period (a₁ b₁ a₂ b₂ a₃ b₃ : ℤ) (hm : 2 * a₂ + a₃ = 0) (T : ℕ)
    (h : ∀ t : ℕ, T ≤ t → 1 ≤ a₁ * t + b₁ ∧ 2 ≤ a₂ * t + b₂ ∧ 1 ≤ a₃ * t + b₃) :
    ∀ t : ℕ, T ≤ t →
      (E10Pos (a₁ * t + b₁).toNat (a₂ * t + b₂).toNat (a₃ * t + b₃).toNat ↔
        E10Pos (a₁ * (t + (2 * b₂ + b₃).toNat : ℕ) + b₁).toNat
          (a₂ * (t + (2 * b₂ + b₃).toNat : ℕ) + b₂).toNat
          (a₃ * (t + (2 * b₂ + b₃).toNat : ℕ) + b₃).toNat) := by
  intro t ht
  obtain ⟨h1, h2, h3⟩ := h t ht
  have hM : 2 * (a₂ * t + b₂) + (a₃ * t + b₃) = 2 * b₂ + b₃ := by
    linear_combination (t : ℤ) * hm
  have hMpos : 0 ≤ 2 * b₂ + b₃ := by linarith
  obtain ⟨h1', h2', h3'⟩ := h (t + (2 * b₂ + b₃).toNat) (by omega)
  rw [e10Pos_toNat (by linarith) (by linarith) (by linarith),
    e10Pos_toNat (by linarith) (by linarith) (by linarith)]
  have c : (((t + (2 * b₂ + b₃).toNat : ℕ)) : ℤ) = t + (2 * (a₂ * t + b₂) + (a₃ * t + b₃)) := by
    push_cast; rw [Int.toNat_of_nonneg hMpos, hM]
  rw [c, show a₁ * ((t : ℤ) + (2 * (a₂ * t + b₂) + (a₃ * t + b₃))) + b₁ =
      (a₁ * t + b₁) + a₁ * (2 * (a₂ * t + b₂) + (a₃ * t + b₃)) by ring,
    show a₂ * ((t : ℤ) + (2 * (a₂ * t + b₂) + (a₃ * t + b₃))) + b₂ =
      (a₂ * t + b₂) + a₂ * (2 * (a₂ * t + b₂) + (a₃ * t + b₃)) by ring,
    show a₃ * ((t : ℤ) + (2 * (a₂ * t + b₂) + (a₃ * t + b₃))) + b₃ =
      (a₃ * t + b₃) + a₃ * (2 * (a₂ * t + b₂) + (a₃ * t + b₃)) by ring,
    e10Z_shift _ _ _ _ _ _ hm]

end Claude2

#print axioms Claude2.k3_ray_period
#print axioms Claude2.e10_ray_period
