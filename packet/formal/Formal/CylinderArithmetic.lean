import Formal.LatticeTransport

/-! Arithmetic core of AD §2. A primitive circumference direction u is supplied
with a Bezout witness; W = g*u. Geometry and the choice Q = 2*g*L are not asserted. -/
namespace R002

def cylScale (a : ℤ) (v : ℤ × ℤ) : ℤ × ℤ := (a * v.1, a * v.2)

def cylHeight (u v : ℤ × ℤ) : ℤ := -u.2 * v.1 + u.1 * v.2

theorem cylinder_displacement_height (u D v : ℤ × ℤ) :
    cylHeight u (cylScale (cylHeight u D) v - cylScale (cylHeight u v) D) = 0 := by
  simp [cylHeight, cylScale]
  ring

/-- Bezout primitivity gives the full integral kernel, including signed axes. -/
theorem cylinder_height_kernel (u z : ℤ × ℤ) (a b : ℤ)
    (hprim : a * u.1 + b * u.2 = 1) (hz : cylHeight u z = 0) :
    z = cylScale (a * z.1 + b * z.2) u := by
  have hdet : u.1 * z.2 = u.2 * z.1 := by
    dsimp [cylHeight] at hz
    linarith
  apply Prod.ext
  · dsimp [cylScale]
    calc
      z.1 = (a * u.1 + b * u.2) * z.1 := by rw [hprim]; ring
      _ = (a * z.1 + b * z.2) * u.1 := by
        nlinarith [congrArg (fun x : ℤ => b * x) hdet]
  · dsimp [cylScale]
    calc
      z.2 = (a * u.1 + b * u.2) * z.2 := by rw [hprim]; ring
      _ = (a * z.1 + b * z.2) * u.2 := by
        nlinarith [congrArg (fun x : ℤ => a * x) hdet]

theorem cylinder_scaled_kernel (u z : ℤ × ℤ) (a b g k : ℤ)
    (hprim : a * u.1 + b * u.2 = 1) (hz : cylHeight u z = 0)
    (hdiv : g ∣ k) :
    ∃ m : ℤ, cylScale k z = cylScale m (cylScale g u) := by
  obtain ⟨c, hc⟩ := hdiv
  refine ⟨c * (a * z.1 + b * z.2), ?_⟩
  have hk := cylinder_height_kernel u z a b hprim hz
  conv_lhs => rw [hk]
  rw [hc]
  ext <;> simp [cylScale] <;> ring

/-- The quotient is literal integer division; divisibility is an explicit premise. -/
theorem cylinder_portal_shift (u D v : ℤ × ℤ) (a b g Q : ℤ)
    (hprim : a * u.1 + b * u.2 = 1) (hdiv : g ∣ Q / cylHeight u v) :
    ∃ m : ℤ,
      cylScale (Q / cylHeight u v)
          (cylScale (cylHeight u D) v - cylScale (cylHeight u v) D) =
        cylScale m (cylScale g u) := by
  exact cylinder_scaled_kernel u _ a b g _ hprim
    (cylinder_displacement_height u D v) hdiv

#print axioms cylinder_displacement_height
#print axioms cylinder_height_kernel
#print axioms cylinder_scaled_kernel
#print axioms cylinder_portal_shift
end R002
