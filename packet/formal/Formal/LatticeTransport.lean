import Formal.GCArithmetic

/-! Integer-coordinate transport used in the R002 GC argument.
The identification of these maps with surface chart changes is not formalized. -/

namespace R002

/-- Counterclockwise 60-degree rotation in a positively oriented 60-degree basis. -/
def rotate60 (v : ℤ × ℤ) : ℤ × ℤ := (-v.2, v.1 + v.2)

/-- Rotation about an integral center. -/
def rotateAbout (c v : ℤ × ℤ) : ℤ × ℤ := c + rotate60 (v - c)

theorem scaled_add {k : ℤ} {v w : ℤ × ℤ}
    (hv : InScaledLattice k v) (hw : InScaledLattice k w) :
    InScaledLattice k (v + w) :=
  ⟨dvd_add hv.1 hw.1, dvd_add hv.2 hw.2⟩

theorem scaled_sub {k : ℤ} {v w : ℤ × ℤ}
    (hv : InScaledLattice k v) (hw : InScaledLattice k w) :
    InScaledLattice k (v - w) :=
  ⟨dvd_sub hv.1 hw.1, dvd_sub hv.2 hw.2⟩

theorem rotate60_scaled_iff (k : ℤ) (v : ℤ × ℤ) :
    InScaledLattice k (rotate60 v) ↔ InScaledLattice k v := by
  constructor
  · intro h
    have hy : k ∣ v.2 := by simpa [rotate60] using h.1
    have hx : k ∣ v.1 := by
      have := dvd_sub h.2 hy
      simpa [rotate60] using this
    exact ⟨hx, hy⟩
  · intro h
    exact ⟨by simpa [rotate60] using h.2, dvd_add h.1 h.2⟩

/-- Both membership and nonmembership are preserved, not just one implication. -/
theorem rotateAbout_scaled_iff (k : ℤ) (c v : ℤ × ℤ)
    (hc : InScaledLattice k c) :
    InScaledLattice k (rotateAbout c v) ↔ InScaledLattice k v := by
  constructor
  · intro h
    have hr : InScaledLattice k (rotate60 (v - c)) := by
      simpa [rotateAbout] using scaled_sub h hc
    have hv := (rotate60_scaled_iff k (v - c)).mp hr
    simpa using scaled_add hv hc
  · intro h
    exact scaled_add hc ((rotate60_scaled_iff k (v - c)).mpr (scaled_sub h hc))

/-- Apply a finite list of rotations, in list order. Repeated centers are allowed. -/
def transportCenters : List (ℤ × ℤ) → (ℤ × ℤ) → (ℤ × ℤ)
  | [], v => v
  | c :: cs, v => transportCenters cs (rotateAbout c v)

theorem transportCenters_scaled_iff (k : ℤ) (cs : List (ℤ × ℤ))
    (hc : ∀ c ∈ cs, InScaledLattice k c) (v : ℤ × ℤ) :
    InScaledLattice k (transportCenters cs v) ↔ InScaledLattice k v := by
  induction cs generalizing v with
  | nil => rfl
  | cons c cs ih =>
    have hhead : InScaledLattice k c := hc c (by simp)
    have htail : ∀ d ∈ cs, InScaledLattice k d := by
      intro d hd
      exact hc d (by simp [hd])
    exact (ih htail (rotateAbout c v)).trans (rotateAbout_scaled_iff k c v hhead)

/-- Affine transport commutes with the forced next-point expression. -/
theorem rotateAbout_next (c a b d : ℤ × ℤ) :
    rotateAbout c (b + d - a) =
      rotateAbout c b + rotateAbout c d - rotateAbout c a := by
  ext <;> simp [rotateAbout, rotate60] <;> ring

/-- The triangular-lattice squared norm is unchanged by the coordinate rotation. -/
theorem rotate60_norm (v : ℤ × ℤ) :
    (rotate60 v).1 ^ 2 + (rotate60 v).1 * (rotate60 v).2 + (rotate60 v).2 ^ 2 =
      v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2 := by
  simp [rotate60]
  ring

/-- Each odd row point may undergo its own finite transport. -/
theorem transported_strip_odd_not_scaled (p : ℕ → ℤ × ℤ)
    (h0 : p 0 = (0, 0)) (h1 : p 1 = (1, 0)) (h2 : p 2 = (0, 1))
    (hs : ∀ n, p (n + 3) = p (n + 1) + p (n + 2) - p n)
    (k : ℤ) (hk : 2 ≤ k) (t : ℕ) (cs : List (ℤ × ℤ))
    (hc : ∀ c ∈ cs, InScaledLattice k c) :
    ¬ InScaledLattice k (transportCenters cs (p (2 * t + 1))) := by
  intro h
  exact strip_odd_not_scaled p h0 h1 h2 hs k hk t
    ((transportCenters_scaled_iff k cs hc (p (2 * t + 1))).mp h)

#print axioms rotate60_scaled_iff
#print axioms rotateAbout_scaled_iff
#print axioms transportCenters_scaled_iff
#print axioms rotateAbout_next
#print axioms rotate60_norm
#print axioms transported_strip_odd_not_scaled

end R002
