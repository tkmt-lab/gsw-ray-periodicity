import Formal.GCPrimitiveDegree

namespace R002.GCPrimitive
open Icosahedron (Corner)
variable {k l : ℤ}

theorem right_sector_positive_x (hk : 0<k) (hl : 0<l) (p : Lattice)
    (hb : b k l p<0) (hs : 0<a k l p+b k l p) : 0<p.1 := by
  have hT := norm_pos k l hk hl.le
  have h1 := mul_pos hk hs
  have h2 := mul_neg_of_pos_of_neg (add_pos hk hl) hb
  have hid : norm k l*p.1=k*(a k l p+b k l p)-(k+l)*b k l p := by
    dsimp [norm,a,b]; ring
  have hp : 0<norm k l*p.1 := by nlinarith
  by_contra hx
  have hn := mul_nonpos_of_nonneg_of_nonpos hT.le (show p.1≤0 by omega)
  omega

theorem left_sector_negative_x (hk : 0<k) (hl : 0<l) (p : Lattice)
    (ha : a k l p<0) (hs : 0<a k l p+b k l p) : p.1<0 := by
  have hT := norm_pos k l hk hl.le
  have h1 := mul_pos hl hs
  have h2 := mul_neg_of_pos_of_neg (add_pos hk hl) ha
  have hid : -(norm k l*p.1)=l*(a k l p+b k l p)-(k+l)*a k l p := by
    dsimp [norm,a,b]; ring
  have hp : norm k l*p.1<0 := by nlinarith
  by_contra hx
  have hn := mul_nonneg hT.le (show 0≤p.1 by omega)
  omega

theorem outside_02_no_unit (hk : 0<k) (hl : 0<l) (p q : Lattice)
    (hp : Interior k l (opposite k l (frame k l 0 p)))
    (hq : Interior k l (opposite k l (frame k l 2 q))) : ¬Unit p q := by
  have hp' := (opposite_interior k l p).mp (by simpa [frame] using hp)
  have hq' := (opposite_interior k l (GCPrimitive.turn k l q)).mp (by simpa [frame] using hq)
  rw [(turn_slices k l q).1,(turn_slices k l q).2.1] at hq'
  have hx := right_sector_positive_x hk hl p hp'.2.1 hp'.2.2
  have hy := left_sector_negative_x hk hl q hq'.2.1 (by dsimp [c] at hq'; omega)
  rintro ⟨i,rfl⟩
  fin_cases i <;> simp [direction] at hy <;> omega

/-- Distinct neighboring face interiors have a gap wider than one lattice edge. -/
theorem outside_distinct_no_unit (hk : 0<k) (hl : 0<l) (p q : Lattice) (e d : Corner)
    (hne : e≠d) (hp : Interior k l (opposite k l (frame k l e p)))
    (hq : Interior k l (opposite k l (frame k l d q))) : ¬Unit p q := by
  intro hu
  fin_cases e <;> fin_cases d
  · exact hne rfl
  · apply outside_02_no_unit hk hl (frame k l 1 q) (frame k l 1 p)
      (by simpa [frame] using hq) (by simpa [frame,turn_three] using hp)
    exact (frame_unit k l 1 _ _).mpr (unit_symm _ _ hu)
  · exact outside_02_no_unit hk hl p q hp hq hu
  · apply outside_02_no_unit hk hl (frame k l 1 p) (frame k l 1 q)
      (by simpa [frame] using hp) (by simpa [frame,turn_three] using hq)
    exact (frame_unit k l 1 _ _).mpr hu
  · exact hne rfl
  · apply outside_02_no_unit hk hl (frame k l 2 q) (frame k l 2 p)
      (by simpa [frame] using hq) (by simpa [frame] using hp)
    exact (frame_unit k l 2 _ _).mpr (unit_symm _ _ hu)
  · exact outside_02_no_unit hk hl q p hq hp (unit_symm _ _ hu)
  · apply outside_02_no_unit hk hl (frame k l 2 p) (frame k l 2 q)
      (by simpa [frame] using hp) (by simpa [frame] using hq)
    exact (frame_unit k l 2 _ _).mpr hu
  · exact hne rfl

end R002.GCPrimitive
