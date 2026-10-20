import Formal.GCNegMinusSeams
import Formal.GCNegReturn

namespace R002.GCNeg
open Icosahedron GCPrimitive GCSector

abbrev plusAtlas (P : TailParameters) (hp : Primitive (plusK P) P.l) : Atlas where
  k := plusK P
  l := P.l
  A := plusA P
  hkl := by linarith [(plus_bounds P).2.1]
  hl := (plus_bounds P).1
  hprim := hp
  hA := by linarith [(plus_bounds P).2.2.1]
  active := PlusActive P
  dart := plusDart P
  closedInterior := closed_interior_of_no_coarse _ _ _
    (by linarith [(plus_bounds P).1,(plus_bounds P).2.1]) (plus_bounds P).1 hp (plus_no_coarse P)
  activeOf := plus_active P hp
  compatible := plus_seams P
  dartTop := plus_top P
  dartLower := by rw [plus_lower]; rfl
  dartSecond := by
    simpa [psi_zero,bandDart,labelA] using plus_reg P 0 (-1) (by have := P.ha; omega) (by omega) (by omega) (by omega) false

abbrev minusAtlas (P : TailParameters) (ha2 : 2≤P.a) (hp : Primitive (minusK P) P.l) : Atlas where
  k := minusK P
  l := P.l
  A := minusA P
  hkl := by linarith [(minus_bounds P ha2).2.1]
  hl := (minus_bounds P ha2).1
  hprim := hp
  hA := by linarith [(minus_bounds P ha2).2.2.1]
  active := MinusActive P
  dart := minusDart P
  closedInterior := closed_interior_of_no_coarse _ _ _
    (by linarith [(minus_bounds P ha2).1,(minus_bounds P ha2).2.1]) (minus_bounds P ha2).1 hp (minus_no_coarse P ha2)
  activeOf := minus_active P ha2 hp
  compatible := minus_seams P ha2
  dartTop := minus_top P
  dartLower := by rw [minus_lower]; rfl
  dartSecond := by rw [minus_initial]; rfl

theorem psi_source_index (a : ℤ) : (-(↑(-a):ZMod 2)-1)=(a:ZMod 2)+1 := by
  push_cast
  have h2 : (2 : ZMod 2)=0 := by decide +kernel
  linear_combination -h2
theorem chi_source_index (a : ℤ) : (-(↑(1-a):ZMod 2)-1)=(a:ZMod 2) := by
  push_cast
  have h2 : (2 : ZMod 2)=0 := by decide +kernel
  linear_combination -h2
theorem base_plus0 : bandDart 0 true=(10,0) := by decide +kernel
theorem base_plus1 : bandDart 1 false=(6,0) := by decide +kernel
theorem base_minus : minusBase (-1) true=(11,0) := by decide +kernel

theorem psi_position (k l : ℤ) (n : ZMod 2) (f : Face) (e : Corner) (p q : Lattice)
    (h : unframe k l e p=q) :
    unframe k l (phasePsi n (f,e)).2 p=unframe k l (phasePsi n (f,0)).2 q :=
  rotated_position k l _ f e p q h
theorem chi_position (k l : ℤ) (n : ZMod 2) (f : Face) (e : Corner) (p q : Lattice)
    (h : unframe k l e p=q) :
    unframe k l (phaseChi n (f,e)).2 p=unframe k l (phaseChi n (f,0)).2 q :=
  rotated_position k l _ f e p q h

end R002.GCNeg
