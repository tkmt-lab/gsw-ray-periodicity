import Formal.GCNegNearLabels

namespace R002.GCNeg
open Icosahedron GCSector

theorem plus_top (P : TailParameters) : plusDart P ⟨0,0,true⟩=(0,0) := by simp [plusDart]
theorem plus_lower (P : TailParameters) (s : Bool) : plusDart P ⟨-1,-1,s⟩=bandDart (-1) s := by simp [plusDart]
theorem plus_reg (P : TailParameters) (i j : ℤ) (hj0 : -P.a-1≤j) (hj1 : j≤ -1)
    (hm0 : -2 ≤ i+2*j) (hm1 : i+2*j≤0) (s : Bool) :
    plusDart P ⟨i,j,s⟩=phasePsi (-j-1) (bandDart ((i+2*j+2:ℤ):ZMod 5) s) := by
  have ha := P.ha
  simp [plusDart,show j≠0 by omega,show i≠ -1 by omega,show i≠2*P.a+3 by omega]
theorem plus_cap0 (P : TailParameters) (s : Bool) :
    plusDart P ⟨2*P.a+3,-P.a-1,s⟩=phasePsi (P.a+1) (gDart false s) := by
  have ha := P.ha
  simp [plusDart,show -P.a-1≠0 by omega,show 2*P.a+3≠ -1 by omega]
theorem plus_cap1 (P : TailParameters) (s : Bool) :
    plusDart P ⟨2*P.a+3,-P.a-2,s⟩=phasePsi (P.a+1) (gDart true s) := by
  have ha := P.ha
  simp [plusDart,show -P.a-2≠0 by omega,show 2*P.a+3≠ -1 by omega]

theorem minus_top (P : TailParameters) : minusDart P ⟨0,0,true⟩=(0,0) := by simp [minusDart]
theorem minus_lower (P : TailParameters) (s : Bool) : minusDart P ⟨-1,-1,s⟩=bandDart (-1) s := by simp [minusDart]
theorem minus_initial (P : TailParameters) (s : Bool) : minusDart P ⟨0,-1,s⟩=bandDart 0 s := by simp [minusDart]
theorem minus_upper (P : TailParameters) (i j : ℤ) (hj0 : -P.a≤j) (hj1 : j≤ -1)
    (hm : i+2*j= -1) (s : Bool) :
    minusDart P ⟨i,j,s⟩=phaseChi (-j-1) (minusBase (-1) s) := by
  simp [minusDart,show j≠0 by omega,show i≠ -1 by omega,show i≠0 by omega,
    show j≠ -P.a-2 by omega,hm,Int.cast_sub]
theorem minus_bottom (P : TailParameters) (i j m : ℤ) (hj0 : -P.a-1≤j) (hj1 : j≤ -2)
    (hm : i+2*j=m) (hm' : m= -3 ∨ m= -2) (s : Bool) :
    minusDart P ⟨i,j,s⟩=phaseChi (-j-2) (minusBase m s) := by
  have hmn : m≠ -1 := by omega
  simp [minusDart,show j≠0 by omega,show i≠ -1 by omega,show i≠0 by omega,
    show j≠ -P.a-2 by omega,hm,hmn,Int.cast_sub]
theorem minus_cap0 (P : TailParameters) (ha2 : 2≤P.a) (s : Bool) :
    minusDart P ⟨2*P.a,-P.a-2,s⟩=phaseChi P.a (hDart false s) := by
  simp [minusDart,show -P.a-2≠0 by omega,show 2*P.a≠ -1 by omega,show 2*P.a≠0 by omega]
theorem minus_cap1 (P : TailParameters) (ha2 : 2≤P.a) (s : Bool) :
    minusDart P ⟨2*P.a+1,-P.a-2,s⟩=phaseChi P.a (hDart true s) := by
  simp [minusDart,show -P.a-2≠0 by omega,show 2*P.a+1≠ -1 by omega,show 2*P.a+1≠0 by omega]

end R002.GCNeg
