import Formal.GCNegNearAtlas

namespace R002.GCNeg
open Icosahedron GCPrimitive GCSector

theorem plus_slices (P : TailParameters) (xi : ℤ) :
    a (plusK P) P.l (tileLocal (plusK P) P.l ⟨2*P.a-2,-P.a,true⟩ (plusJ P-1,xi))=
      norm (plusK P) P.l-a (plusK P) P.l (plusDelta P xi)-b (plusK P) P.l (plusDelta P xi) ∧
    b (plusK P) P.l (tileLocal (plusK P) P.l ⟨2*P.a-2,-P.a,true⟩ (plusJ P-1,xi))=a (plusK P) P.l (plusDelta P xi) ∧
    c (plusK P) P.l (tileLocal (plusK P) P.l ⟨2*P.a-2,-P.a,true⟩ (plusJ P-1,xi))=b (plusK P) P.l (plusDelta P xi) ∧
    a (plusK P) P.l (tileLocal (plusK P) P.l ⟨2*P.a-1,-P.a,false⟩ (plusJ P-1,xi))=norm (plusK P) P.l-b (plusK P) P.l (plusDelta P xi) ∧
    b (plusK P) P.l (tileLocal (plusK P) P.l ⟨2*P.a-1,-P.a,false⟩ (plusJ P-1,xi))=a (plusK P) P.l (plusDelta P xi)+b (plusK P) P.l (plusDelta P xi)-norm (plusK P) P.l ∧
    c (plusK P) P.l (tileLocal (plusK P) P.l ⟨2*P.a-1,-P.a,false⟩ (plusJ P-1,xi))=norm (plusK P) P.l-a (plusK P) P.l (plusDelta P xi) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp [a,b,c,GCPrimitive.norm,tileLocal,tileBase,plusDelta,A3.gc]; ring

/-- The closed diagonal is handled before primitive boundary exclusion; no branch is omitted. -/
theorem plus_source_tile (P : TailParameters) (hp : Primitive (plusK P) P.l)
    (xi : ℤ) (hx0 : 0≤xi) (hx1 : xi≤1) :
    Interior (plusK P) P.l (tileLocal (plusK P) P.l ⟨2*P.a-2,-P.a,true⟩ (plusJ P-1,xi)) ∨
    Interior (plusK P) P.l (tileLocal (plusK P) P.l ⟨2*P.a-1,-P.a,false⟩ (plusJ P-1,xi)) := by
  have hb := plus_bounds P
  have hc := plus_certificates P xi hx0 hx1
  have hs := plus_slices P xi
  have hr : Region (plusA P) (plusJ P-1,xi) := ⟨by linarith [hc.1],by linarith [hc.2.1],by omega,hx1⟩
  have hn : (plusJ P-1,xi)≠(0,0) := by intro he; have hh := congrArg (fun p : Lattice => p.1) he; dsimp at hh; linarith [hc.1]
  have hi := closed_interior_of_no_coarse (plusK P) P.l (plusA P)
    (by linarith [hb.1,hb.2.1]) hb.1 hp (plus_no_coarse P) (plusJ P-1,xi) hr hn
  by_cases hsum : a (plusK P) P.l (plusDelta P xi)+b (plusK P) P.l (plusDelta P xi)≤norm (plusK P) P.l
  · left; apply hi; change 0≤_ ∧ 0≤_ ∧ 0≤_
    rw [hs.1,hs.2.1,hs.2.2.1]
    exact ⟨by omega,hc.2.2.1.le,hc.2.2.2.2.1.le⟩
  · right; apply hi; change 0≤_ ∧ 0≤_ ∧ 0≤_
    rw [hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2]
    exact ⟨by linarith [hc.2.2.2.2.2],by omega,by linarith [hc.2.2.2.1]⟩

theorem plus_source_dart0 (P : TailParameters) :
    plusDart P ⟨2*P.a-2,-P.a,true⟩=phasePsi (P.a+1) (10,0) := by
  have ha := P.ha
  rw [plus_reg P (2*P.a-2) (-P.a) (by omega) (by omega) (by omega) (by omega)]
  have he : 2*P.a-2+2*(-P.a)+2=0 := by ring
  rw [he,psi_source_index]
  simpa using congrArg (phasePsi ((P.a:ZMod 2)+1)) base_plus0
theorem plus_source_dart1 (P : TailParameters) :
    plusDart P ⟨2*P.a-1,-P.a,false⟩=phasePsi (P.a+1) (6,0) := by
  have ha := P.ha
  rw [plus_reg P (2*P.a-1) (-P.a) (by omega) (by omega) (by omega) (by omega)]
  have he : 2*P.a-1+2*(-P.a)+2=1 := by ring
  rw [he,psi_source_index]
  simpa using congrArg (phasePsi ((P.a:ZMod 2)+1)) base_plus1
theorem minus_source_dart (P : TailParameters) (ha2 : 2≤P.a) :
    minusDart P ⟨2*P.a-3,1-P.a,true⟩=phaseChi P.a (11,0) := by
  rw [minus_upper P (2*P.a-3) (1-P.a) (by omega) (by omega) (by omega),chi_source_index,base_minus]

theorem plus_local0 (P : TailParameters) (p : Lattice) :
    tileLocal (plusK P) P.l ⟨2*P.a+3,-P.a-2,false⟩ (plusG P p)=
      tileLocal (plusK P) P.l ⟨2*P.a-2,-P.a,true⟩ p := by
  ext <;> dsimp [tileLocal,tileBase,plusG,plusA,plusJ,A3.gc] <;> ring
theorem plus_local1 (P : TailParameters) (p : Lattice) :
    unframe (plusK P) P.l 2 (tileLocal (plusK P) P.l ⟨2*P.a+3,-P.a-1,true⟩ (plusG P p))=
      tileLocal (plusK P) P.l ⟨2*P.a-1,-P.a,false⟩ p := by
  ext <;> dsimp [tileLocal,tileBase,plusG,plusA,plusJ,A3.gc,unframe,GCPrimitive.turn] <;> ring
theorem minus_local (P : TailParameters) (p : Lattice) :
    unframe (minusK P) P.l 1 (tileLocal (minusK P) P.l ⟨2*P.a+1,-P.a-2,false⟩ (minusH P p))=
      tileLocal (minusK P) P.l ⟨2*P.a-3,1-P.a,true⟩ p := by
  ext <;> dsimp [tileLocal,tileBase,minusH,minusA,minusJ,A3.gc,unframe,GCPrimitive.turn] <;> ring

end R002.GCNeg
