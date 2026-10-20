import Formal.GCNegCoarse

namespace R002.GCNeg
open GCPrimitive GCSector

theorem plus_bounds (P : TailParameters) :
    0<P.l ∧ 0<plusK P-P.l ∧ 0<plusA P-1 ∧ 0<3*plusK P+P.l ∧
    0<norm (plusK P) P.l-(3*plusK P+P.l) ∧
    0<2*norm (plusK P) P.l-P.r*plusA P-(3*plusK P+P.l) ∧
    0<(2*P.a+4)*norm (plusK P) P.l-plusK P*plusA P-(plusK P+P.l) := by
  rcases P with ⟨a,r,t,ha,ht,htr⟩
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ a=1+u := ⟨a-1,by omega,by omega⟩
  obtain ⟨v,hv,rfl⟩ : ∃ v : ℤ, 0≤v ∧ t=2+v := ⟨t-2,by omega,by omega⟩
  obtain ⟨w,hw,rfl⟩ : ∃ w : ℤ, 0≤w ∧ r=4+v+w := ⟨r-4-v,by omega,by omega⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp [plusK,plusA,TailParameters.l,GCPrimitive.norm]; ring_nf; positivity

theorem minus_bounds (P : TailParameters) (ha2 : 2≤P.a) :
    0<P.l ∧ 0<minusK P-P.l ∧ 0<minusA P-1 ∧ 0<3*minusK P+P.l ∧
    0<norm (minusK P) P.l-(3*minusK P+P.l) ∧
    0<2*norm (minusK P) P.l-P.r*minusA P-(3*minusK P+P.l) ∧
    0<(2*P.a+2)*norm (minusK P) P.l-minusK P*minusA P-(minusK P+P.l) := by
  rcases P with ⟨a,r,t,ha,ht,htr⟩
  dsimp at ha2
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ a=2+u := ⟨a-2,by omega,by omega⟩
  obtain ⟨v,hv,rfl⟩ : ∃ v : ℤ, 0≤v ∧ t=2+v := ⟨t-2,by omega,by omega⟩
  obtain ⟨w,hw,rfl⟩ : ∃ w : ℤ, 0≤w ∧ r=4+v+w := ⟨r-4-v,by omega,by omega⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp [minusK,minusA,TailParameters.l,GCPrimitive.norm]; ring_nf; positivity

theorem plus_no_coarse (P : TailParameters) (u v : ℤ)
    (hp : Region (plusA P) (A3.gc (plusK P) P.l u v)) : A3.gc (plusK P) P.l u v=(0,0) := by
  have h := plus_bounds P
  have hr : 4≤P.r := by have := P.ht; have := P.htr; omega
  apply rectangle_zero P.r P.t (3*plusK P+P.l) (norm (plusK P) P.l) (plusA P)
    hr P.ht P.htr h.2.2.2.1.le (by linarith [h.2.2.2.2.1]) (by linarith [h.2.2.2.2.2.1])
    _ hp (u+3*v) (P.a*(u+3*v)+v)
  · dsimp [A3.gc,plusK,TailParameters.l,GCPrimitive.norm]; ring
  · dsimp [A3.gc,plusK,TailParameters.l]; ring

theorem minus_no_coarse (P : TailParameters) (ha2 : 2≤P.a) (u v : ℤ)
    (hp : Region (minusA P) (A3.gc (minusK P) P.l u v)) : A3.gc (minusK P) P.l u v=(0,0) := by
  have h := minus_bounds P ha2
  have hr : 4≤P.r := by have := P.ht; have := P.htr; omega
  let p := A3.gc (minusK P) P.l u v
  change Region (minusA P) p at hp
  have hh : (p.1,-p.2)=(0,0) := by
    apply rectangle_zero P.r P.t (3*minusK P+P.l) (norm (minusK P) P.l) (minusA P)
      hr P.ht P.htr h.2.2.2.1.le (by linarith [h.2.2.2.2.1]) (by linarith [h.2.2.2.2.2.1])
      (p.1,-p.2) ⟨hp.1,hp.2.1,by have := hp.2.2.2; change -1≤ -p.2; omega,by have := hp.2.2.1; change -p.2≤1; omega⟩ (-u-3*v) (P.a*(-u-3*v)+v)
    · dsimp [p,A3.gc,minusK,TailParameters.l,GCPrimitive.norm]; ring
    · dsimp [p,A3.gc,minusK,TailParameters.l]; ring
  apply Prod.ext
  · have hx := congrArg (fun z : Lattice => z.1) hh; exact hx
  · have hy := congrArg (fun z : Lattice => z.2) hh
    change -p.2=0 at hy
    change p.2=0
    omega

end R002.GCNeg
