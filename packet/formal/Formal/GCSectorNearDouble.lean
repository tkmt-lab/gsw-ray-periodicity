import Formal.GCSectorComplement

/-! General arithmetic certificates for the two sectors next to k=2l.
They supply source-point interiors and return coordinates, not whole-strip coverage. -/
namespace R002.GCSector
open GCPrimitive

structure TailParameters where
  a : ℤ
  r : ℤ
  t : ℤ
  ha : 1≤a
  ht : 2≤t
  htr : t≤r-2
def TailParameters.l (P : TailParameters) : ℤ := P.a*P.r+P.t
def plusK (P : TailParameters) : ℤ := 2*P.l+P.r
def plusA (P : TailParameters) : ℤ := (2*P.a+5)*plusK P+3*P.a*P.l
def plusJ (P : TailParameters) : ℤ := 3*P.a*plusK P+(P.a-5)*P.l
def plusG (P : TailParameters) (p : Lattice) : Lattice := (plusA P-p.2,p.1+p.2-plusJ P)
def plusDelta (P : TailParameters) (xi : ℤ) : Lattice :=
  (plusJ P-1,xi)-A3.gc (plusK P) P.l (3*P.a-2) (-P.a)

theorem plus_delta (P : TailParameters) (xi : ℤ) :
    plusDelta P xi=(2*P.r-P.l-1,3*P.l-P.t+xi) := by
  ext <;> dsimp [plusDelta,plusJ,plusK,TailParameters.l,A3.gc] <;> ring

theorem plus_certificates (P : TailParameters) (xi : ℤ) (hx0 : 0≤xi) (hx1 : xi≤1) :
    0<plusJ P-1 ∧ 0<plusA P-plusJ P ∧
    0<a (plusK P) P.l (plusDelta P xi) ∧ a (plusK P) P.l (plusDelta P xi)<norm (plusK P) P.l ∧
    0<b (plusK P) P.l (plusDelta P xi) ∧ b (plusK P) P.l (plusDelta P xi)<norm (plusK P) P.l := by
  rcases P with ⟨a,r,t,ha,ht,htr⟩
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ a=1+u := ⟨a-1,by omega,by omega⟩
  obtain ⟨v,hv,rfl⟩ : ∃ v : ℤ, 0≤v ∧ t=2+v := ⟨t-2,by omega,by omega⟩
  obtain ⟨w,hw,rfl⟩ : ∃ w : ℤ, 0≤w ∧ r=4+v+w := ⟨r-4-v,by omega,by omega⟩
  interval_cases xi <;> refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals try (apply sub_pos.mp)
  all_goals dsimp [plusJ,plusA,plusK,plusDelta,TailParameters.l,A3.gc,GCPrimitive.a,b,GCPrimitive.norm]
  all_goals ring_nf; positivity

theorem plus_affine (P : TailParameters) (p : Lattice) :
    plusG P p=(-p.2,p.1+p.2)+A3.gc (plusK P) P.l (2*P.a+5) (-3*P.a) := by
  ext <;> dsimp [plusG,plusA,plusJ,A3.gc] <;> ring
theorem plus_upper_collision (P : TailParameters) : plusG P (plusJ P-1,1)=(plusA P-1,0) := by
  ext <;> dsimp [plusG] <;> ring
theorem plus_lower_collision (P : TailParameters) : plusG P (plusJ P-1,0)=(plusA P,-1) := by
  ext <;> dsimp [plusG] <;> ring

def minusK (P : TailParameters) : ℤ := 2*P.l-P.r
def minusA (P : TailParameters) : ℤ := 3*P.a*minusK P+(P.a+5)*P.l
def minusJ (P : TailParameters) : ℤ := (2*P.a-5)*minusK P+3*P.a*P.l
def minusH (P : TailParameters) (p : Lattice) : Lattice :=
  (p.1+p.2+minusA P-minusJ P,-p.1+minusJ P)

theorem minus_delta (P : TailParameters) (eta : ℤ) :
    (minusJ P-1+eta,-eta)-A3.gc (minusK P) P.l (3*P.a-4) (2-P.a)=
      ((P.a+1)*P.r-1+eta,-2*P.l-(P.a-2)*P.r-eta) := by
  ext <;> dsimp [minusJ,minusK,TailParameters.l,A3.gc] <;> ring

theorem minus_certificates (P : TailParameters) (ha2 : 2≤P.a) (eta : ℤ) (he0 : 0≤eta) (he1 : eta≤1) :
    0<minusJ P-1 ∧ 0<minusA P-minusJ P ∧
    Interior (minusK P) P.l (tileLocal (minusK P) P.l ⟨2*P.a-3,1-P.a,true⟩ (minusJ P-1+eta,-eta)) := by
  rcases P with ⟨a,r,t,ha,ht,htr⟩
  dsimp at ha2
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ a=2+u := ⟨a-2,by omega,by omega⟩
  obtain ⟨v,hv,rfl⟩ : ∃ v : ℤ, 0≤v ∧ t=2+v := ⟨t-2,by omega,by omega⟩
  obtain ⟨w,hw,rfl⟩ : ∃ w : ℤ, 0≤w ∧ r=4+v+w := ⟨r-4-v,by omega,by omega⟩
  interval_cases eta <;> refine ⟨?_,?_,?_,?_,?_⟩
  all_goals dsimp [minusJ,minusA,minusK,TailParameters.l,tileLocal,tileBase,A3.gc,GCPrimitive.a,b,c,GCPrimitive.norm]
  all_goals ring_nf; positivity

theorem minus_affine (P : TailParameters) (p : Lattice) :
    minusH P p=A3.invRotate p+A3.gc (minusK P) P.l (P.a+5) (2*P.a-5) := by
  ext <;> dsimp [minusH,minusA,minusJ,A3.invRotate,A3.gc] <;> ring
theorem minus_upper_collision (P : TailParameters) : minusH P (minusJ P-1,0)=(minusA P-1,1) := by
  ext <;> dsimp [minusH] <;> ring
theorem minus_lower_collision (P : TailParameters) : minusH P (minusJ P,-1)=(minusA P-1,0) := by
  ext <;> dsimp [minusH] <;> ring

end R002.GCSector
