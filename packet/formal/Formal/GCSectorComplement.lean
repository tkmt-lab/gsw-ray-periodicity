import Formal.GCSectorBlocks

/-! Coordinate and strict-interior certificates for R004 remaining sector §3.
The strip-to-surface map for this sector is deliberately still a separate obligation. -/
namespace R002.GCSector
open GCPrimitive

def compL (P : Parameters) : ℤ := P.k-P.l
def compA (P : Parameters) : ℤ := (P.q+4)*P.k+2*(P.q-1)*compL P
def compJ (P : Parameters) : ℤ := 2*(P.q-1)*P.k+(P.q-6)*compL P
def compG (P : Parameters) (p : Lattice) : Lattice := (compA P-p.2,p.1+p.2-compJ P)

theorem comp_positive (P : Parameters) : 0<compL P ∧ compL P<P.k := by
  have := params_positive P
  dsimp [compL]; omega

theorem comp_gap (P : Parameters) : compA P-compJ P=(9*P.q-4)*P.l+10*P.s := by
  dsimp [compA,compJ,compL,Parameters.k]; ring

theorem comp_indices_order (P : Parameters) : 1<compJ P ∧ compJ P<compA P := by
  have hl := l_ge_four P
  have hs := P.hs
  have hq := P.hq
  have hgap := comp_gap P
  have hp := mul_pos (show 0<9*P.q-4 by omega) (show 0<P.l by omega)
  have hid : compJ P=(3*(P.q-3)^2+9*(P.q-3)+6)*P.l+(3*(P.q-3)+1)*P.s := by
    dsimp [compJ,compL,Parameters.k]; ring
  rw [hid]
  have h1 := mul_nonneg (show 0≤3*(P.q-3)^2+9*(P.q-3) by nlinarith [sq_nonneg (P.q-3)]) (show 0≤P.l by omega)
  have h2 := mul_nonneg (show 0≤3*(P.q-3) by omega) (show 0≤P.s by omega)
  constructor <;> nlinarith

theorem comp_affine (P : Parameters) (p : Lattice) :
    compG P p=(-p.2,p.1+p.2)+A3.gc P.k (compL P) (P.q+4) (-2*(P.q-1)) := by
  ext <;> dsimp [compG,compA,compJ,A3.gc] <;> ring

theorem comp_delta (P : Parameters) (xi : ℤ) :
    (compJ P-1,xi)-A3.gc P.k (compL P) (2*P.q-5) (3-P.q)=
      (3*P.l-1,-2*P.l-P.s+xi) := by
  ext <;> dsimp [compJ,compL,Parameters.k,A3.gc] <;> ring

/-- Strict interior in the old F2 chart, for both source points. -/
theorem comp_source_interior (P : Parameters) (xi : ℤ) (hx0 : 0≤xi) (hx1 : xi≤1) :
    Interior P.k (compL P) (tileLocal P.k (compL P) ⟨P.q-3,2-P.q,true⟩ (compJ P-1,xi)) := by
  rcases P with ⟨q,h,s,hq,hs,hsh⟩
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ q=3+u := ⟨q-3,by omega,by omega⟩
  obtain ⟨v,hv,rfl⟩ : ∃ v : ℤ, 0≤v ∧ s=2+v := ⟨s-2,by omega,by omega⟩
  obtain ⟨w,hw,rfl⟩ : ∃ w : ℤ, 0≤w ∧ h=4+v+w := ⟨h-4-v,by omega,by omega⟩
  interval_cases xi <;>
    dsimp [Interior,tileLocal,tileBase,compL,compJ,Parameters.k,A3.gc,a,b,c,GCPrimitive.norm] <;>
    constructor
  all_goals first | (constructor <;> ring_nf <;> positivity) | (ring_nf; positivity)

theorem comp_face_return (P : Parameters) :
    compG P (A3.gc P.k (compL P) (2*P.q-5) (2-P.q))=A3.gc P.k (compL P) (2*P.q+2) (-P.q-1) ∧
    compG P (A3.gc P.k (compL P) (2*P.q-4) (2-P.q))=A3.gc P.k (compL P) (2*P.q+2) (-P.q) ∧
    compG P (A3.gc P.k (compL P) (2*P.q-5) (3-P.q))=A3.gc P.k (compL P) (2*P.q+1) (-P.q) := by
  constructor
  · ext <;> dsimp [compG,compA,compJ,A3.gc] <;> ring
  constructor <;> ext <;> dsimp [compG,compA,compJ,A3.gc] <;> ring

theorem comp_upper_collision (P : Parameters) : compG P (compJ P-1,1)=(compA P-1,0) := by
  ext <;> dsimp [compG] <;> ring
theorem comp_lower_collision (P : Parameters) : compG P (compJ P-1,0)=(compA P,-1) := by
  ext <;> dsimp [compG] <;> ring

end R002.GCSector
