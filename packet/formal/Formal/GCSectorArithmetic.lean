import Formal.GCTwoStartOrbits
import Formal.A3Arithmetic

/-! First-sector coordinate arithmetic, without assuming a strip-to-surface map. -/
namespace R002.GCSector
open GCPrimitive

structure Parameters where
  q : ℤ
  l : ℤ
  s : ℤ
  hq : 3 ≤ q
  hs : 2 ≤ s
  hsl : s ≤ l-2

def Parameters.k (P : Parameters) : ℤ := P.q*P.l+P.s
def Parameters.J (P : Parameters) : ℤ := (P.q-4)*P.k+(P.q+2)*P.l
def Parameters.K (P : Parameters) : ℤ := (P.q+2)*P.k+6*P.l

theorem l_ge_four (P : Parameters) : 4 ≤ P.l := by have := P.hs; have := P.hsl; omega

theorem k_ge (P : Parameters) : 3*P.l+2 ≤ P.k := by
  have h := mul_nonneg (show 0 ≤ P.q-3 by have := P.hq; omega)
    (show 0 ≤ P.l by have := l_ge_four P; omega)
  dsimp [Parameters.k]
  have := P.hs
  nlinarith

theorem params_positive (P : Parameters) : 0<P.l ∧ P.l<P.k := by
  have := l_ge_four P; have := k_ge P; omega

theorem J_rewrite (P : Parameters) : P.J=(P.q-3)*P.k+2*P.l-P.s := by
  dsimp [Parameters.J,Parameters.k]
  ring

theorem J_ge (P : Parameters) : P.l+2 ≤ P.J := by
  rw [J_rewrite]
  have h := mul_nonneg (show 0 ≤ P.q-3 by have := P.hq; omega)
    (show 0 ≤ P.k by have := k_ge P; have := l_ge_four P; omega)
  have := P.hsl
  nlinarith

theorem K_sub_J (P : Parameters) : P.K-P.J=5*P.k+4*P.l+P.s := by
  dsimp [Parameters.K,Parameters.J,Parameters.k]
  ring

theorem indices_order (P : Parameters) : 2<P.J ∧ P.J<P.K := by
  have := J_ge P; have := l_ge_four P; have := k_ge P; have := P.hs
  have := K_sub_J P
  omega

def H (P : Parameters) (p : Lattice) : Lattice :=
  (p.1+p.2+P.K-P.J,-p.1+P.J)
def Hinv (P : Parameters) (p : Lattice) : Lattice :=
  (P.J-p.2,p.1-P.K+p.2)

theorem H_inverse (P : Parameters) (p : Lattice) :
    H P (Hinv P p)=p ∧ Hinv P (H P p)=p := by
  constructor <;> ext <;> dsimp [H,Hinv] <;> ring

theorem H_affine (P : Parameters) (p : Lattice) :
    H P p=A3.invRotate p+A3.gc P.k P.l 6 (P.q-4) := by
  ext <;> dsimp [H,Parameters.K,Parameters.J,A3.invRotate,A3.gc] <;> ring

theorem upper_collision (P : Parameters) : H P (P.J-1,0)=(P.K-1,1) := by
  ext <;> dsimp [H] <;> ring

theorem lower_collision (P : Parameters) : H P (P.J,-1)=(P.K-1,0) := by
  ext <;> dsimp [H] <;> ring

/-- Both rectangle inequalities are strict, including the boundary case q=3. -/
theorem rectangle_upper_gap (P : Parameters) : 0<P.l*(P.J-1)-P.k := by
  have hl := l_ge_four P
  have hk := k_ge P
  have hs := P.hs
  have hsl := P.hsl
  by_cases hq : P.q=3
  · have hid : P.l*(P.J-1)-P.k=
        (P.l-1)*(P.l-2)+(P.l+1)*(P.l-P.s-2) := by
      dsimp [Parameters.J,Parameters.k]; rw [hq]; ring
    rw [hid]
    have h1 := mul_pos (show 0<P.l-1 by omega) (show 0<P.l-2 by omega)
    have h2 := mul_nonneg (show 0≤P.l+1 by omega) (show 0≤P.l-P.s-2 by omega)
    omega
  · have hq4 : 4≤P.q := by have := P.hq; omega
    have hp := mul_nonneg (show 0≤P.q-4 by omega) (show 0≤P.k by omega)
    have hj : P.k+P.l+2≤P.J := by rw [J_rewrite]; nlinarith
    have hh := mul_le_mul_of_nonneg_left hj (show 0≤P.l by omega)
    nlinarith [mul_nonneg (show 0≤P.l-1 by omega) (show 0≤P.k by omega)]

theorem rectangle_lower_identity (P : Parameters) :
    norm P.k P.l-P.l*(P.J+1)-2*P.k=
      (P.s+4*P.l-2)*P.k+P.s*P.l-P.l^2-P.l := by
  dsimp [GCPrimitive.norm,Parameters.J,Parameters.k]
  ring

theorem rectangle_lower_gap (P : Parameters) :
    0<norm P.k P.l-P.l*(P.J+1)-2*P.k := by
  rw [rectangle_lower_identity]
  have hl := l_ge_four P
  have hk := k_ge P
  have hs := P.hs
  have h1 := mul_nonneg (show 0≤P.s+3*P.l-2 by omega) (show 0≤P.k by omega)
  have h2 := mul_pos (show 0<P.l by omega) (show 0<P.k-P.l-1 by omega)
  have h3 := mul_nonneg (show 0≤P.s by omega) (show 0≤P.l by omega)
  nlinarith

def Belt (P : Parameters) (p : Lattice) : Prop :=
  -norm P.k P.l < b P.k P.l p ∧ b P.k P.l p < 0

theorem rectangle_in_belt (P : Parameters) (x y : ℤ)
    (hx0 : P.J-1≤x) (hx1 : x≤P.J+1) (hy0 : -2≤y) (hy1 : y≤1) :
    Belt P (x,y) := by
  have hk := (params_positive P).2.trans' (params_positive P).1
  have hl := (params_positive P).1
  have h1 := mul_le_mul_of_nonneg_left hx0 hl.le
  have h2 := mul_le_mul_of_nonneg_left hx1 hl.le
  have h3 := mul_le_mul_of_nonneg_left hy0 hk.le
  have h4 := mul_le_mul_of_nonneg_left hy1 hk.le
  have hu := rectangle_upper_gap P
  have hd := rectangle_lower_gap P
  dsimp [Belt,b]
  constructor <;> nlinarith

theorem return_section (P : Parameters) (y : ℤ) (hy0 : -1≤y) (hy1 : y≤1) :
    Belt P (Hinv P (P.K-1,y)) := by
  dsimp [Hinv]
  apply rectangle_in_belt P <;> omega

theorem earlier_points_in_belt (P : Parameters) :
    Belt P (P.J-1,0) ∧ Belt P (P.J,-1) := by
  constructor <;> apply rectangle_in_belt P <;> omega

end R002.GCSector
