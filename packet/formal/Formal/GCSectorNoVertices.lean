import Formal.GCSectorArithmetic

/-! No coarse lattice vertex lies in the entire bounded strip except its origin. -/
namespace R002.GCSector
open GCPrimitive

theorem coarse_slices (k l u v : ℤ) :
    a k l (A3.gc k l u v)=norm k l*u ∧
    b k l (A3.gc k l u v)=norm k l*v := by
  dsimp [a,b,GCPrimitive.norm,A3.gc]
  constructor <;> ring

theorem coarse_gap_identity (P : Parameters) :
    2*norm P.k P.l-P.k-P.l*(P.K-1)=
      (P.k-2*P.l)*(P.k+2*P.l)+(P.s-1)*P.k+P.l := by
  dsimp [GCPrimitive.norm,Parameters.K,Parameters.k]
  ring

theorem coarse_gap (P : Parameters) : 0<2*norm P.k P.l-P.k-P.l*(P.K-1) := by
  rw [coarse_gap_identity]
  have hk := k_ge P
  have hl := l_ge_four P
  have hs := P.hs
  have h1 := mul_pos (show 0<P.k-2*P.l by omega) (show 0<P.k+2*P.l by omega)
  have h2 := mul_nonneg (show 0≤P.s-1 by omega) (show 0≤P.k by omega)
  omega

def InStrip (P : Parameters) (p : Lattice) : Prop :=
  0≤p.1 ∧ p.1≤P.K-1 ∧ -1≤p.2 ∧ p.2≤1

theorem coarse_strip_only_origin (P : Parameters) (u v : ℤ)
    (h : InStrip P (A3.gc P.k P.l u v)) : A3.gc P.k P.l u v=(0,0) := by
  have hl := l_ge_four P
  have hk := k_ge P
  have hs := P.hs
  have hsl := P.hsl
  obtain ⟨hx0,hx1,hy0,hy1⟩ := h
  change 0≤P.k*u-P.l*v at hx0
  change P.k*u-P.l*v≤P.K-1 at hx1
  change -1≤P.l*u+(P.k+P.l)*v at hy0
  change P.l*u+(P.k+P.l)*v≤1 at hy1
  by_cases hv : 0≤v
  · have hu : 0≤u := by
      by_contra h
      have : u≤ -1 := by omega
      nlinarith [mul_nonneg (show 0≤P.l by omega) hv,
        mul_nonpos_of_nonneg_of_nonpos (show 0≤P.k by omega) (show u+1≤0 by omega)]
    have hu0 : u=0 := by
      by_contra h
      have : 1≤u := by omega
      nlinarith [mul_nonneg (show 0≤P.k+P.l by omega) hv,
        mul_nonneg (show 0≤P.l by omega) (show 0≤u-1 by omega)]
    have hv0 : v=0 := by
      rw [hu0] at hy1
      by_contra h
      have : 1≤v := by omega
      nlinarith [mul_nonneg (show 0≤P.k+P.l by omega) (show 0≤v-1 by omega)]
    simp [A3.gc,hu0,hv0]
  by_cases hv1 : v= -1
  · have he : P.l*u+(P.k+P.l)*v=P.l*(u-P.q-1)-P.s := by
      rw [hv1]; dsimp [Parameters.k]; ring
    rw [he] at hy0 hy1
    exact False.elim (no_positive_strip P.l (u-P.q-1) (by omega) (by omega) (by omega))
  · have hv2 : v≤ -2 := by omega
    have hT := norm_pos P.k P.l (by omega) (by omega)
    have hb := (coarse_slices P.k P.l u v).2
    have hnv := mul_le_mul_of_nonneg_left hv2 hT.le
    have hpy := mul_le_mul_of_nonneg_left hy0 (show 0≤P.k by omega)
    have hpx := mul_le_mul_of_nonneg_left hx1 (show 0≤P.l by omega)
    have hg := coarse_gap P
    dsimp [b,A3.gc] at hb
    nlinarith

end R002.GCSector
