import Formal.GCNegGeometry

namespace R002.GCNeg
open GCPrimitive GCSector

def PlusActive (P : TailParameters) (t : Tile) : Prop :=
  (t.i=0 ∧ t.j=0 ∧ t.side=true) ∨ (t.i= -1 ∧ t.j= -1) ∨
  (-P.a-1≤t.j ∧ t.j≤ -1 ∧ -2≤t.i+2*t.j ∧ t.i+2*t.j≤0) ∨
  (t.i=2*P.a+3 ∧ -P.a-2≤t.j ∧ t.j≤ -P.a-1)

theorem plus_active (P : TailParameters) (hprim : Primitive (plusK P) P.l)
    (p : Lattice) (hp : Region (plusA P) p) (hn : p≠(0,0)) (t : Tile)
    (ht : Interior (plusK P) P.l (tileLocal (plusK P) P.l t p)) : PlusActive P t := by
  have hbnd := plus_bounds P
  have hr : 4≤P.r := by have := P.ht; have := P.htr; omega
  have hat := mul_le_mul_of_nonneg_right P.ha (show 0≤P.r by omega)
  have hrel : P.l=P.a*P.r+P.t := rfl
  have hkrel : plusK P=2*P.l+P.r := rfl
  have htl := P.ht
  have htr := P.htr
  have hk : 0<plusK P := by omega
  have hl : 1<P.l := by nlinarith
  have hT := norm_pos (plusK P) P.l hk (by omega)
  by_cases hb : 0≤b (plusK P) P.l p
  · have he := top_tile (plusK P) P.l (plusA P) hk hl hprim (plus_no_coarse P) p hp hn t ht hb
    subst t; exact Or.inl ⟨rfl,rfl,rfl⟩
  have hbox := tile_box (plusK P) P.l t p ht
  have hh := tile_height_bounds (plusK P) P.l hk (by omega) t p ht
  have hlo : plusK P*(t.i+2*t.j)-P.r*t.i<2*p.2 := by
    have he : plusK P*(t.i+2*t.j)-P.r*t.i=2*(P.l*t.i+plusK P*t.j) := by dsimp [plusK]; ring
    rw [he]; linarith [hh.1]
  have hhi : 2*p.2<plusK P*(t.i+2*t.j+3)-P.r*(t.i+1) := by
    have he : plusK P*(t.i+2*t.j+3)-P.r*(t.i+1)=2*(P.l*(t.i+1)+plusK P*(t.j+1)) := by dsimp [plusK]; ring
    rw [he]; linarith [hh.2]
  have hs := S_bounds (plusK P) P.l (plusA P) (2*P.a+4) hk (by omega)
    (by linarith [hbnd.2.2.2.2.1]) (by linarith [hbnd.2.2.2.2.2.2]) p hp
  have hj : t.j≤ -1 := by
    by_contra h; have hh := mul_nonneg (show 0≤t.j by omega) hT.le; omega
  have hi0 : -1≤t.i := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_right (show t.i+1≤ -1 by omega) hT.le
    nlinarith [hbox.2.1,hs.1]
  have hi1 : t.i≤2*P.a+3 := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_right (show 2*P.a+4≤t.i by omega) hT.le
    nlinarith [hbox.1,hs.2]
  by_cases hi : t.i= -1
  · have hj' : t.j= -1 := by
      by_contra h
      have hm := mul_le_mul_of_nonneg_left (show t.j+1≤ -1 by omega) hk.le
      rw [hi] at hh; nlinarith [hh.2,hp.2.2.1]
    exact Or.inr (Or.inl ⟨hi,hj'⟩)
  have hi : 0≤t.i := by omega
  have hm0 : -2≤t.i+2*t.j := by
    by_contra h
    have h1 := mul_nonpos_of_nonneg_of_nonpos hk.le (show t.i+2*t.j+3≤0 by omega)
    have h2 := mul_nonneg (show 0≤P.r by omega) hi
    nlinarith [hp.2.2.1]
  by_cases hiq : t.i≤2*P.a+2
  · have hm1 : t.i+2*t.j≤0 := by
      by_contra hm
      have h1 := mul_le_mul_of_nonneg_left (show 1≤t.i+2*t.j by omega) hk.le
      have hiend : t.i=2*P.a+2 := by
        by_contra he
        have h2 := mul_le_mul_of_nonneg_left (show t.i≤2*P.a+1 by omega) (show 0≤P.r by omega)
        nlinarith [hp.2.2.2]
      have hm2 : 2≤t.i+2*t.j := by omega
      have h2 := mul_le_mul_of_nonneg_left hm2 hk.le
      rw [hiend] at hlo
      nlinarith [hp.2.2.2]
    have hjq : -P.a-1≤t.j := by
      by_contra h
      have hiend : t.i=2*P.a+2 := by omega
      have hjend : t.j= -P.a-2 := by omega
      rw [hiend,hjend] at hhi
      nlinarith [hp.2.2.1]
    exact Or.inr (Or.inr (Or.inl ⟨hjq,hj,hm0,hm1⟩))
  · have hiend : t.i=2*P.a+3 := by omega
    have hm1 : t.i+2*t.j≤1 := by
      by_contra h
      have hm3 : 3≤t.i+2*t.j := by omega
      have h3 := mul_le_mul_of_nonneg_left hm3 hk.le
      rw [hiend] at hlo
      nlinarith [hp.2.2.2]
    exact Or.inr (Or.inr (Or.inr ⟨hiend,by omega,by omega⟩))

end R002.GCNeg
