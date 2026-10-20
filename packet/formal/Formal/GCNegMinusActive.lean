import Formal.GCNegPlusActive

namespace R002.GCNeg
open GCPrimitive GCSector

def MinusActive (P : TailParameters) (t : Tile) : Prop :=
  (t.i=0 ∧ t.j=0 ∧ t.side=true) ∨ (t.i= -1 ∧ t.j= -1) ∨ (t.i=0 ∧ t.j= -1) ∨
  (-P.a≤t.j ∧ t.j≤ -1 ∧ t.i+2*t.j= -1) ∨
  (-P.a-1≤t.j ∧ t.j≤ -2 ∧ (t.i+2*t.j= -3 ∨ t.i+2*t.j= -2)) ∨
  (t.j= -P.a-2 ∧ (t.i=2*P.a ∨ t.i=2*P.a+1))

set_option maxHeartbeats 1000000 in
theorem minus_active (P : TailParameters) (ha2 : 2≤P.a) (hprim : Primitive (minusK P) P.l)
    (p : Lattice) (hp : Region (minusA P) p) (hn : p≠(0,0)) (t : Tile)
    (ht : Interior (minusK P) P.l (tileLocal (minusK P) P.l t p)) : MinusActive P t := by
  have hbnd := minus_bounds P ha2
  have hr : 4≤P.r := by have := P.ht; have := P.htr; omega
  have hat := mul_le_mul_of_nonneg_right ha2 (show 0≤P.r by omega)
  have hrel : P.l=P.a*P.r+P.t := rfl
  have hkrel : minusK P=2*P.l-P.r := rfl
  have htl := P.ht
  have htr := P.htr
  have hk : 0<minusK P := by omega
  have hl : 1<P.l := by nlinarith
  have hT := norm_pos (minusK P) P.l hk (by omega)
  by_cases hb : 0≤b (minusK P) P.l p
  · have he := top_tile (minusK P) P.l (minusA P) hk hl hprim (minus_no_coarse P ha2) p hp hn t ht hb
    subst t; exact Or.inl ⟨rfl,rfl,rfl⟩
  have hbox := tile_box (minusK P) P.l t p ht
  have hh := tile_height_bounds (minusK P) P.l hk (by omega) t p ht
  have hlo : minusK P*(t.i+2*t.j)+P.r*t.i<2*p.2 := by
    have he : minusK P*(t.i+2*t.j)+P.r*t.i=2*(P.l*t.i+minusK P*t.j) := by dsimp [minusK]; ring
    rw [he]; linarith [hh.1]
  have hhi : 2*p.2<minusK P*(t.i+2*t.j+3)+P.r*(t.i+1) := by
    have he : minusK P*(t.i+2*t.j+3)+P.r*(t.i+1)=2*(P.l*(t.i+1)+minusK P*(t.j+1)) := by dsimp [minusK]; ring
    rw [he]; linarith [hh.2]
  have hs := S_bounds (minusK P) P.l (minusA P) (2*P.a+2) hk (by omega)
    (by linarith [hbnd.2.2.2.2.1]) (by linarith [hbnd.2.2.2.2.2.2]) p hp
  have hj : t.j≤ -1 := by
    by_contra h; have hh := mul_nonneg (show 0≤t.j by omega) hT.le; omega
  have hi0 : -1≤t.i := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_right (show t.i+1≤ -1 by omega) hT.le
    nlinarith [hbox.2.1,hs.1]
  have hi1 : t.i≤2*P.a+1 := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_right (show 2*P.a+2≤t.i by omega) hT.le
    nlinarith [hbox.1,hs.2]
  by_cases hi : t.i= -1
  · have hj' : t.j= -1 := by
      by_contra h
      have hm := mul_le_mul_of_nonneg_left (show t.j+1≤ -1 by omega) hk.le
      rw [hi] at hh; nlinarith [hh.2,hp.2.2.1]
    exact Or.inr (Or.inl ⟨hi,hj'⟩)
  by_cases hiz : t.i=0
  · have hj' : t.j= -1 := by
      by_contra h
      have hm := mul_le_mul_of_nonneg_left (show t.j+1≤ -1 by omega) hk.le
      rw [hiz] at hh; nlinarith [hh.2,hp.2.2.1]
    exact Or.inr (Or.inr (Or.inl ⟨hiz,hj'⟩))
  have hi : 1≤t.i := by omega
  have hm1 : t.i+2*t.j≤ -1 := by
    by_contra h
    have h1 := mul_nonneg hk.le (show 0≤t.i+2*t.j by omega)
    have h2 := mul_le_mul_of_nonneg_left hi (show 0≤P.r by omega)
    nlinarith [hp.2.2.2]
  by_cases hiq : t.i≤2*P.a-1
  · have hm0 : -3≤t.i+2*t.j := by
      by_contra h
      by_cases he : t.i=2*P.a-1
      · have hm5 : t.i+2*t.j≤ -5 := by omega
        have h1 := mul_le_mul_of_nonneg_left (show t.i+2*t.j+3≤ -2 by omega) hk.le
        rw [he] at hhi
        nlinarith [hp.2.2.1]
      · have h1 := mul_le_mul_of_nonneg_left (show t.i+2*t.j+3≤ -1 by omega) hk.le
        have h2 := mul_le_mul_of_nonneg_left (show t.i+1≤2*P.a-1 by omega) (show 0≤P.r by omega)
        nlinarith [hp.2.2.1]
    by_cases hm : t.i+2*t.j= -1
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,hj,hm⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega⟩))))
  · have hiend : t.i=2*P.a ∨ t.i=2*P.a+1 := by omega
    rcases hiend with he|he
    · have hm0 : -4≤t.i+2*t.j := by
        by_contra h
        have hm6 : t.i+2*t.j≤ -6 := by omega
        have h1 := mul_le_mul_of_nonneg_left (show t.i+2*t.j+3≤ -3 by omega) hk.le
        rw [he] at hhi
        nlinarith [hp.2.2.1]
      have hm : t.i+2*t.j= -4 ∨ t.i+2*t.j= -2 := by omega
      rcases hm with hm|hm
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,Or.inl he⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,Or.inr hm⟩))))
    · have hmhi : t.i+2*t.j≤ -3 := by
        by_contra h
        have hm : t.i+2*t.j= -1 := by omega
        rw [hm,he] at hlo
        nlinarith [hp.2.2.2]
      have hmlo : -3≤t.i+2*t.j := by
        by_contra h
        have hm5 : t.i+2*t.j≤ -5 := by omega
        have h1 := mul_le_mul_of_nonneg_left (show t.i+2*t.j+3≤ -2 by omega) hk.le
        rw [he] at hhi
        nlinarith [hp.2.2.1]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,Or.inr he⟩))))

end R002.GCNeg
