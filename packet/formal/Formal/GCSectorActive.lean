import Formal.GCSectorTileCover

/-! The bounded horizontal strip uses only the first belt, two caps, and the return belt. -/
namespace R002.GCSector
open GCPrimitive

def Active (P : Parameters) (t : Tile) : Prop :=
  (t.j= -1 ∧ t.i≤P.q) ∨ (t.i=P.q ∧ t.j= -2) ∨
  (t.i=P.q+1 ∧ t.j≤ -2) ∨ (t.i=0 ∧ t.j=0 ∧ t.side=true)

theorem height_identity (k l : ℤ) (p : Lattice) :
    l*(a k l p+b k l p)+k*b k l p=norm k l*p.2 := by
  dsimp [a,b,GCPrimitive.norm]; ring

theorem tile_height_bounds (k l : ℤ) (hk : 0<k) (hl : 0<l) (t : Tile) (p : Lattice)
    (hp : Interior k l (tileLocal k l t p)) :
    l*t.i+k*t.j<p.2 ∧ p.2<l*(t.i+1)+k*(t.j+1) := by
  have h := tile_box k l t p hp
  have hT := norm_pos k l hk hl.le
  have h1 := add_lt_add (mul_lt_mul_of_pos_left h.1 hl) (mul_lt_mul_of_pos_left h.2.2.1 hk)
  have h2 := add_lt_add (mul_lt_mul_of_pos_left h.2.1 hl) (mul_lt_mul_of_pos_left h.2.2.2 hk)
  rw [height_identity] at h1 h2
  constructor
  · apply (mul_lt_mul_iff_right₀ hT).mp
    convert h1 using 1 <;> ring
  · apply (mul_lt_mul_iff_right₀ hT).mp
    convert h2 using 1 <;> ring

theorem strip_S_upper (P : Parameters) (p : Lattice) (hp : InStrip P p) :
    a P.k P.l p+b P.k P.l p<(P.q+2)*norm P.k P.l := by
  have hk := (params_positive P).1.trans (params_positive P).2
  have hl := (params_positive P).1
  have h1 := mul_le_mul_of_nonneg_left hp.2.1 hk.le
  have h2 := mul_le_mul_of_nonneg_left hp.2.2.2 (show 0≤P.k+P.l by omega)
  have he : (P.q+2)*norm P.k P.l-(P.k*P.K+P.l)=P.l*(P.J-1) := by
    dsimp [GCPrimitive.norm,Parameters.K,Parameters.J]; ring
  have hj := J_ge P
  have hpos := mul_pos hl (show 0<P.J-1 by omega)
  dsimp [a,b]
  nlinarith

theorem upper_cap_closed (P : Parameters) (p : Lattice) (hp : InStrip P p)
    (hb : 0≤b P.k P.l p) : Closed P.k P.l p := by
  have hk := (params_positive P).1.trans (params_positive P).2
  have hl := (params_positive P).1
  have hl4 := l_ge_four P
  have hT := norm_pos P.k P.l hk hl.le
  have hxy := height_identity P.k P.l p
  have hy : 0≤p.2 := by
    have hx := mul_nonneg hl.le hp.1
    dsimp [b] at hb; nlinarith
  have ha : 0≤a P.k P.l p := by
    exact add_nonneg (mul_nonneg (by omega) hp.1) (mul_nonneg hl.le hy)
  have hkb := mul_nonneg hk.le hb
  have hy1 := mul_le_mul_of_nonneg_left hp.2.2.2 hT.le
  have hS : a P.k P.l p+b P.k P.l p<norm P.k P.l := by
    by_contra hn
    have hmul := mul_le_mul_of_nonneg_left (show norm P.k P.l≤a P.k P.l p+b P.k P.l p by omega) hl.le
    have hneg := mul_pos (show 0<P.l-1 by omega) hT
    nlinarith
  exact ⟨ha,hb,by dsimp [c]; omega⟩

theorem top_tile_turn (k l : ℤ) (p : Lattice) :
    tileLocal k l ⟨0,0,true⟩ p=GCPrimitive.turn k l p := by
  ext <;> simp [tileLocal,tileBase,A3.gc,GCPrimitive.turn] <;> ring

theorem strip_active (P : Parameters) (hprim : Primitive P.k P.l)
    (p : Lattice) (hp : InStrip P p) (hn : p≠(0,0)) (t : Tile)
    (ht : Interior P.k P.l (tileLocal P.k P.l t p)) : Active P t := by
  have hl := (params_positive P).1
  have hk := hl.trans (params_positive P).2
  have hT := norm_pos P.k P.l hk hl.le
  have hs := P.hs
  have hsl := P.hsl
  have hl4 := l_ge_four P
  have hk3 := k_ge P
  have hqy : P.l*P.q=P.k-P.s := by dsimp [Parameters.k]; ring
  have hbox := tile_box P.k P.l t p ht
  have hheight := tile_height_bounds P.k P.l hk hl t p ht
  by_cases hb : 0≤b P.k P.l p
  · have hc := upper_cap_closed P p hp hb
    have htc : Closed P.k P.l (tileLocal P.k P.l ⟨0,0,true⟩ p) := by
      rw [top_tile_turn,closed_turn]; exact hc
    have hti := strip_closed_interior P hprim p hp hn _ htc
    have he := tile_unique P.k P.l hT t ⟨0,0,true⟩ p ht hti
    subst t
    exact Or.inr (Or.inr (Or.inr ⟨rfl,rfl,rfl⟩))
  have hj : t.j≤ -1 := by
    by_contra h
    have hmul := mul_nonneg (show 0≤t.j by omega) hT.le
    omega
  by_cases hj1 : t.j= -1
  · left
    refine ⟨hj1,?_⟩
    by_contra hi
    have hmul := mul_le_mul_of_nonneg_left (show P.q+1≤t.i by omega) hl.le
    rw [hj1] at hheight
    nlinarith [hp.2.2.2]
  have hj2 : t.j≤ -2 := by omega
  have hi0 : P.q≤t.i := by
    by_contra h
    have h1 := mul_le_mul_of_nonneg_left (show t.i+1≤P.q by omega) hl.le
    have h2 := mul_le_mul_of_nonneg_left (show t.j+1≤ -1 by omega) hk.le
    nlinarith [hp.2.2.1]
  have hi1 : t.i≤P.q+1 := by
    have hsmax := strip_S_upper P p hp
    by_contra h
    have h1 := mul_le_mul_of_nonneg_right (show P.q+2≤t.i by omega) hT.le
    nlinarith [hbox.1]
  by_cases hiq : t.i=P.q
  · have hjexact : t.j= -2 := by
      by_contra h
      have h1 := mul_le_mul_of_nonneg_left (show t.j+1≤ -2 by omega) hk.le
      rw [hiq] at hheight
      nlinarith [hp.2.2.1]
    exact Or.inr (Or.inl ⟨hiq,hjexact⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by omega,hj2⟩))

end R002.GCSector
