import Formal.GCSectorCompCover

namespace R002.GCSector
open GCPrimitive

def CompActive (P : Parameters) (t : Tile) : Prop :=
  (t.i=0 ∧ t.j=0 ∧ t.side=true) ∨ (t.i= -1 ∧ t.j= -1) ∨
  (-P.q≤t.j ∧ t.j≤ -1 ∧ (t.i+t.j= -1 ∨ t.i+t.j=0)) ∨
  (t.i=P.q+1 ∧ -P.q-1≤t.j ∧ t.j≤ -P.q)

theorem comp_S_bounds (P : Parameters) (p : Lattice) (hp : CompStrip P p) :
    -norm P.k (compL P)<a P.k (compL P) p+b P.k (compL P) p ∧
    a P.k (compL P) p+b P.k (compL P) p<(P.q+2)*norm P.k (compL P) := by
  have hk := (comp_positive P).1.trans (comp_positive P).2
  have hl := (comp_positive P).1
  have hgap := comp_strip_gaps P
  have h0 := mul_nonneg hk.le hp.1
  have h1 := mul_le_mul_of_nonneg_left hp.2.1 hk.le
  have h2 := mul_le_mul_of_nonneg_left hp.2.2.1 (show 0≤P.k+compL P by omega)
  have h3 := mul_le_mul_of_nonneg_left hp.2.2.2 (show 0≤P.k+compL P by omega)
  dsimp [a,b,compL] at *
  constructor <;> nlinarith

theorem comp_top_closed (P : Parameters) (p : Lattice) (hp : CompStrip P p)
    (hb : 0≤b P.k (compL P) p) : Closed P.k (compL P) p := by
  have hl : 1<compL P := by have := k_ge P; have := l_ge_four P; dsimp [compL]; omega
  have hk := (comp_positive P).1.trans (comp_positive P).2
  have hT := norm_pos P.k (compL P) hk (by omega)
  have hxy := height_identity P.k (compL P) p
  have hy : 0≤p.2 := by
    have hx := mul_nonneg (show 0≤compL P by omega) hp.1
    dsimp [b] at hb; nlinarith
  have ha : 0≤a P.k (compL P) p := add_nonneg
    (mul_nonneg (by omega) hp.1) (mul_nonneg (by omega) hy)
  have hkb := mul_nonneg hk.le hb
  have hy1 := mul_le_mul_of_nonneg_left hp.2.2.2 hT.le
  have hS : a P.k (compL P) p+b P.k (compL P) p<norm P.k (compL P) := by
    by_contra hn
    have hh := mul_le_mul_of_nonneg_left (show norm P.k (compL P)≤a P.k (compL P) p+b P.k (compL P) p by omega)
      (show 0≤compL P by omega)
    have hg := mul_pos (show 0<compL P-1 by omega) hT
    nlinarith
  exact ⟨ha,hb,by dsimp [c]; omega⟩

theorem comp_strip_active (P : Parameters) (hprim : Primitive P.k (compL P))
    (p : Lattice) (hp : CompStrip P p) (hn : p≠(0,0)) (t : Tile)
    (ht : Interior P.k (compL P) (tileLocal P.k (compL P) t p)) : CompActive P t := by
  have hk := (comp_positive P).1.trans (comp_positive P).2
  have hl := (comp_positive P).1
  have hh := l_ge_four P
  have hs := P.hs
  have hsl := P.hsl
  have hq := P.hq
  have he : P.k=P.q*P.l+P.s := rfl
  have hT := norm_pos P.k (compL P) hk hl.le
  have hbox := tile_box P.k (compL P) t p ht
  have hheight := tile_height_bounds P.k (compL P) hk hl t p ht
  have hlow : P.k*(t.i+t.j)-P.l*t.i<p.2 := by dsimp [compL] at hheight; nlinarith [hheight.1]
  have hhigh : p.2<P.k*(t.i+t.j+2)-P.l*(t.i+1) := by dsimp [compL] at hheight; nlinarith [hheight.2]
  by_cases hb : 0≤b P.k (compL P) p
  · have hc := comp_top_closed P p hp hb
    have htc : Closed P.k (compL P) (tileLocal P.k (compL P) ⟨0,0,true⟩ p) := by
      rw [top_tile_turn,closed_turn]; exact hc
    have hti := comp_closed_interior P hprim p hp hn _ htc
    have ht' := tile_unique P.k (compL P) hT t ⟨0,0,true⟩ p ht hti
    subst t; exact Or.inl ⟨rfl,rfl,rfl⟩
  have hj : t.j≤ -1 := by
    by_contra h
    have hmul := mul_nonneg (show 0≤t.j by omega) hT.le
    omega
  have hS := comp_S_bounds P p hp
  have hi0 : -1≤t.i := by
    by_contra h
    have hmul := mul_le_mul_of_nonneg_right (show t.i+1≤ -1 by omega) hT.le
    nlinarith [hbox.2.1,hS.1]
  have hi1 : t.i≤P.q+1 := by
    by_contra h
    have hmul := mul_le_mul_of_nonneg_right (show P.q+2≤t.i by omega) hT.le
    nlinarith [hbox.1,hS.2]
  by_cases hi : t.i= -1
  · have hj' : t.j= -1 := by
      by_contra h
      have hmul := mul_le_mul_of_nonneg_left (show t.i+t.j+2≤ -1 by omega) hk.le
      rw [hi] at hhigh
      nlinarith [hp.2.2.1]
    exact Or.inr (Or.inl ⟨hi,hj'⟩)
  have hi : 0≤t.i := by omega
  have hsum0 : -1≤t.i+t.j := by
    by_contra h
    have h1 := mul_nonpos_of_nonneg_of_nonpos hk.le (show t.i+t.j+2≤0 by omega)
    have h2 := mul_nonneg (show 0≤P.l by omega) hi
    nlinarith [hp.2.2.1]
  by_cases hiq : t.i≤P.q
  · have hsum1 : t.i+t.j≤0 := by
      by_contra h
      have h1 := mul_le_mul_of_nonneg_left (show 1≤t.i+t.j by omega) hk.le
      have h2 := mul_le_mul_of_nonneg_left hiq (show 0≤P.l by omega)
      nlinarith [hp.2.2.2]
    have hjq : -P.q≤t.j := by
      by_contra h
      have hii : t.i=P.q := by omega
      have hjj : t.j= -P.q-1 := by omega
      rw [hii,hjj] at hhigh
      nlinarith [hp.2.2.1]
    exact Or.inr (Or.inr (Or.inl ⟨hjq,hj,by omega⟩))
  · have hii : t.i=P.q+1 := by omega
    have hsum1 : t.i+t.j≤1 := by
      by_contra h
      have h1 := mul_le_mul_of_nonneg_left (show 2≤t.i+t.j by omega) hk.le
      rw [hii] at hlow
      have hkl := k_ge P
      nlinarith [hp.2.2.2]
    have hsum0' : 0≤t.i+t.j := by
      by_contra h
      have heq : t.i+t.j= -1 := by omega
      rw [heq,hii] at hhigh
      nlinarith [hp.2.2.1]
    exact Or.inr (Or.inr (Or.inr ⟨hii,by omega,by omega⟩))

end R002.GCSector
