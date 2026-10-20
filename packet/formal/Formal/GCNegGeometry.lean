import Formal.GCNegNearCover

namespace R002.GCNeg
open GCPrimitive GCSector Icosahedron

theorem S_bounds (k l X M : ℤ) (hk : 0<k) (hl : 0<l)
    (hlo : k+l<norm k l) (hhi : k*X+(k+l)<M*norm k l)
    (p : Lattice) (hp : Region X p) :
    -norm k l<a k l p+b k l p ∧ a k l p+b k l p<M*norm k l := by
  have h0 := mul_nonneg hk.le hp.1
  have h1 := mul_le_mul_of_nonneg_left hp.2.1 hk.le
  have h2 := mul_le_mul_of_nonneg_left hp.2.2.1 (show 0≤k+l by omega)
  have h3 := mul_le_mul_of_nonneg_left hp.2.2.2 (show 0≤k+l by omega)
  dsimp [a,b]; constructor <;> nlinarith

theorem top_tile (k l X : ℤ) (hk : 0<k) (hl : 1<l) (hprim : Primitive k l)
    (H : ∀ u v, Region X (A3.gc k l u v) → A3.gc k l u v=(0,0))
    (p : Lattice) (hp : Region X p) (hn : p≠(0,0)) (t : Tile)
    (ht : Interior k l (tileLocal k l t p)) (hb : 0≤b k l p) : t=⟨0,0,true⟩ := by
  have hT := norm_pos k l hk (by omega)
  have hxy := height_identity k l p
  have hy : 0≤p.2 := by
    have hx := mul_nonneg (show 0≤l by omega) hp.1
    dsimp [b] at hb; nlinarith
  have ha : 0≤a k l p := add_nonneg (mul_nonneg (by omega) hp.1) (mul_nonneg (by omega) hy)
  have hkb := mul_nonneg hk.le hb
  have hy1 := mul_le_mul_of_nonneg_left hp.2.2.2 hT.le
  have hs : a k l p+b k l p<norm k l := by
    by_contra hn
    have hh := mul_le_mul_of_nonneg_left (show norm k l≤a k l p+b k l p by omega) (show 0≤l by omega)
    have hg := mul_pos (show 0<l-1 by omega) hT
    nlinarith
  have hc : Closed k l (tileLocal k l ⟨0,0,true⟩ p) := by
    rw [top_tile_turn,closed_turn]
    exact ⟨ha,hb,by dsimp [c]; omega⟩
  exact tile_unique k l hT t _ p ht (closed_interior_of_no_coarse k l X hk (by omega) hprim H p hp hn _ hc)

end R002.GCNeg
