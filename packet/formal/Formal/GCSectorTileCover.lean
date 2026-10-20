import Formal.GCSectorTiling
import Formal.GCSectorNoVertices

namespace R002.GCSector
open GCPrimitive Icosahedron

theorem floor_bounds (T x : ℤ) (hT : 0<T) :
    (x/T)*T≤x ∧ x<((x/T)+1)*T := by
  have h0 := Int.emod_nonneg x (ne_of_gt hT)
  have h1 := Int.emod_lt_of_pos x hT
  have he := Int.ediv_mul_add_emod x T
  constructor <;> nlinarith

theorem tiles_cover_closed (k l : ℤ) (hT : 0<norm k l) (p : Lattice) :
    ∃ t : Tile, Closed k l (tileLocal k l t p) := by
  let i := (a k l p+b k l p)/norm k l
  let j := b k l p/norm k l
  have hi := floor_bounds (norm k l) (a k l p+b k l p) hT
  have hj := floor_bounds (norm k l) (b k l p) hT
  change i*norm k l≤_ ∧ _<(i+1)*norm k l at hi
  change j*norm k l≤_ ∧ _<(j+1)*norm k l at hj
  by_cases ha : a k l p≤(i-j)*norm k l
  · refine ⟨⟨i,j,false⟩,?_⟩
    dsimp [Closed]
    have h := tile_slices_A k l i j p
    rw [h.1,h.2.1,h.2.2]
    exact ⟨by nlinarith,by nlinarith,by nlinarith⟩
  · refine ⟨⟨i,j,true⟩,?_⟩
    dsimp [Closed]
    have h := tile_slices_B k l i j p
    rw [h.1,h.2.1,h.2.2]
    exact ⟨by nlinarith,by nlinarith,by nlinarith⟩

theorem tile_corners_coarse (k l : ℤ) (t : Tile) (e : Corner) :
    ∃ u v : ℤ, tileEmbed k l t (corner k l e)=A3.gc k l u v := by
  rcases t with ⟨i,j,side⟩
  cases side <;> fin_cases e
  · exact ⟨i-j-1,j+1,by ext <;> simp [tileEmbed,tileBase,corner,A3.gc]⟩
  · exact ⟨i-j,j,by ext <;> simp [tileEmbed,tileBase,corner,A,B,A3.gc] <;> ring⟩
  · exact ⟨i-j,j+1,by ext <;> simp [tileEmbed,tileBase,corner,A,B,A3.gc] <;> ring⟩
  · exact ⟨i-j,j+1,by ext <;> simp [tileEmbed,tileBase,corner,A3.gc]⟩
  · exact ⟨i-j,j,by ext <;> simp [tileEmbed,tileBase,corner,A,B,A3.gc] <;> ring⟩
  · exact ⟨i-j+1,j,by ext <;> simp [tileEmbed,tileBase,corner,A,B,A3.gc] <;> ring⟩

theorem strip_not_tile_corner (P : Parameters) (p : Lattice) (hp : InStrip P p) (hn : p≠(0,0))
    (t : Tile) (e : Corner) : tileLocal P.k P.l t p≠corner P.k P.l e := by
  intro he
  have hx : p=tileEmbed P.k P.l t (corner P.k P.l e) :=
    (tile_inverse P.k P.l t p).1.symm.trans (congrArg (tileEmbed P.k P.l t) he)
  obtain ⟨u,v,hv⟩ := tile_corners_coarse P.k P.l t e
  have hpp := hx.trans hv
  have hh := coarse_strip_only_origin P u v (hpp ▸ hp)
  exact hn (hpp.trans hh)

theorem strip_closed_interior (P : Parameters) (hprim : Primitive P.k P.l)
    (p : Lattice) (hp : InStrip P p) (hn : p≠(0,0)) (t : Tile)
    (ht : Closed P.k P.l (tileLocal P.k P.l t p)) : Interior P.k P.l (tileLocal P.k P.l t p) := by
  have hk : 0<P.k := (params_positive P).1.trans (params_positive P).2
  rcases closed_partition P.k P.l hk (params_positive P).1.le hprim _ ht with h|h|h|h
  · exact False.elim (strip_not_tile_corner P p hp hn t 0 h)
  · exact False.elim (strip_not_tile_corner P p hp hn t 1 h)
  · exact False.elim (strip_not_tile_corner P p hp hn t 2 h)
  · exact h

theorem strip_tiles_cover (P : Parameters) (hprim : Primitive P.k P.l)
    (p : Lattice) (hp : InStrip P p) (hn : p≠(0,0)) :
    ∃! t : Tile, Interior P.k P.l (tileLocal P.k P.l t p) := by
  have hT := norm_pos P.k P.l ((params_positive P).1.trans (params_positive P).2) (params_positive P).1.le
  obtain ⟨t,ht⟩ := tiles_cover_closed P.k P.l hT p
  have hi := strip_closed_interior P hprim p hp hn t ht
  exact ⟨t,hi,fun u hu => tile_unique P.k P.l hT u t p hu hi⟩

end R002.GCSector
