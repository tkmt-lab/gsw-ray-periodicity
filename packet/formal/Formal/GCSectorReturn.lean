import Formal.GCSectorSurfaceMap

/-! The developed return identifies actual quotient vertices, not just coordinates. -/
namespace R002.GCSector
open GCPrimitive GCPrimitiveSurface Icosahedron

def returnTile (P : Parameters) (i : ℤ) (side : Bool) : Tile :=
  if side then ⟨P.q+1,P.q-i-6,false⟩ else ⟨P.q+1,P.q-i-5,true⟩

theorem return_coordinates_A (P : Parameters) (i : ℤ) (p : Lattice) :
    tileLocal P.k P.l (returnTile P i false) (H P p)=tileLocal P.k P.l ⟨i,-1,false⟩ p := by
  ext <;> dsimp [returnTile,tileLocal,tileBase,H,Parameters.K,Parameters.J,A3.gc] <;> ring

theorem return_coordinates_B (P : Parameters) (i : ℤ) (p : Lattice) :
    unframe P.k P.l 1 (tileLocal P.k P.l (returnTile P i true) (H P p))=
      tileLocal P.k P.l ⟨i,-1,true⟩ p := by
  ext <;> dsimp [returnTile,tileLocal,tileBase,H,Parameters.K,Parameters.J,A3.gc,unframe,GCPrimitive.turn] <;> ring

theorem return_interior (P : Parameters) (i : ℤ) (side : Bool) (p : Lattice)
    (hp : Interior P.k P.l (tileLocal P.k P.l ⟨i,-1,side⟩ p)) :
    Interior P.k P.l (tileLocal P.k P.l (returnTile P i side) (H P p)) := by
  cases side
  · rwa [return_coordinates_A]
  · apply (interior_unframe P.k P.l 1 _).mp
    rwa [return_coordinates_B]

theorem return_label_A (q i : ℤ) : returnDart q ((q-i-5:ℤ):ZMod 5) true=bandDart i false := by
  have he : (q : ZMod 5)-((q-i-5 : ℤ) : ZMod 5)=i := by push_cast; ring_nf; norm_num; decide +kernel
  simp only [returnDart,bandDart,ite_true,Bool.false_eq_true,ite_false,he]

theorem return_label_B (q i : ℤ) : returnDart q ((q-i-6:ℤ):ZMod 5) false=(labelB i,1) := by
  have he : (q : ZMod 5)-((q-i-6 : ℤ) : ZMod 5)-1=i := by push_cast; ring_nf; norm_num; decide +kernel
  simp only [returnDart,Bool.false_eq_true,ite_false,he]

theorem belt_tile_j (P : Parameters) (p : Lattice) (hb : Belt P p) (t : Tile)
    (ht : Interior P.k P.l (tileLocal P.k P.l t p)) : t.j= -1 := by
  have hT := norm_pos P.k P.l ((params_positive P).1.trans (params_positive P).2) (params_positive P).1.le
  apply interval_index_unique (norm P.k P.l) (b P.k P.l p) t.j (-1) hT (tile_box _ _ t p ht).2.2
  simpa only [Belt,neg_mul,one_mul,neg_add_cancel,zero_mul] using hb

/-- Once both positions lie in the verified strip, H identifies their actual vertices. -/
theorem strip_return (P : Parameters) (hprim : Primitive P.k P.l) (p : Lattice)
    (hp : InStrip P p) (hn : p≠(0,0)) (hH : InStrip P (H P p)) (hHn : H P p≠(0,0))
    (hb : Belt P p) : stripVertex P hprim (H P p) hH hHn=stripVertex P hprim p hp hn := by
  obtain ⟨t,ht,_⟩ := strip_tiles_cover P hprim p hp hn
  have hj := belt_tile_j P p hb t ht
  rcases t with ⟨i,j,side⟩
  dsimp at hj
  subst j
  have hi := return_interior P i side p ht
  have ha := strip_active P hprim (H P p) hH hHn (returnTile P i side) hi
  have hjr : (returnTile P i side).j≤ -2 := by
    have hq := P.hq
    cases side <;> simp [returnTile,Active] at ha ⊢ <;> omega
  rw [stripVertex_eq_chart P hprim (H P p) hH hHn _ hi,
    stripVertex_eq_chart P hprim p hp hn _ ht]
  cases side
  · have hd := dart_return P (P.q-i-5) hjr true
    rw [return_label_A] at hd
    unfold chartVertex
    apply congrArg vertex
    apply Prod.ext
    · simp only [returnTile,Bool.false_eq_true,ite_false,hd,dart_band]
    · apply congrArg Sum.inr
      apply Subtype.ext
      change unframe P.k P.l (tileDart P (returnTile P i false)).2 _=
        unframe P.k P.l (tileDart P ⟨i,-1,false⟩).2 _
      simp only [returnTile,Bool.false_eq_true,ite_false,hd,dart_band,bandDart,unframe]
      exact return_coordinates_A P i p

  · have hd := dart_return P (P.q-i-6) hjr false
    rw [return_label_B] at hd
    unfold chartVertex
    apply congrArg vertex
    apply Prod.ext
    · simp only [returnTile,ite_true,hd,dart_band,bandDart]
    · apply congrArg Sum.inr
      apply Subtype.ext
      change unframe P.k P.l (tileDart P (returnTile P i true)).2 _=
        unframe P.k P.l (tileDart P ⟨i,-1,true⟩).2 _
      simp only [returnTile,ite_true,hd,dart_band,bandDart,unframe]
      exact return_coordinates_B P i p


end R002.GCSector
