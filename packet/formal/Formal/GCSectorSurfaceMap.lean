import Formal.GCSectorLabels

/-! The developed patch is mapped to the actual primitive quotient, with real adjacency. -/
namespace R002.GCSector
open Icosahedron GCPrimitive GCPrimitiveSurface

def chartPoint (P : Parameters) (t : Tile) (p : Lattice)
    (hp : Interior P.k P.l (tileLocal P.k P.l t p)) : Point P.k P.l :=
  ⟨unframe P.k P.l (tileDart P t).2 (tileLocal P.k P.l t p),
    (interior_unframe P.k P.l _ _).mpr hp⟩

def chartVertex (P : Parameters) (t : Tile) (p : Lattice)
    (hp : Interior P.k P.l (tileLocal P.k P.l t p)) : Vertex P.k P.l :=
  vertex ((tileDart P t).1,.inr (chartPoint P t p hp))

theorem chart_degree (P : Parameters) (hprim : Primitive P.k P.l) (t : Tile) (p : Lattice)
    (hp : Interior P.k P.l (tileLocal P.k P.l t p)) :
    ClaudeChallenge.deg (graph P.k P.l) (chartVertex P t p hp)=6 :=
  ordinary_neighbor_card ((params_positive P).1.trans (params_positive P).2)
    (params_positive P).1 hprim _ _

theorem chart_landing (P : Parameters) (hprim : Primitive P.k P.l)
    (t u : Tile) (p q : Lattice)
    (ht : Interior P.k P.l (tileLocal P.k P.l t p))
    (hu : Interior P.k P.l (tileLocal P.k P.l u q)) (hat : Active P t) (hau : Active P u)
    (hq : InStrip P q) (hqn : q≠(0,0)) (hunit : Unit p q) :
    Landing (tileDart P t).1
      (unframe P.k P.l (tileDart P t).2 (tileLocal P.k P.l t q)) (chartVertex P u q hu) := by
  have hk := (params_positive P).1.trans (params_positive P).2
  have hl := (params_positive P).1
  have hT := norm_pos P.k P.l hk hl.le
  rcases tile_step_covered P.k P.l hk hl t p q ht hunit with hc|⟨e,he⟩
  · have hi := strip_closed_interior P hprim q hq hqn t hc
    have heu := tile_unique P.k P.l hT t u q hi hu
    subst u
    exact Or.inl ⟨((tileDart P t).1,.inr (chartPoint P t q hu)),rfl,rfl,rfl⟩
  · have heu := tile_unique P.k P.l hT (tileNeighbor t e) u q he hu
    subst u
    have hcomp := active_compatible P t e hat hau
    have hf := congrArg Prod.fst hcomp
    have hm := congrArg Prod.snd hcomp
    change (mate ((tileDart P t).1,e+(tileDart P t).2)).1=(tileDart P (tileNeighbor t e)).1 at hf
    change (mate ((tileDart P t).1,e+(tileDart P t).2)).2=
      tileMateCorner t e+(tileDart P (tileNeighbor t e)).2 at hm
    refine Or.inr ⟨e+(tileDart P t).2,chartPoint P (tileNeighbor t e) q hu,?_,?_⟩
    · change opposite P.k P.l
        (frame P.k P.l (mate ((tileDart P t).1,e+(tileDart P t).2)).2
          (unframe P.k P.l (tileDart P (tileNeighbor t e)).2
            (tileLocal P.k P.l (tileNeighbor t e) q)))=_
      rw [hm,frame_shift_cancel,frame_shift_cancel,neighbor_coordinates,frame_unframe,opposite_involution]
    · change vertex (_,Sum.inr (chartPoint P (tileNeighbor t e) q hu))=
        vertex (_,Sum.inr (chartPoint P (tileNeighbor t e) q hu))
      rw [hf]

theorem chart_adjacent (P : Parameters) (hprim : Primitive P.k P.l)
    (t u : Tile) (p q : Lattice)
    (ht : Interior P.k P.l (tileLocal P.k P.l t p))
    (hu : Interior P.k P.l (tileLocal P.k P.l u q)) (hat : Active P t) (hau : Active P u)
    (hq : InStrip P q) (hqn : q≠(0,0)) (hunit : Unit p q) :
    (graph P.k P.l).Adj (chartVertex P t p ht) (chartVertex P u q hu) := by
  apply landing_is_edge (tileDart P t).1 (chartPoint P t p ht)
    (unframe P.k P.l (tileDart P t).2 (tileLocal P.k P.l t q))
  · exact (unframe_unit P.k P.l _ _ _).mpr (tile_unit_forward P.k P.l t p q hunit)
  · exact chart_landing P hprim t u p q ht hu hat hau hq hqn hunit

noncomputable def stripTile (P : Parameters) (hprim : Primitive P.k P.l)
    (p : Lattice) (hp : InStrip P p) (hn : p≠(0,0)) : Tile :=
  Classical.choose (strip_tiles_cover P hprim p hp hn)

theorem stripTile_interior (P : Parameters) (hprim : Primitive P.k P.l)
    (p : Lattice) (hp : InStrip P p) (hn : p≠(0,0)) :
    Interior P.k P.l (tileLocal P.k P.l (stripTile P hprim p hp hn) p) :=
  (Classical.choose_spec (strip_tiles_cover P hprim p hp hn)).1

theorem stripTile_active (P : Parameters) (hprim : Primitive P.k P.l)
    (p : Lattice) (hp : InStrip P p) (hn : p≠(0,0)) : Active P (stripTile P hprim p hp hn) :=
  strip_active P hprim p hp hn _ (stripTile_interior P hprim p hp hn)

noncomputable def stripVertex (P : Parameters) (hprim : Primitive P.k P.l)
    (p : Lattice) (hp : InStrip P p) (hn : p≠(0,0)) : Vertex P.k P.l :=
  chartVertex P (stripTile P hprim p hp hn) p (stripTile_interior P hprim p hp hn)

theorem stripVertex_eq_chart (P : Parameters) (hprim : Primitive P.k P.l)
    (p : Lattice) (hp : InStrip P p) (hn : p≠(0,0)) (t : Tile)
    (ht : Interior P.k P.l (tileLocal P.k P.l t p)) :
    stripVertex P hprim p hp hn=chartVertex P t p ht := by
  have hT := norm_pos P.k P.l ((params_positive P).1.trans (params_positive P).2) (params_positive P).1.le
  have he := tile_unique P.k P.l hT _ t p (stripTile_interior P hprim p hp hn) ht
  unfold stripVertex
  cases he
  rfl

theorem strip_degree (P : Parameters) (hprim : Primitive P.k P.l)
    (p : Lattice) (hp : InStrip P p) (hn : p≠(0,0)) :
    ClaudeChallenge.deg (graph P.k P.l) (stripVertex P hprim p hp hn)=6 :=
  chart_degree P hprim _ _ _

theorem strip_landing (P : Parameters) (hprim : Primitive P.k P.l)
    (p q : Lattice) (hp : InStrip P p) (hq : InStrip P q) (hpn : p≠(0,0)) (hqn : q≠(0,0))
    (hu : Unit p q) :
    let t := stripTile P hprim p hp hpn
    Landing (tileDart P t).1
      (unframe P.k P.l (tileDart P t).2 (tileLocal P.k P.l t q)) (stripVertex P hprim q hq hqn) :=
  chart_landing P hprim _ _ p q (stripTile_interior P hprim p hp hpn)
    (stripTile_interior P hprim q hq hqn) (stripTile_active P hprim p hp hpn)
    (stripTile_active P hprim q hq hqn) hq hqn hu

theorem strip_adjacent (P : Parameters) (hprim : Primitive P.k P.l)
    (p q : Lattice) (hp : InStrip P p) (hq : InStrip P q) (hpn : p≠(0,0)) (hqn : q≠(0,0))
    (hu : Unit p q) :
    (graph P.k P.l).Adj (stripVertex P hprim p hp hpn) (stripVertex P hprim q hq hqn) :=
  chart_adjacent P hprim _ _ p q (stripTile_interior P hprim p hp hpn)
    (stripTile_interior P hprim q hq hqn) (stripTile_active P hprim p hp hpn)
    (stripTile_active P hprim q hq hqn) hq hqn hu

theorem strip_neighbor_injective (P : Parameters) (hprim : Primitive P.k P.l)
    (p q r : Lattice) (hp : InStrip P p) (hq : InStrip P q) (hr : InStrip P r)
    (hpn : p≠(0,0)) (hqn : q≠(0,0)) (hrn : r≠(0,0)) (hu : Unit p q) (hv : Unit p r)
    (he : stripVertex P hprim q hq hqn=stripVertex P hprim r hr hrn) : q=r := by
  have h1 := strip_landing P hprim p q hp hq hpn hqn hu
  have h2 := strip_landing P hprim p r hp hr hpn hrn hv
  rw [← he] at h2
  have hpos := landing_position_injective _ _ _ _ h1 h2
  have hh := congrArg (frame P.k P.l (tileDart P (stripTile P hprim p hp hpn)).2) hpos
  simp only [frame_unframe] at hh
  exact tile_local_injective P.k P.l _ hh

end R002.GCSector
