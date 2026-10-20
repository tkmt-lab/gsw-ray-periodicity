import Formal.GCSectorCompActive

namespace R002.GCNeg
open Icosahedron GCPrimitive GCPrimitiveSurface GCSector

def Region (A : ℤ) (p : Lattice) : Prop := 0≤p.1 ∧ p.1≤A ∧ -1≤p.2 ∧ p.2≤1

structure Atlas where
  k : ℤ
  l : ℤ
  A : ℤ
  hkl : l<k
  hl : 0<l
  hprim : Primitive k l
  hA : 2≤A
  active : Tile → Prop
  dart : Tile → Dart
  closedInterior : ∀ p, Region A p → p≠(0,0) → ∀ t,
    Closed k l (tileLocal k l t p) → Interior k l (tileLocal k l t p)
  activeOf : ∀ p, Region A p → p≠(0,0) → ∀ t,
    Interior k l (tileLocal k l t p) → active t
  compatible : ∀ t e, active t → active (tileNeighbor t e) →
    Compatible (dart t) e (dart (tileNeighbor t e)) (tileMateCorner t e)
  dartTop : dart ⟨0,0,true⟩=(0,0)
  dartLower : dart ⟨-1,-1,true⟩=(14,0)
  dartSecond : dart ⟨0,-1,false⟩=(5,0)

theorem Atlas.hk (S : Atlas) : 0<S.k := S.hl.trans S.hkl

theorem tiles_cover (S : Atlas) (p : Lattice) (hp : Region S.A p) (hn : p≠(0,0)) :
    ∃! t, Interior S.k S.l (tileLocal S.k S.l t p) := by
  have hT := norm_pos S.k S.l S.hk S.hl.le
  obtain ⟨t,ht⟩ := tiles_cover_closed S.k S.l hT p
  have hi := S.closedInterior p hp hn t ht
  exact ⟨t,hi,fun u hu => tile_unique S.k S.l hT u t p hu hi⟩

def chartPoint (S : Atlas) (t : Tile) (p : Lattice)
    (hp : Interior S.k S.l (tileLocal S.k S.l t p)) : Point S.k S.l :=
  ⟨unframe S.k S.l (S.dart t).2 (tileLocal S.k S.l t p),
    (interior_unframe S.k S.l _ _).mpr hp⟩

def chartVertex (S : Atlas) (t : Tile) (p : Lattice)
    (hp : Interior S.k S.l (tileLocal S.k S.l t p)) : Vertex S.k S.l :=
  vertex ((S.dart t).1,.inr (chartPoint S t p hp))

theorem chart_degree (S : Atlas) (t : Tile) (p : Lattice)
    (hp : Interior S.k S.l (tileLocal S.k S.l t p)) :
    ClaudeChallenge.deg (graph S.k S.l) (chartVertex S t p hp)=6 :=
  ordinary_neighbor_card S.hk
    S.hl S.hprim _ _

theorem chart_landing (S : Atlas)     (t u : Tile) (p q : Lattice)
    (ht : Interior S.k S.l (tileLocal S.k S.l t p))
    (hu : Interior S.k S.l (tileLocal S.k S.l u q)) (hat : S.active t) (hau : S.active u)
    (hq : Region S.A q) (hqn : q≠(0,0)) (hunit : Unit p q) :
    Landing (S.dart t).1
      (unframe S.k S.l (S.dart t).2 (tileLocal S.k S.l t q)) (chartVertex S u q hu) := by
  have hk := S.hk
  have hl := S.hl
  have hT := norm_pos S.k S.l hk hl.le
  rcases tile_step_covered S.k S.l hk hl t p q ht hunit with hc|⟨e,he⟩
  · have hi := S.closedInterior q hq hqn t hc
    have heu := tile_unique S.k S.l hT t u q hi hu
    subst u
    exact Or.inl ⟨((S.dart t).1,.inr (chartPoint S t q hu)),rfl,rfl,rfl⟩
  · have heu := tile_unique S.k S.l hT (tileNeighbor t e) u q he hu
    subst u
    have hcomp := S.compatible t e hat hau
    have hf := congrArg Prod.fst hcomp
    have hm := congrArg Prod.snd hcomp
    change (mate ((S.dart t).1,e+(S.dart t).2)).1=(S.dart (tileNeighbor t e)).1 at hf
    change (mate ((S.dart t).1,e+(S.dart t).2)).2=
      tileMateCorner t e+(S.dart (tileNeighbor t e)).2 at hm
    refine Or.inr ⟨e+(S.dart t).2,chartPoint S (tileNeighbor t e) q hu,?_,?_⟩
    · change opposite S.k S.l
        (frame S.k S.l (mate ((S.dart t).1,e+(S.dart t).2)).2
          (unframe S.k S.l (S.dart (tileNeighbor t e)).2
            (tileLocal S.k S.l (tileNeighbor t e) q)))=_
      rw [hm,frame_shift_cancel,frame_shift_cancel,neighbor_coordinates,frame_unframe,opposite_involution]
    · change vertex (_,Sum.inr (chartPoint S (tileNeighbor t e) q hu))=
        vertex (_,Sum.inr (chartPoint S (tileNeighbor t e) q hu))
      rw [hf]

theorem chart_adjacent (S : Atlas)     (t u : Tile) (p q : Lattice)
    (ht : Interior S.k S.l (tileLocal S.k S.l t p))
    (hu : Interior S.k S.l (tileLocal S.k S.l u q)) (hat : S.active t) (hau : S.active u)
    (hq : Region S.A q) (hqn : q≠(0,0)) (hunit : Unit p q) :
    (graph S.k S.l).Adj (chartVertex S t p ht) (chartVertex S u q hu) := by
  apply landing_is_edge (S.dart t).1 (chartPoint S t p ht)
    (unframe S.k S.l (S.dart t).2 (tileLocal S.k S.l t q))
  · exact (unframe_unit S.k S.l _ _ _).mpr (tile_unit_forward S.k S.l t p q hunit)
  · exact chart_landing S t u p q ht hu hat hau hq hqn hunit

noncomputable def stripTile (S : Atlas)     (p : Lattice) (hp : Region S.A p) (hn : p≠(0,0)) : Tile :=
  Classical.choose (tiles_cover S p hp hn)

theorem stripTile_interior (S : Atlas)     (p : Lattice) (hp : Region S.A p) (hn : p≠(0,0)) :
    Interior S.k S.l (tileLocal S.k S.l (stripTile S p hp hn) p) :=
  (Classical.choose_spec (tiles_cover S p hp hn)).1

theorem stripTile_active (S : Atlas)     (p : Lattice) (hp : Region S.A p) (hn : p≠(0,0)) : S.active (stripTile S p hp hn) :=
  S.activeOf p hp hn _ (stripTile_interior S p hp hn)

noncomputable def stripVertex (S : Atlas)     (p : Lattice) (hp : Region S.A p) (hn : p≠(0,0)) : Vertex S.k S.l :=
  chartVertex S (stripTile S p hp hn) p (stripTile_interior S p hp hn)

theorem stripVertex_eq_chart (S : Atlas)     (p : Lattice) (hp : Region S.A p) (hn : p≠(0,0)) (t : Tile)
    (ht : Interior S.k S.l (tileLocal S.k S.l t p)) :
    stripVertex S p hp hn=chartVertex S t p ht := by
  have hT := norm_pos S.k S.l S.hk S.hl.le
  have he := tile_unique S.k S.l hT _ t p (stripTile_interior S p hp hn) ht
  unfold stripVertex
  cases he
  rfl

theorem strip_degree (S : Atlas)     (p : Lattice) (hp : Region S.A p) (hn : p≠(0,0)) :
    ClaudeChallenge.deg (graph S.k S.l) (stripVertex S p hp hn)=6 :=
  chart_degree S _ _ _

theorem strip_landing (S : Atlas)     (p q : Lattice) (hp : Region S.A p) (hq : Region S.A q) (hpn : p≠(0,0)) (hqn : q≠(0,0))
    (hu : Unit p q) :
    let t := stripTile S p hp hpn
    Landing (S.dart t).1
      (unframe S.k S.l (S.dart t).2 (tileLocal S.k S.l t q)) (stripVertex S q hq hqn) :=
  chart_landing S _ _ p q (stripTile_interior S p hp hpn)
    (stripTile_interior S q hq hqn) (stripTile_active S p hp hpn)
    (stripTile_active S q hq hqn) hq hqn hu

theorem strip_adjacent (S : Atlas)     (p q : Lattice) (hp : Region S.A p) (hq : Region S.A q) (hpn : p≠(0,0)) (hqn : q≠(0,0))
    (hu : Unit p q) :
    (graph S.k S.l).Adj (stripVertex S p hp hpn) (stripVertex S q hq hqn) :=
  chart_adjacent S _ _ p q (stripTile_interior S p hp hpn)
    (stripTile_interior S q hq hqn) (stripTile_active S p hp hpn)
    (stripTile_active S q hq hqn) hq hqn hu

theorem strip_neighbor_injective (S : Atlas)     (p q r : Lattice) (hp : Region S.A p) (hq : Region S.A q) (hr : Region S.A r)
    (hpn : p≠(0,0)) (hqn : q≠(0,0)) (hrn : r≠(0,0)) (hu : Unit p q) (hv : Unit p r)
    (he : stripVertex S q hq hqn=stripVertex S r hr hrn) : q=r := by
  have h1 := strip_landing S p q hp hq hpn hqn hu
  have h2 := strip_landing S p r hp hr hpn hrn hv
  rw [← he] at h2
  have hpos := landing_position_injective _ _ _ _ h1 h2
  have hh := congrArg (frame S.k S.l (S.dart (stripTile S p hp hpn)).2) hpos
  simp only [frame_unframe] at hh
  exact tile_local_injective S.k S.l _ hh

end R002.GCNeg
