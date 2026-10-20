import Formal.GCPrimitiveSeamEdges
import Formal.GCPrimitiveSeparatedCharts
import Formal.ForcedContinuation

namespace R002.GCPrimitiveSurface
open Icosahedron GCPrimitive
variable {k l : ℤ}

theorem neighbor_faces_not_adjacent : ∀ (f : Face) (e d c : Corner),
    (mate ((mate (f,e)).1,c)).1≠(mate (f,d)).1 := by decide +kernel

theorem distinct_neighbor_no_adj (f : Face) (e d : Corner) (hne : e≠d) (p q : Point k l) :
    ¬(graph k l).Adj (vertex ((mate (f,e)).1,.inr p)) (vertex ((mate (f,d)).1,.inr q)) := by
  rw [ordinary_raw_adj_iff]
  rintro (⟨hf,_⟩|⟨c,a,b,ha,hb,_⟩)
  · exact hne (neighborFace_injective f hf)
  · have hc : c.1=(mate (f,e)).1 := (congrArg Prod.fst ha).symm
    have hh : (mate c).1=(mate (f,d)).1 := (congrArg Prod.fst hb).symm
    apply neighbor_faces_not_adjacent f e d c.2
    change (mate (c.1,c.2)).1=(mate (f,d)).1 at hh
    rwa [hc] at hh

theorem onFace_neighbor_adj_iff (hkl : l<k) (hl : 0<l) (f : Face) (e : Corner)
    (p q : Lattice) (x y : Vertex k l) (hx : OnFace f p x) (hy : OnNeighbor f e q y) :
    (graph k l).Adj x y ↔ Unit p q := by
  obtain ⟨⟨g,u⟩,hg,hp,rfl⟩ := hx
  change g=f at hg; subst g
  obtain ⟨s,hs,rfl⟩ := hy
  rw [seam_adj_iff_unit hkl hl (f,e) u (.inr s)]
  change Unit (frame k l e (position (f,u)))
    (opposite k l (frame k l (mate (f,e)).2 s.val)) ↔ Unit p q
  rw [hp,hs]
  exact frame_unit k l e p q

/-- This developed star is an induced unit-lattice graph, including seam corners. -/
theorem landing_adj_iff_unit (hkl : l<k) (hl : 0<l) (f : Face)
    (p q : Lattice) (x y : Vertex k l) (hx : Landing f p x) (hy : Landing f q y) :
    (graph k l).Adj x y ↔ Unit p q := by
  rcases hx with hx | ⟨e,hx⟩ <;> rcases hy with hy | ⟨d,hy⟩
  · obtain ⟨u,huf,hup,rfl⟩ := hx
    obtain ⟨v,hvf,hvp,rfl⟩ := hy
    rw [same_face_adj_iff_unit hkl hl u v (huf.trans hvf.symm),hup,hvp]
  · exact onFace_neighbor_adj_iff hkl hl f d p q x y hx hy
  · rw [(graph k l).adj_comm,onFace_neighbor_adj_iff hkl hl f e q p y x hy hx]
    exact ⟨fun h => unit_symm _ _ h,fun h => unit_symm _ _ h⟩
  · by_cases hed : e=d
    · subst d
      obtain ⟨r,hr,rfl⟩ := hx
      obtain ⟨s,hs,rfl⟩ := hy
      rw [same_face_adj_iff_unit hkl hl ((mate (f,e)).1,.inr r) ((mate (f,e)).1,.inr s) rfl]
      change Unit r.val s.val ↔ Unit p q
      rw [← frame_unit k l (mate (f,e)).2,← unit_opposite_iff k l,hr,hs]
      exact frame_unit k l e p q
    · have hp := onNeighbor_interior f e p x hx
      have hq := onNeighbor_interior f d q y hy
      obtain ⟨r,_,rfl⟩ := hx
      obtain ⟨s,_,rfl⟩ := hy
      exact iff_of_false (distinct_neighbor_no_adj f e d hed r s)
        (outside_distinct_no_unit (by omega) hl p q e d hed hp hq)

theorem unit_translate (p q r : Lattice) : Unit (p+q) (p+r) ↔ Unit q r := by
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i,add_left_cancel (by simpa only [add_assoc] using hi)⟩
  · rintro ⟨i,hi⟩
    exact ⟨i,by rw [hi,add_assoc]⟩

theorem direction_cycle : ∀ i j : Fin 6,
    Unit (direction i) (direction j) ↔ j=i+1 ∨ j=i+5 := by
  unfold GCPrimitive.Unit
  decide +kernel

theorem cycle_two_distinct : ∀ i : Fin 6, i+1≠i+5 := by decide +kernel

noncomputable def around (hk : 0<k) (hl : 0<l) (hprim : Primitive k l)
    (f : Face) (p : Point k l) (i : Fin 6) : Vertex k l :=
  (stepNeighbor hk hl hprim f p i).val

theorem around_injective (hk : 0<k) (hl : 0<l) (hprim : Primitive k l)
    (f : Face) (p : Point k l) : Function.Injective (around hk hl hprim f p) := by
  intro i j h
  exact (stepNeighbor_bijective hk hl hprim f p).1 (Subtype.ext h)

theorem around_complete (hk : 0<k) (hl : 0<l) (hprim : Primitive k l)
    (f : Face) (p : Point k l) (v : Vertex k l)
    (hv : (graph k l).Adj (vertex (f,.inr p)) v) : ∃ i, around hk hl hprim f p i=v := by
  obtain ⟨i,hi⟩ := (stepNeighbor_bijective hk hl hprim f p).2 ⟨v,hv⟩
  exact ⟨i,congrArg Subtype.val hi⟩

theorem around_adj (hk : 0<k) (hl : 0<l) (hprim : Primitive k l)
    (f : Face) (p : Point k l) (i : Fin 6) :
    (graph k l).Adj (vertex (f,.inr p)) (around hk hl hprim f p i) :=
  (stepNeighbor hk hl hprim f p i).property

theorem around_link (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (f : Face) (p : Point k l) (i j : Fin 6) :
    (graph k l).Adj (around (by omega) hl hprim f p i) (around (by omega) hl hprim f p j) ↔
      j=i+1 ∨ j=i+5 := by
  unfold around
  rw [landing_adj_iff_unit hkl hl f _ _ _ _
    (stepNeighbor_landing (by omega) hl hprim f p i)
    (stepNeighbor_landing (by omega) hl hprim f p j),unit_translate,direction_cycle]

theorem ordinary_two_common (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (f : Face) (p : Point k l) (c : Vertex k l)
    (hc : (graph k l).Adj (vertex (f,.inr p)) c) :
    ∃ x y, x≠y ∧ ∀ v, ((graph k l).Adj (vertex (f,.inr p)) v ∧ (graph k l).Adj c v) ↔
      v=x ∨ v=y := by
  have hk : 0<k := by omega
  obtain ⟨i,rfl⟩ := around_complete hk hl hprim f p c hc
  refine ⟨around hk hl hprim f p (i+1),around hk hl hprim f p (i+5),?_,?_⟩
  · exact fun h => cycle_two_distinct i (around_injective hk hl hprim f p h)
  · intro v
    constructor
    · rintro ⟨hv,hi⟩
      obtain ⟨j,rfl⟩ := around_complete hk hl hprim f p v hv
      exact ((around_link hkl hl hprim f p i j).mp hi).elim
        (fun h => Or.inl (congrArg (around hk hl hprim f p) h))
        (fun h => Or.inr (congrArg (around hk hl hprim f p) h))
    · rintro (rfl|rfl)
      · exact ⟨around_adj hk hl hprim f p _,(around_link hkl hl hprim f p _ _).mpr (Or.inl rfl)⟩
      · exact ⟨around_adj hk hl hprim f p _,(around_link hkl hl hprim f p _ _).mpr (Or.inr rfl)⟩

theorem two_common_neighbors (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) :
    R002.TwoCommonNeighbors (graph k l) := by
  intro b c
  refine Quotient.inductionOn₂ b c ?_
  rintro ⟨f,e|p⟩ ⟨g,d|q⟩ h
  · exact False.elim (no_parent_parent hkl hl f g e d h)
  · obtain ⟨x,y,hxy,hh⟩ := ordinary_two_common hkl hl hprim g q _ h.symm
    exact ⟨x,y,hxy,fun v => and_comm.trans (hh v)⟩
  · exact ordinary_two_common hkl hl hprim f p _ h
  · exact ordinary_two_common hkl hl hprim f p _ h

/-- A genuine unit-lattice triangle in the developed star, with ordinary first vertex.
No graph-adjacency or two-common-neighbor premise occurs in this definition. -/
def SmallTriangle (f : Face) (p : Point k l) (y z : Vertex k l) : Prop :=
  ∃ q r : Lattice, Unit p.val q ∧ Unit q r ∧ Unit r p.val ∧ Landing f q y ∧ Landing f r z

theorem smallTriangle_iff_edges (hkl : l<k) (hl : 0<l) (f : Face) (p : Point k l)
    (y z : Vertex k l) : SmallTriangle f p y z ↔
      (graph k l).Adj (vertex (f,.inr p)) y ∧ (graph k l).Adj y z ∧
      (graph k l).Adj z (vertex (f,.inr p)) := by
  constructor
  · rintro ⟨q,r,hq,hqr,hr,hy,hz⟩
    exact ⟨landing_is_edge f p q y hq hy,
      (landing_adj_iff_unit hkl hl f q r y z hy hz).mpr hqr,
      (landing_is_edge f p r z (unit_symm _ _ hr) hz).symm⟩
  · rintro ⟨hy,hyz,hz⟩
    obtain ⟨i,hi⟩ := (ordinary_adjacency_iff_directions f p y).mp hy
    obtain ⟨j,hj⟩ := (ordinary_adjacency_iff_directions f p z).mp hz.symm
    exact ⟨_,_,⟨i,rfl⟩,(landing_adj_iff_unit hkl hl f _ _ y z hi hj).mp hyz,
      unit_symm _ _ ⟨j,rfl⟩,hi,hj⟩

/-- Geometric triangles, allowing a cyclic choice of an ordinary center. -/
def Triangle (x y z : Vertex k l) : Prop :=
  (∃ f p, x=vertex (f,.inr p) ∧ SmallTriangle f p y z) ∨
  (∃ f p, y=vertex (f,.inr p) ∧ SmallTriangle f p z x) ∨
  (∃ f p, z=vertex (f,.inr p) ∧ SmallTriangle f p x y)

theorem triangle_iff_edges (hkl : l<k) (hl : 0<l) (x y z : Vertex k l) :
    Triangle x y z ↔ (graph k l).Adj x y ∧ (graph k l).Adj y z ∧ (graph k l).Adj z x := by
  constructor
  · rintro (⟨f,p,rfl,h⟩|⟨f,p,rfl,h⟩|⟨f,p,rfl,h⟩)
    · exact (smallTriangle_iff_edges hkl hl f p _ _).mp h
    · obtain ⟨h1,h2,h3⟩ := (smallTriangle_iff_edges hkl hl f p _ _).mp h
      exact ⟨h3,h1,h2⟩
    · obtain ⟨h1,h2,h3⟩ := (smallTriangle_iff_edges hkl hl f p _ _).mp h
      exact ⟨h2,h3,h1⟩
  · refine Quotient.inductionOn₂ x y ?_
    rintro ⟨f,e|p⟩ ⟨g,d|q⟩ ⟨hxy,hyz,hzx⟩
    · exact False.elim (no_parent_parent hkl hl f g e d hxy)
    · exact Or.inr (Or.inl ⟨g,q,rfl,(smallTriangle_iff_edges hkl hl g q _ _).mpr ⟨hyz,hzx,hxy⟩⟩)
    · exact Or.inl ⟨f,p,rfl,(smallTriangle_iff_edges hkl hl f p _ _).mpr ⟨hxy,hyz,hzx⟩⟩
    · exact Or.inl ⟨f,p,rfl,(smallTriangle_iff_edges hkl hl f p _ _).mpr ⟨hxy,hyz,hzx⟩⟩

end R002.GCPrimitiveSurface
