import Formal.GCPrimitiveCanonical

/-! A step has a unique quotient endpoint, obtained in the source face or one
of its three neighboring charts. This is not built into the quotient relation. -/
namespace R002.GCPrimitiveSurface
open Icosahedron GCPrimitive
variable {k l : ℤ}

def OnFace (f : Face) (q : Lattice) (x : Vertex k l) : Prop :=
  ∃ u : Raw k l, u.1=f ∧ position u=q ∧ vertex u=x
def OnNeighbor (f : Face) (e : Corner) (q : Lattice) (x : Vertex k l) : Prop :=
  ∃ r : Point k l, opposite k l (frame k l (mate (f,e)).2 r.val)=frame k l e q ∧
    vertex ((mate (f,e)).1,.inr r)=x
def Landing (f : Face) (q : Lattice) (x : Vertex k l) : Prop :=
  OnFace f q x ∨ ∃ e : Corner, OnNeighbor f e q x

theorem onNeighbor_interior (f : Face) (e : Corner) (q : Lattice) (x : Vertex k l)
    (h : OnNeighbor f e q x) : Interior k l (opposite k l (frame k l e q)) := by
  obtain ⟨r,hr,_⟩ := h
  rw [← hr,opposite_involution]
  exact (interior_frame k l _ _).mpr r.property

theorem onFace_closed (hk : 0<k) (hl : 0≤l) (f : Face) (q : Lattice)
    (x : Vertex k l) (h : OnFace f q x) : Closed k l q := by
  obtain ⟨u,_,hp,_⟩ := h
  rw [← hp]
  exact position_closed hk hl u

theorem landing_exists (hk : 0<k) (hl : 0<l) (hprim : Primitive k l)
    (f : Face) (p q : Lattice) (hp : Interior k l p) (hu : Unit p q) :
    ∃ x : Vertex k l, Landing f q x := by
  rcases unit_step_covered k l hk hl p q hp hu with hq | ⟨e,he⟩
  · obtain ⟨u,hf,hp⟩ := closed_has_raw hk hl.le hprim f q hq
    exact ⟨vertex u,Or.inl ⟨u,hf,hp,rfl⟩⟩
  · let r : Point k l := ⟨unframe k l (mate (f,e)).2 (opposite k l (frame k l e q)),
      (interior_unframe k l _ _).mpr he⟩
    refine ⟨vertex ((mate (f,e)).1,.inr r),Or.inr ⟨e,r,?_,rfl⟩⟩
    simp [r,frame_unframe,opposite_involution]

theorem onNeighbor_unique (f : Face) (e : Corner) (q : Lattice) (x y : Vertex k l)
    (hx : OnNeighbor f e q x) (hy : OnNeighbor f e q y) : x=y := by
  obtain ⟨r,hr,rfl⟩ := hx
  obtain ⟨s,hs,rfl⟩ := hy
  have he := congrArg (opposite k l) (hr.trans hs.symm)
  simp only [opposite_involution] at he
  have hp : r=s := Subtype.ext (frame_injective k l _ he)
  rw [hp]

theorem landing_unique (hk : 0<k) (hl : 0<l)
    (f : Face) (q : Lattice) (x y : Vertex k l)
    (hx : Landing f q x) (hy : Landing f q y) : x=y := by
  rcases hx with hx | ⟨e,hx⟩ <;> rcases hy with hy | ⟨d,hy⟩
  · obtain ⟨u,huf,hup,rfl⟩ := hx
    obtain ⟨v,hvf,hvp,rfl⟩ := hy
    exact congrArg vertex (position_injective_in_face hk hl u v (huf.trans hvf.symm) (hup.trans hvp.symm))
  · exact False.elim (neighbor_not_closed k l q d (onNeighbor_interior f d q y hy)
      (onFace_closed hk hl.le f q x hx))
  · exact False.elim (neighbor_not_closed k l q e (onNeighbor_interior f e q x hx)
      (onFace_closed hk hl.le f q y hy))
  · have hed := adjacent_chart_unique k l q e d
      (onNeighbor_interior f e q x hx) (onNeighbor_interior f d q y hy)
    subst d
    exact onNeighbor_unique f e q x y hx hy

theorem unit_step_unique_lift (hk : 0<k) (hl : 0<l) (hprim : Primitive k l)
    (f : Face) (p q : Lattice) (hp : Interior k l p) (hu : Unit p q) :
    ∃! x : Vertex k l, Landing f q x := by
  obtain ⟨x,hx⟩ := landing_exists hk hl hprim f p q hp hu
  exact ⟨x,hx,fun y hy => landing_unique hk hl f q y x hy hx⟩

end R002.GCPrimitiveSurface
