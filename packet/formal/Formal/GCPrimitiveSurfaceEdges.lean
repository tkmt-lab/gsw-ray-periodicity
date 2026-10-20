import Formal.GCPrimitiveLanding

namespace R002.GCPrimitiveSurface
open Icosahedron GCPrimitive
variable {k l : ℤ}

theorem unit_seam_swap (p q : Lattice) (h : Unit p (opposite k l q)) :
    Unit q (opposite k l p) := by
  have hh := unit_symm _ _ (unit_opposite k l _ _ h)
  simpa only [opposite_involution] using hh

theorem across_symm (u v : Raw k l) (h : Across u v) : Across v u := by
  obtain ⟨d,p,q,rfl,rfl,h⟩ := h
  refine ⟨mate d,q,p,rfl,?_,?_⟩
  · rw [mate_involutive]
  · rw [mate_involutive]
    exact unit_seam_swap _ _ h

theorem rawEdge_symm (u v : Raw k l) (h : RawEdge u v) : RawEdge v u := by
  rcases h with ⟨hf,hu⟩ | h | h
  · exact Or.inl ⟨hf.symm,unit_symm _ _ hu⟩
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem across_ne (u v : Raw k l) (h : Across u v) : vertex u≠vertex v := by
  obtain ⟨d,p,q,rfl,rfl,_⟩ := h
  intro hv
  have hc := congrArg toCanonical hv
  have he : (d.1,p)=((mate d).1,q) := Sum.inr.inj hc
  have hf : d.1=(mate d).1 := congrArg (fun z : Face × Point k l => z.1) he
  exact mate_other_face d hf.symm

theorem rawEdge_ne (u v : Raw k l) (h : RawEdge u v) : vertex u≠vertex v := by
  rcases h with ⟨hf,hu⟩ | h | h
  · intro hv
    have he := same_face_vertex_injective u v hf hv
    exact unit_ne _ _ hu (congrArg position he)
  · exact across_ne u v h
  · exact (across_ne v u h).symm

def graph (k l : ℤ) : SimpleGraph (Vertex k l) where
  Adj := Adj
  symm := ⟨by
    rintro x y ⟨hne,u,v,hx,hy,h⟩
    exact ⟨hne.symm,v,u,hy,hx,rawEdge_symm u v h⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem rawEdge_adj (u v : Raw k l) (h : RawEdge u v) :
    (graph k l).Adj (vertex u) (vertex v) := ⟨rawEdge_ne u v h,u,v,rfl,rfl,h⟩

theorem landing_is_edge (f : Face) (p : Point k l) (q : Lattice) (x : Vertex k l)
    (hu : Unit p.val q) (hx : Landing f q x) :
    (graph k l).Adj (vertex (f,.inr p)) x := by
  rcases hx with ⟨u,hf,hp,rfl⟩ | ⟨e,r,hr,rfl⟩
  · apply rawEdge_adj
    refine Or.inl ⟨hf.symm,?_⟩
    change Unit p.val (position u)
    rw [hp]
    exact hu
  · apply rawEdge_adj
    refine Or.inr (Or.inl ⟨(f,e),p,r,rfl,rfl,?_⟩)
    rw [hr]
    exact (frame_unit k l e _ _).mpr hu

theorem across_to_step (f : Face) (p : Point k l) (v : Raw k l)
    (h : Across (f,.inr p) v) :
    ∃ i : Fin 6, Landing f (p.val+direction i) (vertex v) := by
  obtain ⟨d,a,r,ha,rfl,hu⟩ := h
  have hf : f=d.1 := congrArg Prod.fst ha
  have hp : p=a := Sum.inr.inj (congrArg Prod.snd ha)
  subst f; subst a
  let q := unframe k l d.2 (opposite k l (frame k l (mate d).2 r.val))
  have hq : Unit p.val q := by
    apply (frame_unit k l d.2 _ _).mp
    simpa only [q,frame_unframe] using hu
  obtain ⟨i,hi⟩ := hq
  refine ⟨i,Or.inr ⟨d.2,r,?_,rfl⟩⟩
  rw [← hi]
  exact (frame_unframe k l d.2 _).symm

/-- All graph neighbors of an ordinary vertex arise from one of its six steps;
conversely every landing of one of those steps is a graph edge. -/
theorem ordinary_adjacency_iff_directions (f : Face) (p : Point k l) (y : Vertex k l) :
    (graph k l).Adj (vertex (f,.inr p)) y ↔
      ∃ i : Fin 6, Landing f (p.val+direction i) y := by
  constructor
  · rintro ⟨_,u,v,hu,hv,he⟩
    have hc : canonical u=Sum.inr (f,p) := congrArg toCanonical hu
    have heq := interior_raw_unique u f p hc
    subst u
    rcases he with ⟨hf,hstep⟩ | hac | hac
    · obtain ⟨i,hi⟩ := hstep
      exact ⟨i,Or.inl ⟨v,hf.symm,hi,hv⟩⟩
    · obtain ⟨i,hi⟩ := across_to_step f p v hac
      exact ⟨i,hv ▸ hi⟩
    · obtain ⟨i,hi⟩ := across_to_step f p v (across_symm _ _ hac)
      exact ⟨i,hv ▸ hi⟩
  · rintro ⟨i,hi⟩
    exact landing_is_edge f p _ y ⟨i,rfl⟩ hi

theorem six_steps_total (hk : 0<k) (hl : 0<l) (hprim : Primitive k l)
    (f : Face) (p : Point k l) (i : Fin 6) :
    ∃! y : Vertex k l, Landing f (p.val+direction i) y ∧
      (graph k l).Adj (vertex (f,.inr p)) y := by
  obtain ⟨y,hy,unique⟩ := unit_step_unique_lift hk hl hprim f p.val _ p.property ⟨i,rfl⟩
  exact ⟨y,⟨hy,landing_is_edge f p _ y ⟨i,rfl⟩ hy⟩,fun z hz => unique z hz.1⟩

/-- The finite cut table characterizes every across-face generator. -/
theorem across_iff_cut (hk : 0<k) (hl : 0<l) (u v : Raw k l) :
    Across u v ↔ ∃ (d : Dart) (p q : Point k l) (r : Fin 3),
      u=(d.1,.inr p) ∧ v=((mate d).1,.inr q) ∧
      opposite k l (frame k l (mate d).2 q.val)=
        frame k l d.2 p.val+direction (exitDirection r) ∧ Cut k l (frame k l d.2 p.val) r := by
  constructor
  · rintro ⟨d,p,q,hu,hv,hstep⟩
    have hs : SeamEdge k l (frame k l d.2 p.val)
        (opposite k l (frame k l (mate d).2 q.val)) :=
      ⟨(interior_frame k l _ _).mpr p.property,by
        rw [opposite_involution]; exact (interior_frame k l _ _).mpr q.property,hstep⟩
    obtain ⟨r,hr,hcut⟩ := (seam_iff_certificate k l hk hl _ _).mp hs
    exact ⟨d,p,q,r,hu,hv,hr,hcut⟩
  · rintro ⟨d,p,q,r,hu,hv,hr,hcut⟩
    refine ⟨d,p,q,hu,hv,?_⟩
    rw [hr]
    exact ⟨exitDirection r,rfl⟩

end R002.GCPrimitiveSurface
