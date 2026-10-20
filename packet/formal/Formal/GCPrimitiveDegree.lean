import Formal.GCPrimitiveSurfaceCorners
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Degrees are derived from the graph's neighbor sets, not assigned labels. -/
namespace R002.GCPrimitiveSurface
open Icosahedron GCPrimitive
variable {k l : ℤ}

theorem neighborFace_injective : ∀ f : Face,
    Function.Injective (fun e : Corner => (mate (f,e)).1) := by decide +kernel

theorem direction_injective : Function.Injective direction := by decide +kernel

/-- A quotient vertex cannot represent two distinct positions in this star chart. -/
theorem landing_position_injective (f : Face) (p q : Lattice) (x : Vertex k l)
    (hp : Landing f p x) (hq : Landing f q x) : p=q := by
  rcases hp with ⟨u,huf,hup,hux⟩ | ⟨e,r,hr,hrx⟩ <;>
    rcases hq with ⟨v,hvf,hvp,hvx⟩ | ⟨d,s,hs,hsx⟩
  · have huv := same_face_vertex_injective u v (huf.trans hvf.symm) (hux.trans hvx.symm)
    exact hup.symm.trans ((congrArg position huv).trans hvp)
  · have hc : canonical u=Sum.inr ((mate (f,d)).1,s) := congrArg toCanonical (hux.trans hsx.symm)
    have he := interior_raw_unique u _ s hc
    have hf : (mate (f,d)).1=f := (congrArg Prod.fst he).symm.trans huf
    exact False.elim (mate_other_face (f,d) hf)
  · have hc : canonical v=Sum.inr ((mate (f,e)).1,r) := congrArg toCanonical (hvx.trans hrx.symm)
    have he := interior_raw_unique v _ r hc
    have hf : (mate (f,e)).1=f := (congrArg Prod.fst he).symm.trans hvf
    exact False.elim (mate_other_face (f,e) hf)
  · have hc : ((mate (f,e)).1,r)=((mate (f,d)).1,s) :=
      Sum.inr.inj (congrArg toCanonical (hrx.trans hsx.symm))
    have hf : (mate (f,e)).1=(mate (f,d)).1 := congrArg (fun z : Face × Point k l => z.1) hc
    have hed := neighborFace_injective f hf
    subst d
    have hrs : r=s := congrArg Prod.snd hc
    subst s
    exact frame_injective k l e (hr.symm.trans hs)

noncomputable def stepNeighbor (hk : 0<k) (hl : 0<l) (hprim : Primitive k l)
    (f : Face) (p : Point k l) (i : Fin 6) :
    (graph k l).neighborSet (vertex (f,.inr p)) :=
  ⟨Classical.choose (six_steps_total hk hl hprim f p i),
    (Classical.choose_spec (six_steps_total hk hl hprim f p i)).1.2⟩

theorem stepNeighbor_landing (hk : 0<k) (hl : 0<l) (hprim : Primitive k l)
    (f : Face) (p : Point k l) (i : Fin 6) :
    Landing f (p.val+direction i) (stepNeighbor hk hl hprim f p i).val :=
  (Classical.choose_spec (six_steps_total hk hl hprim f p i)).1.1

theorem stepNeighbor_bijective (hk : 0<k) (hl : 0<l) (hprim : Primitive k l)
    (f : Face) (p : Point k l) : Function.Bijective (stepNeighbor hk hl hprim f p) := by
  constructor
  · intro i j h
    have he := landing_position_injective f _ _ _ (stepNeighbor_landing hk hl hprim f p i)
      (show Landing f (p.val+direction j) (stepNeighbor hk hl hprim f p i).val by
        rw [h]; exact stepNeighbor_landing hk hl hprim f p j)
    exact direction_injective (add_left_cancel he)
  · intro y
    obtain ⟨i,hi⟩ := (ordinary_adjacency_iff_directions f p y.val).mp y.property
    refine ⟨i,Subtype.ext ?_⟩
    exact landing_unique hk hl f _ _ _ (stepNeighbor_landing hk hl hprim f p i) hi

noncomputable def ordinaryNeighborsEquiv (hk : 0<k) (hl : 0<l) (hprim : Primitive k l)
    (f : Face) (p : Point k l) : Fin 6 ≃ (graph k l).neighborSet (vertex (f,.inr p)) :=
  Equiv.ofBijective _ (stepNeighbor_bijective hk hl hprim f p)

theorem ordinary_neighbor_card (hk : 0<k) (hl : 0<l) (hprim : Primitive k l)
    (f : Face) (p : Point k l) : Nat.card ((graph k l).neighborSet (vertex (f,.inr p)))=6 := by
  rw [← Nat.card_congr (ordinaryNeighborsEquiv hk hl hprim f p)]
  simp

abbrev Incident (a : ParentVertex) := {d : Dart // faceVertex d.1 d.2=a}

noncomputable def parentNeighbor (hkl : l<k) (hl : 0<l) (d : Dart)
    (e : Incident (faceVertex d.1 d.2)) :
    (graph k l).neighborSet (vertex (d.1,.inl d.2)) :=
  ⟨vertex (e.val.1,.inr (fanPoint hkl hl e.val.2)),
    (parent_adjacency_iff_fans hkl hl d _).mpr ⟨e.val.1,e.val.2,e.property,rfl⟩⟩

theorem parentNeighbor_bijective (hkl : l<k) (hl : 0<l) (d : Dart) :
    Function.Bijective (parentNeighbor hkl hl d) := by
  constructor
  · intro e b h
    have hc : (e.val.1,fanPoint hkl hl e.val.2)=(b.val.1,fanPoint hkl hl b.val.2) :=
      Sum.inr.inj (congrArg toCanonical (congrArg Subtype.val h))
    have hf : e.val.1=b.val.1 := congrArg (fun z : Face × Point k l => z.1) hc
    apply Subtype.ext
    apply Prod.ext hf
    apply faceVertex_injective e.val.1
    exact e.property.trans (by simpa only [← hf] using b.property.symm)
  · intro y
    obtain ⟨f,e,he,hy⟩ := (parent_adjacency_iff_fans hkl hl d y.val).mp y.property
    exact ⟨⟨(f,e),he⟩,Subtype.ext hy.symm⟩

noncomputable def parentNeighborsEquiv (hkl : l<k) (hl : 0<l) (d : Dart) :
    Incident (faceVertex d.1 d.2) ≃ (graph k l).neighborSet (vertex (d.1,.inl d.2)) :=
  Equiv.ofBijective _ (parentNeighbor_bijective hkl hl d)

theorem incident_card (a : ParentVertex) : Nat.card (Incident a)=5 := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  exact five_corners a

theorem parent_neighbor_card (hkl : l<k) (hl : 0<l) (d : Dart) :
    Nat.card ((graph k l).neighborSet (vertex (d.1,.inl d.2)))=5 := by
  rw [← Nat.card_congr (parentNeighborsEquiv hkl hl d)]
  exact incident_card _

theorem all_neighbor_card (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (x : Vertex k l) : Nat.card ((graph k l).neighborSet x)=
      match toCanonical x with | .inl _ => 5 | .inr _ => 6 := by
  refine Quotient.inductionOn x ?_
  rintro ⟨f,e|p⟩
  · exact parent_neighbor_card hkl hl (f,e)
  · exact ordinary_neighbor_card (by omega) hl hprim f p

noncomputable def locallyFinite (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) :
    (graph k l).LocallyFinite := by
  intro x
  haveI : Finite ((graph k l).neighborSet x) := Nat.finite_of_card_ne_zero (by
    rw [all_neighbor_card hkl hl hprim]
    cases toCanonical x <;> simp)
  exact Fintype.ofFinite _

theorem graph_degree (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (x : Vertex k l) :
    letI := locallyFinite hkl hl hprim
    (graph k l).degree x=match toCanonical x with | .inl _ => 5 | .inr _ => 6 := by
  letI := locallyFinite hkl hl hprim
  rw [← SimpleGraph.ncard_neighborSet]
  exact all_neighbor_card hkl hl hprim x

end R002.GCPrimitiveSurface
