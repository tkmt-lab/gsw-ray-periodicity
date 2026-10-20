import Formal.GCPrimitiveCharts

/-! Exact quotient classes: twelve parent vertices and face-labelled interiors. -/
namespace R002.GCPrimitiveSurface
open Icosahedron GCPrimitive
variable {k l : ℤ}

theorem canonical_glue (u v : Raw k l) (h : Glue k l u v) : canonical u=canonical v := by
  obtain ⟨d,rfl,rfl⟩ := h
  exact congrArg Sum.inl (mate_reverses d).2.symm

theorem canonical_respects (u v : Raw k l)
    (h : Relation.EqvGen (Glue k l) u v) : canonical u=canonical v := by
  induction h with
  | rel x y h => exact canonical_glue x y h
  | refl => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

def toCanonical : Vertex k l → Canonical k l := Quotient.lift canonical canonical_respects
@[simp] theorem toCanonical_vertex (u : Raw k l) : toCanonical (vertex u)=canonical u := rfl

theorem corner_turns (d : Dart) (m : ℕ) :
    Relation.EqvGen (Glue k l) (d.1,.inl d.2)
      (((Icosahedron.turn^[m]) d).1,.inl ((Icosahedron.turn^[m]) d).2) := by
  induction m with
  | zero => exact .refl _
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact .trans _ _ _ ih (.rel _ _ ⟨(Icosahedron.turn^[m]) d,rfl,rfl⟩)

theorem canonical_exact (u v : Raw k l) (h : canonical u=canonical v) :
    Relation.EqvGen (Glue k l) u v := by
  rcases u with ⟨f,e|p⟩ <;> rcases v with ⟨g,d|q⟩
  · have he : faceVertex f e=faceVertex g d := Sum.inl.inj h
    obtain ⟨i,hi⟩ := turn_covers_vertex (f,e) (g,d) he
    have hh := corner_turns (k:=k) (l:=l) (f,e) i.val
    simpa only [hi] using hh
  · simp [canonical] at h
  · simp [canonical] at h
  · have he := Sum.inr.inj h
    have hf : f=g := congrArg Prod.fst he
    have hp : p=q := congrArg Prod.snd he
    subst g; subst q
    exact .refl _

theorem toCanonical_injective : Function.Injective (@toCanonical k l) := by
  intro u v
  refine Quotient.inductionOn₂ u v ?_
  intro a b h
  exact Quotient.sound (canonical_exact a b h)

theorem parent_representative : ∀ a : ParentVertex, ∃ d : Dart, faceVertex d.1 d.2=a := by
  decide +kernel

theorem toCanonical_surjective : Function.Surjective (@toCanonical k l) := by
  intro v
  cases v with
  | inl a =>
    obtain ⟨d,hd⟩ := parent_representative a
    exact ⟨vertex (d.1,.inl d.2),congrArg Sum.inl hd⟩
  | inr v => exact ⟨vertex (v.1,.inr v.2),rfl⟩

noncomputable def vertexEquiv (k l : ℤ) : Vertex k l ≃ Canonical k l :=
  Equiv.ofBijective toCanonical ⟨toCanonical_injective,toCanonical_surjective⟩

theorem position_closed (hk : 0<k) (hl : 0≤l) (u : Raw k l) : Closed k l (position u) := by
  rcases u with ⟨f,e|p⟩
  · exact corner_closed k l hk hl e
  · exact interior_closed k l _ p.property

/-- Primitive sides ensure the specification has omitted no closed-face lattice point. -/
theorem closed_has_raw (hk : 0<k) (hl : 0≤l) (hprim : Primitive k l)
    (f : Face) (q : Lattice) (hq : Closed k l q) :
    ∃ u : Raw k l, u.1=f ∧ position u=q := by
  rcases closed_partition k l hk hl hprim q hq with h | h | h | h
  · exact ⟨(f,.inl 0),rfl,h.symm⟩
  · exact ⟨(f,.inl 1),rfl,h.symm⟩
  · exact ⟨(f,.inl 2),rfl,h.symm⟩
  · exact ⟨(f,.inr ⟨q,h⟩),rfl,rfl⟩

theorem position_injective_in_face (hk : 0<k) (hl : 0<l)
    (u v : Raw k l) (hf : u.1=v.1) (hp : position u=position v) : u=v := by
  rcases u with ⟨f,e|p⟩ <;> rcases v with ⟨g,d|q⟩
  · have he := corner_injective k l hk hl hp
    exact Prod.ext hf (congrArg Sum.inl he)
  · change corner k l e=q.val at hp
    exact False.elim (corner_not_interior k l e (hp.symm ▸ q.property))
  · change p.val=corner k l d at hp
    exact False.elim (corner_not_interior k l d (hp ▸ p.property))
  · exact Prod.ext hf (congrArg Sum.inr (Subtype.ext hp))

theorem interior_raw_unique (u : Raw k l) (f : Face) (p : Point k l)
    (h : canonical u=Sum.inr (f,p)) : u=(f,.inr p) := by
  rcases u with ⟨g,e|q⟩
  · simp [canonical] at h
  · have hh := Sum.inr.inj h
    have hf : g=f := congrArg Prod.fst hh
    have hp : q=p := congrArg Prod.snd hh
    exact Prod.ext hf (congrArg Sum.inr hp)

theorem same_face_vertex_injective (u v : Raw k l) (hf : u.1=v.1)
    (hv : vertex u=vertex v) : u=v := by
  have h : canonical u=canonical v := congrArg toCanonical hv
  rcases u with ⟨f,e|p⟩ <;> rcases v with ⟨g,d|q⟩
  · change f=g at hf
    subst g
    have hd := (faceVertex_injective f) (Sum.inl.inj h)
    subst d; rfl
  · simp [canonical] at h
  · simp [canonical] at h
  · have hh := Sum.inr.inj h
    have hf' : f=g := congrArg Prod.fst hh
    have hp : p=q := congrArg Prod.snd hh
    exact Prod.ext hf' (congrArg Sum.inr hp)

end R002.GCPrimitiveSurface
