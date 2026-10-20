import Formal.IcosahedronRotations
import Formal.GCChallengeTransport

/-! The finite oriented parent rotations induce actual graph automorphisms.
No classification or absence premise is used. -/
namespace R002.GCPrimitive
open Icosahedron

theorem unframe_add (k l : ℤ) (e d : Corner) (p : Lattice) :
    unframe k l e (unframe k l d p)=unframe k l (d+e) p := by
  fin_cases e <;> fin_cases d <;> simp [unframe,turn_three]

theorem unframe_corner_add (k l : ℤ) (e d : Corner) :
    unframe k l e (corner k l d)=corner k l (d+e) := by
  fin_cases e <;> fin_cases d <;> ext <;> simp [unframe,corner,turn,A,B] <;> ring

theorem frame_shift_cancel (k l : ℤ) (e d : Corner) (p : Lattice) :
    frame k l (d+e) (unframe k l e p)=frame k l d p := by
  fin_cases e <;> fin_cases d <;> simp [frame,unframe,turn_three]

theorem unframe_unit (k l : ℤ) (e : Corner) (p q : Lattice) :
    Unit (unframe k l e p) (unframe k l e q) ↔ Unit p q := by
  rw [← frame_unit k l e,frame_unframe,frame_unframe]

end R002.GCPrimitive

namespace R002.GCPrimitiveSurface
open Icosahedron GCPrimitive
variable {k l : ℤ}

def rotatePoint (r : Rotation) (f : Face) (p : Point k l) : Point k l :=
  ⟨unframe k l (rotationFaces r.1 r.2 f).2 p.val,
    (interior_unframe k l _ _).mpr p.property⟩

def rotateRaw (r : Rotation) (u : Raw k l) : Raw k l :=
  ((rotationFaces r.1 r.2 u.1).1, match u.2 with
    | .inl e => .inl (e+(rotationFaces r.1 r.2 u.1).2)
    | .inr p => .inr (rotatePoint r u.1 p))

@[simp] theorem rotateRaw_corner (r : Rotation) (d : Dart) :
    rotateRaw (k:=k) (l:=l) r (d.1,.inl d.2)=
      ((rotateDart r d).1,.inl (rotateDart r d).2) := rfl

theorem rotateRaw_position (r : Rotation) (u : Raw k l) :
    position (rotateRaw r u)=unframe k l (rotationFaces r.1 r.2 u.1).2 (position u) := by
  rcases u with ⟨f,e|p⟩
  · exact (unframe_corner_add k l _ e).symm
  · rfl

theorem rotateRaw_inverse (r : Rotation) (u : Raw k l) :
    rotateRaw (inverseRotation r) (rotateRaw r u)=u := by
  rcases u with ⟨f,e|p⟩
  · exact congrArg (fun d : Dart => ((d.1,Sum.inl d.2) : Raw k l)) (rotate_inverse r (f,e))
  · have hf := congrArg Prod.fst (rotate_inverse r (f,0))
    have he := congrArg Prod.snd (rotate_inverse r (f,0))
    change (rotationFaces (inverseRotation r).1 (inverseRotation r).2
      (rotationFaces r.1 r.2 f).1).1=f at hf
    change (0+(rotationFaces r.1 r.2 f).2)+
      (rotationFaces (inverseRotation r).1 (inverseRotation r).2 (rotationFaces r.1 r.2 f).1).2=0 at he
    apply Prod.ext hf
    apply congrArg Sum.inr
    apply Subtype.ext
    change unframe k l
      (rotationFaces (inverseRotation r).1 (inverseRotation r).2 (rotationFaces r.1 r.2 f).1).2
      (unframe k l (rotationFaces r.1 r.2 f).2 p.val)=p.val
    have he' : (rotationFaces r.1 r.2 f).2+
        (rotationFaces (inverseRotation r).1 (inverseRotation r).2 (rotationFaces r.1 r.2 f).1).2=0 := by
      simpa only [zero_add] using he
    rw [unframe_add,he']
    simp [unframe]

theorem rotateRaw_right_inverse (r : Rotation) (u : Raw k l) :
    rotateRaw r (rotateRaw (inverseRotation r) u)=u := by
  have hi : inverseRotation (inverseRotation r)=r := by
    apply rotation_distinct
    funext d
    have h := rotate_inverse (inverseRotation r) (rotateDart r d)
    simpa only [rotate_inverse] using h
  simpa only [hi] using rotateRaw_inverse (inverseRotation r) u

theorem rotateRaw_glue (r : Rotation) (u v : Raw k l) (h : Glue k l u v) :
    Glue k l (rotateRaw r u) (rotateRaw r v) := by
  obtain ⟨d,rfl,rfl⟩ := h
  refine ⟨rotateDart r d,rotateRaw_corner r d,?_⟩
  have h := rotate_next r (mate d)
  rw [rotate_mate] at h
  exact congrArg (fun d : Dart => ((d.1,Sum.inl d.2) : Raw k l)) h

theorem rotateRaw_respects (r : Rotation) (u v : Raw k l)
    (h : Relation.EqvGen (Glue k l) u v) :
    Relation.EqvGen (Glue k l) (rotateRaw r u) (rotateRaw r v) := by
  induction h with
  | rel u v h => exact .rel _ _ (rotateRaw_glue r u v h)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

def rotateVertex (r : Rotation) : Vertex k l → Vertex k l :=
  Quotient.map (rotateRaw r) (rotateRaw_respects r)
@[simp] theorem rotateVertex_vertex (r : Rotation) (u : Raw k l) :
    rotateVertex r (vertex u)=vertex (rotateRaw r u) := rfl

def rotationEquiv (r : Rotation) : Vertex k l ≃ Vertex k l where
  toFun := rotateVertex r
  invFun := rotateVertex (inverseRotation r)
  left_inv := by
    intro x; refine Quotient.inductionOn x ?_; intro u
    change vertex (rotateRaw (inverseRotation r) (rotateRaw r u))=vertex u
    rw [rotateRaw_inverse]
  right_inv := by
    intro x; refine Quotient.inductionOn x ?_; intro u
    change vertex (rotateRaw r (rotateRaw (inverseRotation r) u))=vertex u
    rw [rotateRaw_right_inverse]

theorem rotateRaw_across (r : Rotation) (u v : Raw k l) (h : Across u v) :
    Across (rotateRaw r u) (rotateRaw r v) := by
  obtain ⟨d,p,q,rfl,rfl,hu⟩ := h
  refine ⟨rotateDart r d,rotatePoint r d.1 p,rotatePoint r (mate d).1 q,rfl,?_,?_⟩
  · change (_,_) = ((mate (rotateDart r d)).1,_)
    rw [← rotate_mate]
    rfl
  · rw [← rotate_mate]
    change Unit (frame k l (d.2+_) (unframe k l _ p.val))
      (opposite k l (frame k l ((mate d).2+_) (unframe k l _ q.val)))
    simpa only [frame_shift_cancel] using hu

theorem rotateRaw_edge (r : Rotation) (u v : Raw k l) (h : RawEdge u v) :
    RawEdge (rotateRaw r u) (rotateRaw r v) := by
  rcases h with ⟨hf,hu⟩ | h | h
  · refine Or.inl ⟨congrArg (fun f => (rotationFaces r.1 r.2 f).1) hf,?_⟩
    rw [rotateRaw_position,rotateRaw_position,← hf]
    exact (unframe_unit k l _ _ _).mpr hu
  · exact Or.inr (Or.inl (rotateRaw_across r u v h))
  · exact Or.inr (Or.inr (rotateRaw_across r v u h))

theorem rotateVertex_adj (r : Rotation) (x y : Vertex k l) (h : (graph k l).Adj x y) :
    (graph k l).Adj (rotateVertex r x) (rotateVertex r y) := by
  obtain ⟨hne,u,v,rfl,rfl,he⟩ := h
  exact rawEdge_adj _ _ (rotateRaw_edge r u v he)

def rotationGraphIso (r : Rotation) : graph k l ≃g graph k l where
  toEquiv := rotationEquiv r
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      have hh := rotateVertex_adj (inverseRotation r) _ _ h
      change (graph k l).Adj ((rotationEquiv r).symm ((rotationEquiv r) x))
        ((rotationEquiv r).symm ((rotationEquiv r) y)) at hh
      simpa only [Equiv.symm_apply_apply] using hh
    · exact rotateVertex_adj r x y

@[simp] theorem rotationGraphIso_apply (r : Rotation) (x : Vertex k l) :
    rotationGraphIso r x=rotateVertex r x := rfl

end R002.GCPrimitiveSurface
