import Formal.GCPrimitiveSurfaceEdges

namespace R002.GCPrimitive
open Icosahedron (Corner)

theorem frame_corner (k l : ℤ) (e : Corner) : frame k l e (corner k l e)=(0,0) := by
  fin_cases e <;> ext <;> simp [frame,corner,turn,A,B] <;> ring

theorem closed_corner_fan (k l : ℤ) (hkl : l<k) (hl : 0<l)
    (e : Corner) (q : Lattice) :
    Closed k l q ∧ Unit (corner k l e) q ↔ q=unframe k l e (0,1) := by
  constructor
  · rintro ⟨hq,hu⟩
    have hf := (frame_unit k l e _ _).mpr hu
    rw [frame_corner] at hf
    have he := (closed_origin_fan k l hkl hl _).mp ⟨(closed_frame k l e q).mpr hq,hf⟩
    have hh := congrArg (unframe k l e) he
    simpa only [unframe_frame] using hh
  · rintro rfl
    have hin := (interior_unframe k l e _).mpr (origin_winner k l hkl hl).1
    refine ⟨interior_closed k l _ hin,?_⟩
    apply (frame_unit k l e _ _).mp
    rw [frame_corner,frame_unframe]
    exact (origin_winner k l hkl hl).2

/-- No lattice vertex, hence no parent cone point, lies strictly inside a unit edge.
The statement uses homogeneous integer coordinates, without real-number geometry. -/
theorem no_internal_lattice_point (p q z : Lattice) (hu : Unit p q)
    (w m : ℤ) (hm : 0<m) (hmw : m<w)
    (hx : w*z.1=(w-m)*p.1+m*q.1) (hy : w*z.2=(w-m)*p.2+m*q.2) : False := by
  have hw : 0<w := by omega
  obtain ⟨i,rfl⟩ := hu
  fin_cases i <;> simp [direction] at hx hy
  all_goals first
    | exact no_positive_strip w (z.1-p.1) hw (by nlinarith) (by nlinarith)
    | exact no_positive_strip w (p.1-z.1) hw (by nlinarith) (by nlinarith)
    | exact no_positive_strip w (z.2-p.2) hw (by nlinarith) (by nlinarith)
    | exact no_positive_strip w (p.2-z.2) hw (by nlinarith) (by nlinarith)

end R002.GCPrimitive

namespace R002.GCPrimitiveSurface
open Icosahedron GCPrimitive
variable {k l : ℤ}

def fanPoint (hkl : l<k) (hl : 0<l) (e : Corner) : Point k l :=
  ⟨unframe k l e (0,1),(interior_unframe k l e _).mpr (origin_winner k l hkl hl).1⟩

theorem unit_from_corner (hkl : l<k) (hl : 0<l) (f : Face) (e : Corner)
    (v : Raw k l) (hf : v.1=f) (hu : Unit (corner k l e) (position v)) :
    v=(f,.inr (fanPoint hkl hl e)) := by
  have hc := position_closed (show 0<k by omega) hl.le v
  have hp := (closed_corner_fan k l hkl hl e _).mp ⟨hc,hu⟩
  have hpos : position v=position (f,.inr (fanPoint hkl hl e)) := hp
  exact position_injective_in_face (by omega) hl v _ hf hpos

theorem corner_no_across (f : Face) (e : Corner) (v : Raw k l) : ¬Across (f,.inl e) v := by
  rintro ⟨d,p,q,h,_,_⟩
  have hs : Sum.inl e=Sum.inr p := congrArg Prod.snd h
  cases hs

/-- All edges at a parent vertex come from its incident face fans.
The parent table independently proves there are exactly five incident corners. -/
theorem parent_adjacency_iff_fans (hkl : l<k) (hl : 0<l) (d : Dart) (y : Vertex k l) :
    (graph k l).Adj (vertex (d.1,.inl d.2)) y ↔
      ∃ (f : Face) (e : Corner), faceVertex f e=faceVertex d.1 d.2 ∧
        y=vertex (f,.inr (fanPoint hkl hl e)) := by
  constructor
  · rintro ⟨_,u,v,hu,hv,he⟩
    have hc := congrArg toCanonical hu
    rcases u with ⟨f,e|p⟩
    · have hp : faceVertex f e=faceVertex d.1 d.2 := Sum.inl.inj hc
      have hunit : f=v.1 ∧ Unit (corner k l e) (position v) := by
        rcases he with he | he | he
        · exact he
        · exact False.elim (corner_no_across f e v he)
        · exact False.elim (corner_no_across f e v (across_symm _ _ he))
      have heq := unit_from_corner hkl hl f e v hunit.1.symm hunit.2
      exact ⟨f,e,hp,hv.symm.trans (congrArg vertex heq)⟩
    · simp [toCanonical,vertex,canonical] at hc
  · rintro ⟨f,e,hp,rfl⟩
    have heq : vertex (k:=k) (l:=l) (f,.inl e)=vertex (d.1,.inl d.2) :=
      toCanonical_injective (congrArg Sum.inl hp)
    rw [← heq]
    apply rawEdge_adj
    refine Or.inl ⟨rfl,?_⟩
    exact ((closed_corner_fan k l hkl hl e _).mpr rfl).2

end R002.GCPrimitiveSurface
