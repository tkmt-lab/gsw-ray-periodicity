import Formal.GCChallengeVertexEquiv
import Formal.GCPrimitiveSeamEdges

namespace R002.GCChallengeBridge
open Icosahedron GCPrimitive GCPrimitiveSurface
variable {k l : ℤ}

theorem direction_mem : ∀ i : Fin 6, direction i ∈ ClaudeChallenge.unitVec := by decide +kernel

theorem mem_direction (u : Lattice) (hu : u∈ClaudeChallenge.unitVec) : ∃ i, direction i=u := by
  simp only [ClaudeChallenge.unitVec,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩
  · exact ⟨5,rfl⟩

theorem unit_list_iff (p q : Lattice) :
    (∃ u ∈ ClaudeChallenge.unitVec, q=p+u) ↔ GCPrimitive.Unit p q := by
  constructor
  · rintro ⟨u,hu,hq⟩; obtain ⟨i,rfl⟩ := mem_direction u hu; exact ⟨i,hq⟩
  · rintro ⟨i,hi⟩; exact ⟨direction i,direction_mem i,hi⟩

theorem posMap_unit (f : Face) (p q : Lattice) :
    GCPrimitive.Unit (posMap k l f p) (posMap k l f q) ↔ GCPrimitive.Unit p q := by
  have h := frame_unit k l (cornerMap f 0) (posMap k l f p) (posMap k l f q)
  rw [frame_posMap,frame_posMap] at h
  simpa [frame] using h.symm

theorem seam_glue (d : Dart) : ∃ j t,
    ClaudeChallenge.Glue k l (faceMap d.1) (faceMap (mate d).1) j t ∧ ∀ p,
      ClaudeChallenge.rotN j (posMap k l d.1 p)+t=
        posMap k l (mate d).1 (unframe k l (mate d).2 (opposite k l (frame k l d.2 p))) := by
  obtain ⟨j,t,hg,ht⟩ := aligned_glue (k:=k) (l:=l) (faceMap d.1) (faceMap (mate d).1)
    (cornerMap d.1 d.2) (cornerMap (mate d).1 (mate d).2)
    (fun h => mate_other_face d (faceMap_bijective.1 h).symm)
    (by rw [← cornerMap_add_one,labels_agree,labels_agree]; exact (mate_reverses d).2.symm)
    (by rw [← cornerMap_add_one,labels_agree,labels_agree]; exact (mate_reverses d).1.symm)
  exact ⟨j,t,hg,fun p => (ht _).trans (unfold_posMap _ _ _ _ p)⟩

theorem same_face_step (hk : 0<k) (hl : 0<l) (u v : Raw k l) (hf : u.1=v.1)
    (hu : GCPrimitive.Unit (position u) (position v)) :
    ClaudeChallenge.StepTo k l (rawSite hk hl u) (rawSite hk hl v) := by
  have hup := (posMap_unit (k:=k) (l:=l) u.1 _ _).mpr hu
  obtain ⟨s,hs,he⟩ := (unit_list_iff _ _).mpr hup
  refine ⟨s,hs,Or.inl ⟨congrArg faceMap hf.symm,?_⟩⟩
  change posMap k l v.1 (position v)=posMap k l u.1 (position u)+s
  rw [← hf]; exact he

theorem seam_step (hk : 0<k) (hl : 0<l) (d : Dart) (u v : Corner ⊕ Point k l)
    (hu : GCPrimitive.Unit (frame k l d.2 (position (d.1,u)))
      (opposite k l (frame k l (mate d).2 (position ((mate d).1,v))))) :
    ClaudeChallenge.StepTo k l (rawSite hk hl (d.1,u)) (rawSite hk hl ((mate d).1,v)) := by
  let q := unframe k l d.2 (opposite k l (frame k l (mate d).2 (position ((mate d).1,v))))
  have hq : GCPrimitive.Unit (position (d.1,u)) q := by
    apply (frame_unit k l d.2 _ _).mp
    simpa only [q,frame_unframe] using hu
  obtain ⟨s,hs,he⟩ := (unit_list_iff _ _).mpr ((posMap_unit (k:=k) (l:=l) d.1 _ _).mpr hq)
  obtain ⟨j,t,hg,ht⟩ := seam_glue (k:=k) (l:=l) (mate d)
  rw [mate_involutive] at hg ht
  refine ⟨s,hs,Or.inr ⟨j,t,hg,?_⟩⟩
  change ClaudeChallenge.rotN j (posMap k l (mate d).1 (position ((mate d).1,v)))+t=
    posMap k l d.1 (position (d.1,u))+s
  exact (ht _).trans he

/-- Reflection includes corners and all rotations admitted by the independent StepTo. -/
theorem step_reflects (hkl : l<k) (hl : 0<l) (u v : Raw k l)
    (h : ClaudeChallenge.StepTo k l (rawSite (by omega) hl u) (rawSite (by omega) hl v)) :
    (graph k l).Adj (vertex u) (vertex v) := by
  rcases u with ⟨f,u⟩; rcases v with ⟨g,v⟩
  obtain ⟨s,hs,h⟩ := h
  rcases h with ⟨hf,hp⟩ | ⟨j,t,hg,hp⟩
  · have hf' : g=f := faceMap_bijective.1 hf
    subst g
    apply (same_face_adj_iff_unit hkl hl (f,u) (f,v) rfl).mpr
    apply (posMap_unit (k:=k) (l:=l) f _ _).mp
    exact (unit_list_iff _ _).mp ⟨s,hs,hp⟩
  · obtain ⟨e,hf,hmap⟩ := glue_normal (by omega) hl g f j t hg
    subst f
    change ClaudeChallenge.rotN j (posMap k l g (position (g,v)))+t=
      posMap k l (mate (g,e)).1 (position ((mate (g,e)).1,u))+s at hp
    rw [hmap] at hp
    have hu := (posMap_unit (k:=k) (l:=l) (mate (g,e)).1 _ _).mp ((unit_list_iff _ _).mp ⟨s,hs,hp⟩)
    have hu' := (frame_unit k l (mate (g,e)).2 _ _).mpr hu
    rw [frame_unframe] at hu'
    exact ((seam_adj_iff_unit hkl hl (g,e) v u).mpr (unit_seam_swap _ _ hu')).symm

theorem rawEdge_steps (hk : 0<k) (hl : 0<l) (u v : Raw k l) (h : RawEdge u v) :
    ClaudeChallenge.StepTo k l (rawSite hk hl u) (rawSite hk hl v) ∨
    ClaudeChallenge.StepTo k l (rawSite hk hl v) (rawSite hk hl u) := by
  rcases h with ⟨hf,hu⟩ | ⟨d,p,q,rfl,rfl,hu⟩ | ⟨d,p,q,rfl,rfl,hu⟩
  · exact Or.inl (same_face_step hk hl u v hf hu)
  · exact Or.inl (seam_step hk hl d (.inr p) (.inr q) hu)
  · exact Or.inr (seam_step hk hl d (.inr p) (.inr q) hu)

end R002.GCChallengeBridge
