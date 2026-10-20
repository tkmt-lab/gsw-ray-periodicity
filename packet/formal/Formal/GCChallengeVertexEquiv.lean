import Formal.GCChallengeGlueNormal

namespace R002.GCChallengeBridge
open Icosahedron GCPrimitive GCPrimitiveSurface
variable {k l : ℤ}

/-- The overlap of closed neighboring charts consists only of the two primitive corners. -/
theorem seam_equal_vertices (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) (d : Dart)
    (u v : Corner ⊕ Point k l)
    (h : unframe k l (mate d).2 (opposite k l (frame k l d.2 (position (d.1,u))))=
      position ((mate d).1,v)) : vertex (d.1,u)=vertex ((mate d).1,v) := by
  have hp := (closed_frame k l d.2 _).mpr (position_closed hk hl.le (d.1,u))
  have hq := (closed_frame k l (mate d).2 _).mpr (position_closed hk hl.le ((mate d).1,v))
  have he : opposite k l (frame k l d.2 (position (d.1,u)))=
      frame k l (mate d).2 (position ((mate d).1,v)) := by
    simpa only [frame_unframe] using congrArg (frame k l (mate d).2) h
  have hb := hq.2.1
  rw [← he,(opposite_slices k l _).2.1] at hb
  have hb0 := hp.2.1
  have hz : b k l (frame k l d.2 (position (d.1,u)))=0 := by omega
  rcases primitive_OA k l hk hl.le hprim _ hp hz with h0 | h1
  · have hp0 : position (d.1,u)=corner k l d.2 := by
      apply frame_injective k l d.2; rw [frame_corner,h0]
    have hq0 : position ((mate d).1,v)=corner k l ((mate d).2+1) := by
      rw [hp0,unfold_corner_start] at h; exact h.symm
    have hu := position_injective_in_face hk hl (d.1,u) (d.1,.inl d.2) rfl hp0
    have hv := position_injective_in_face hk hl ((mate d).1,v) ((mate d).1,.inl ((mate d).2+1)) rfl hq0
    rw [hu,hv]
    exact Quotient.sound (.rel _ _ ⟨d,rfl,rfl⟩)
  · have hp1 : position (d.1,u)=corner k l (d.2+1) := by
      apply frame_injective k l d.2; rw [frame_next_corner,h1]
    have hq1 : position ((mate d).1,v)=corner k l (mate d).2 := by
      rw [hp1,unfold_corner_end] at h; exact h.symm
    have hu := position_injective_in_face hk hl (d.1,u) (d.1,.inl (d.2+1)) rfl hp1
    have hv := position_injective_in_face hk hl ((mate d).1,v) ((mate d).1,.inl (mate d).2) rfl hq1
    rw [hu,hv]
    apply toCanonical_injective
    exact congrArg Sum.inl (mate_reverses d).1.symm

theorem samePoint_vertex (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) (u v : Raw k l)
    (h : ClaudeChallenge.SamePoint k l (rawSite hk hl u) (rawSite hk hl v)) : vertex u=vertex v := by
  rcases u with ⟨f,u⟩; rcases v with ⟨g,v⟩
  obtain ⟨j,t,hg,hp⟩ := h
  obtain ⟨e,he,hmap⟩ := glue_normal hk hl f g j t hg
  subst g
  change ClaudeChallenge.rotN j (posMap k l f (position (f,u)))+t=
    posMap k l (mate (f,e)).1 (position ((mate (f,e)).1,v)) at hp
  rw [hmap] at hp
  exact seam_equal_vertices hk hl hprim (f,e) u v (posMap_injective _ hp)

noncomputable def fromChallenge (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) :
    ClaudeChallenge.Vertex k l → GCPrimitiveSurface.Vertex k l := by
  let E := siteEquiv hk hl hprim
  refine Quot.lift (fun s => vertex (E.symm s)) ?_
  intro s t h
  induction h with
  | rel a b hab =>
    apply samePoint_vertex hk hl hprim
    change ClaudeChallenge.SamePoint k l (E (E.symm a)) (E (E.symm b))
    simpa only [Equiv.apply_symm_apply] using hab
  | refl => rfl
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

theorem fromChallenge_toChallenge (hk : 0<k) (hl : 0<l) (hprim : Primitive k l)
    (v : GCPrimitiveSurface.Vertex k l) : fromChallenge hk hl hprim (toChallenge hk hl v)=v := by
  refine Quotient.inductionOn v ?_
  intro u
  change vertex ((siteEquiv hk hl hprim).symm ((siteEquiv hk hl hprim) u))=vertex u
  rw [Equiv.symm_apply_apply]

theorem toChallenge_injective (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) :
    Function.Injective (toChallenge hk hl) :=
  (show Function.LeftInverse (fromChallenge hk hl hprim) (toChallenge hk hl) from
    fromChallenge_toChallenge hk hl hprim).injective

noncomputable def challengeVertexEquiv (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) :
    GCPrimitiveSurface.Vertex k l ≃ ClaudeChallenge.Vertex k l :=
  Equiv.ofBijective (toChallenge hk hl) ⟨toChallenge_injective hk hl hprim,toChallenge_surjective hk hl hprim⟩

end R002.GCChallengeBridge
