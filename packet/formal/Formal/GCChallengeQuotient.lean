import Formal.GCChallengeSites
import Formal.GCPrimitiveChartEdges

namespace R002.GCChallengeBridge
open Icosahedron GCPrimitive GCPrimitiveSurface
variable {k l : ℤ}

theorem challenge_corner_eq (e : Corner) : ClaudeChallenge.corner k l e=corner k l e := rfl

theorem challenge_face_injective : ∀ f, Function.Injective (ClaudeChallenge.face f) := by decide +kernel

def cornerSite (hk : 0<k) (hl : 0<l) (f : Fin 20) (e : Fin 3) : ClaudeChallenge.Site k l :=
  ⟨(f,ClaudeChallenge.corner k l e),(inTri_iff_closed _).mpr (corner_closed k l hk hl.le e)⟩

theorem unfold_corner_start (e m : Corner) :
    unframe k l m (opposite k l (frame k l e (corner k l e)))=corner k l (m+1) := by
  rw [frame_corner]
  have ho : opposite k l (0,0)=A k l := by ext <;> simp [opposite,A]
  rw [ho,← frame_next_corner k l m,unframe_frame]

theorem unfold_corner_end (e m : Corner) :
    unframe k l m (opposite k l (frame k l e (corner k l (e+1))))=corner k l m := by
  rw [frame_next_corner]
  have ho : opposite k l (A k l)=(0,0) := by ext <;> simp [opposite,A]
  rw [ho,← frame_corner k l m,unframe_frame]

/-- An actual rotation/translation witness for the challenge's edge identification. -/
theorem aligned_glue (f g : Fin 20) (e m : Fin 3) (hfg : f≠g)
    (h0 : ClaudeChallenge.face f e=ClaudeChallenge.face g (m+1))
    (h1 : ClaudeChallenge.face f (e+1)=ClaudeChallenge.face g m) :
    ∃ j t, ClaudeChallenge.Glue k l f g j t ∧
      ∀ p, ClaudeChallenge.rotN j p+t=unframe k l m (opposite k l (frame k l e p)) := by
  obtain ⟨j,t,ht⟩ := affine_unfold (k:=k) (l:=l) e m
  refine ⟨j,t,?_,ht⟩
  have hne : e≠e+1 := by fin_cases e <;> decide
  refine ⟨hfg,ClaudeChallenge.face f e,ClaudeChallenge.face f (e+1),
    fun h => hne (challenge_face_injective f h),
    ClaudeChallenge.corner k l e,ClaudeChallenge.corner k l (e+1),
    ClaudeChallenge.corner k l (m+1),ClaudeChallenge.corner k l m,
    ⟨e,rfl,rfl⟩,⟨e+1,rfl,rfl⟩,⟨m+1,h0.symm,rfl⟩,⟨m,h1.symm,rfl⟩,?_,?_⟩
  · rw [ht,challenge_corner_eq,unfold_corner_start,challenge_corner_eq]
  · rw [ht,challenge_corner_eq,unfold_corner_end,challenge_corner_eq]

theorem samePoint_corners (hk : 0<k) (hl : 0<l) (f g : Fin 20) (e m : Fin 3)
    (hfg : f≠g) (h0 : ClaudeChallenge.face f e=ClaudeChallenge.face g (m+1))
    (h1 : ClaudeChallenge.face f (e+1)=ClaudeChallenge.face g m) :
    ClaudeChallenge.SamePoint k l (cornerSite hk hl f e) (cornerSite hk hl g (m+1)) := by
  obtain ⟨j,t,hg,ht⟩ := aligned_glue (k:=k) (l:=l) f g e m hfg h0 h1
  refine ⟨j,t,hg,?_⟩
  change ClaudeChallenge.rotN j (ClaudeChallenge.corner k l e)+t=ClaudeChallenge.corner k l (m+1)
  rw [ht,challenge_corner_eq,unfold_corner_start,challenge_corner_eq]

theorem rawSite_corner (hk : 0<k) (hl : 0<l) (f : Face) (e : Corner) :
    rawSite hk hl (f,.inl e)=cornerSite hk hl (faceMap f) (cornerMap f e) := by
  exact Subtype.ext (Prod.ext rfl (corners_agree f e))

theorem glue_to_samePoint (hk : 0<k) (hl : 0<l) (u v : Raw k l) (h : GCPrimitiveSurface.Glue k l u v) :
    ClaudeChallenge.SamePoint k l (rawSite hk hl u) (rawSite hk hl v) := by
  obtain ⟨d,rfl,rfl⟩ := h
  rw [rawSite_corner,rawSite_corner,cornerMap_add_one]
  apply samePoint_corners
  · exact fun h => mate_other_face d (faceMap_bijective.1 h).symm
  · rw [← cornerMap_add_one,labels_agree,labels_agree]
    exact (mate_reverses d).2.symm
  · rw [← cornerMap_add_one,labels_agree,labels_agree]
    exact (mate_reverses d).1.symm

theorem vtx_respects (hk : 0<k) (hl : 0<l) (u v : Raw k l)
    (h : Relation.EqvGen (GCPrimitiveSurface.Glue k l) u v) :
    ClaudeChallenge.vtx (rawSite hk hl u)=ClaudeChallenge.vtx (rawSite hk hl v) := by
  induction h with
  | rel a b hab => exact Quot.sound (.rel _ _ (glue_to_samePoint hk hl a b hab))
  | refl => rfl
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

def toChallenge (hk : 0<k) (hl : 0<l) : GCPrimitiveSurface.Vertex k l → ClaudeChallenge.Vertex k l :=
  Quotient.lift (fun u => ClaudeChallenge.vtx (rawSite hk hl u)) (vtx_respects hk hl)

@[simp] theorem toChallenge_vertex (hk : 0<k) (hl : 0<l) (u : Raw k l) :
    toChallenge hk hl (vertex u)=ClaudeChallenge.vtx (rawSite hk hl u) := rfl

/-- A genuine quotient-level map onto all challenge vertices. Injectivity and graph
reflection require the reverse characterization of the challenge's Glue, not assumed here. -/
theorem toChallenge_surjective (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) :
    Function.Surjective (toChallenge hk hl) := by
  intro v
  refine Quot.inductionOn v ?_
  intro s
  obtain ⟨u,hu⟩ := rawSite_surjective hk hl hprim s
  exact ⟨vertex u,congrArg ClaudeChallenge.vtx hu⟩

end R002.GCChallengeBridge
