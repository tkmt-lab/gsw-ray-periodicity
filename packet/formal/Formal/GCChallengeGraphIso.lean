import Formal.GCChallengeEdges

namespace R002.GCChallengeBridge
open Icosahedron GCPrimitive GCPrimitiveSurface
variable {k l : ℤ}

theorem adjRaw_reflects (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (v w : GCPrimitiveSurface.Vertex k l)
    (h : ClaudeChallenge.AdjRaw k l (toChallenge (by omega) hl v) (toChallenge (by omega) hl w)) :
    (graph k l).Adj v w := by
  obtain ⟨s,t,hs,ht,hstep⟩ := h
  obtain ⟨a,rfl⟩ := rawSite_surjective (by omega) hl hprim s
  obtain ⟨b,rfl⟩ := rawSite_surjective (by omega) hl hprim t
  have ha : vertex a=v := toChallenge_injective (by omega) hl hprim hs
  have hb : vertex b=w := toChallenge_injective (by omega) hl hprim ht
  rw [← ha,← hb]
  exact step_reflects hkl hl a b hstep

/-- Exact adjacency equivalence for the actual quotient map, not just finite tests. -/
theorem toChallenge_adj_iff (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (v w : GCPrimitiveSurface.Vertex k l) :
    (ClaudeChallenge.gcGraph k l).Adj (toChallenge (by omega) hl v) (toChallenge (by omega) hl w) ↔
      (graph k l).Adj v w := by
  constructor
  · rintro ⟨_,h|h⟩
    · exact adjRaw_reflects hkl hl hprim v w h
    · exact (adjRaw_reflects hkl hl hprim w v h).symm
  · rintro ⟨hne,a,b,ha,hb,hedge⟩
    refine ⟨fun h => hne (toChallenge_injective (by omega) hl hprim h),?_⟩
    rcases rawEdge_steps (by omega) hl a b hedge with h | h
    · exact Or.inl ⟨rawSite (by omega) hl a,rawSite (by omega) hl b,
        congrArg (toChallenge (by omega) hl) ha,congrArg (toChallenge (by omega) hl) hb,h⟩
    · exact Or.inr ⟨rawSite (by omega) hl b,rawSite (by omega) hl a,
        congrArg (toChallenge (by omega) hl) hb,congrArg (toChallenge (by omega) hl) ha,h⟩

noncomputable def challengeGraphIso (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) :
    graph k l ≃g ClaudeChallenge.gcGraph k l where
  toEquiv := challengeVertexEquiv (by omega) hl hprim
  map_rel_iff' := by intro v w; exact toChallenge_adj_iff hkl hl hprim v w

@[simp] theorem challengeGraphIso_apply (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (v : GCPrimitiveSurface.Vertex k l) :
    challengeGraphIso hkl hl hprim v=toChallenge (by omega) hl v := rfl

end R002.GCChallengeBridge
