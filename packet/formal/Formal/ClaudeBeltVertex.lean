import Formal.GCChallengeTransport

/-!
# Belt case of A3, part 1: vertex facts on the challenge quotient

Written by a Claude worker (2026-10-19). Only new declarations; the main team's library
is reused through the existing bridge `toChallenge` / `challenge_degree`.

For a primitive pair `k > l > 0`:
* a challenge site whose chart point is a strict interior lattice point has degree six,
  and it is the only site of its vertex;
* corner sites with the same parent label are the same vertex, with different labels
  they are different vertices, and they never meet interior sites;
* corner sites have degree five.
-/

namespace ClaudeBelt
open R002 R002.Icosahedron R002.GCPrimitive R002.GCPrimitiveSurface R002.GCChallengeBridge

variable {k l : ℤ}

theorem interior_posMap (f : Face) (p : Lattice) :
    Interior k l (posMap k l f p) ↔ Interior k l p := by
  by_cases hf : f=4 <;> simp [posMap,hf,interior_turn]

theorem vtx_rawSite (hk : 0<k) (hl : 0<l) (u : Raw k l) :
    ClaudeChallenge.vtx (rawSite hk hl u)=toChallenge hk hl (vertex u) := rfl

/-- A site with a strict interior chart point has degree six. -/
theorem deg_interior (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (s : ClaudeChallenge.Site k l) (hs : Interior k l s.val.2) :
    ClaudeChallenge.deg (ClaudeChallenge.gcGraph k l) (ClaudeChallenge.vtx s)=6 := by
  obtain ⟨u,rfl⟩ := rawSite_surjective (by omega) hl hprim s
  rw [vtx_rawSite (by omega) hl u,challenge_degree hkl hl hprim]
  rcases u with ⟨f,e|p⟩
  · exact False.elim (corner_not_interior k l e ((interior_posMap f _).mp hs))
  · rfl

/-- The vertex of an interior site has no other site. -/
theorem vtx_interior_inj (hk : 0<k) (hl : 0<l) (hprim : Primitive k l)
    (s s' : ClaudeChallenge.Site k l) (hs : Interior k l s.val.2)
    (h : ClaudeChallenge.vtx s=ClaudeChallenge.vtx s') : s=s' := by
  obtain ⟨u,rfl⟩ := rawSite_surjective hk hl hprim s
  obtain ⟨u',rfl⟩ := rawSite_surjective hk hl hprim s'
  rw [vtx_rawSite,vtx_rawSite] at h
  have hv := toChallenge_injective hk hl hprim h
  rcases u with ⟨f,e|p⟩
  · exact False.elim (corner_not_interior k l e ((interior_posMap f _).mp hs))
  · have hc : canonical u'=Sum.inr (f,p) := by
      have := congrArg toCanonical hv
      simpa [canonical] using this.symm
    rw [interior_raw_unique u' f p hc]

/-- Corner sites as challenge vertices are determined by their parent label. -/
theorem vtx_corner_raw (hk : 0<k) (hl : 0<l) (f : Fin 20) (c : Fin 3) :
    ∃ f0 : Face, ∃ e0 : Corner, faceMap f0=f ∧ cornerMap f0 e0=c ∧
      ClaudeChallenge.vtx (cornerSite hk hl f c)=toChallenge hk hl (vertex (f0,.inl e0)) := by
  obtain ⟨f0,rfl⟩ := faceMap_bijective.2 f
  obtain ⟨e0,rfl⟩ := (cornerMap_bijective f0).2 c
  refine ⟨f0,e0,rfl,rfl,?_⟩
  rw [toChallenge_vertex,rawSite_corner]

theorem vtx_corner_eq (hk : 0<k) (hl : 0<l) (f g : Fin 20) (c c' : Fin 3)
    (h : ClaudeChallenge.face f c=ClaudeChallenge.face g c') :
    ClaudeChallenge.vtx (cornerSite hk hl f c)=ClaudeChallenge.vtx (cornerSite hk hl g c') := by
  obtain ⟨f0,e0,rfl,rfl,h1⟩ := vtx_corner_raw hk hl f c
  obtain ⟨g0,d0,rfl,rfl,h2⟩ := vtx_corner_raw hk hl g c'
  rw [h1,h2]
  congr 1
  apply toCanonical_injective
  change Sum.inl (faceVertex f0 e0)=Sum.inl (faceVertex g0 d0)
  rw [← labels_agree,← labels_agree,h]

theorem vtx_corner_ne (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) (f g : Fin 20) (c c' : Fin 3)
    (h : ClaudeChallenge.face f c≠ClaudeChallenge.face g c') :
    ClaudeChallenge.vtx (cornerSite hk hl f c)≠ClaudeChallenge.vtx (cornerSite hk hl g c') := by
  obtain ⟨f0,e0,rfl,rfl,h1⟩ := vtx_corner_raw hk hl f c
  obtain ⟨g0,d0,rfl,rfl,h2⟩ := vtx_corner_raw hk hl g c'
  rw [h1,h2]
  intro he
  have hv := congrArg toCanonical (toChallenge_injective hk hl hprim he)
  change Sum.inl (faceVertex f0 e0)=Sum.inl (faceVertex g0 d0) at hv
  apply h
  rw [labels_agree,labels_agree]
  exact Sum.inl.inj hv

theorem cornerSite_not_interior (hk : 0<k) (hl : 0<l) (f : Fin 20) (c : Fin 3) :
    ¬Interior k l (cornerSite hk hl f c).val.2 :=
  corner_not_interior k l c

theorem vtx_corner_ne_interior (hk : 0<k) (hl : 0<l) (hprim : Primitive k l)
    (f : Fin 20) (c : Fin 3) (s : ClaudeChallenge.Site k l) (hs : Interior k l s.val.2) :
    ClaudeChallenge.vtx (cornerSite hk hl f c)≠ClaudeChallenge.vtx s := by
  intro h
  have := vtx_interior_inj hk hl hprim s _ hs h.symm
  rw [this] at hs
  exact cornerSite_not_interior hk hl f c hs

theorem deg_corner (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) (f : Fin 20) (c : Fin 3) :
    ClaudeChallenge.deg (ClaudeChallenge.gcGraph k l)
      (ClaudeChallenge.vtx (cornerSite (by omega) hl f c))=5 := by
  obtain ⟨f0,e0,_,_,h1⟩ := vtx_corner_raw (k:=k) (by omega) hl f c
  rw [h1,challenge_degree hkl hl hprim]
  rfl

end ClaudeBelt
