import Formal.GCChallengeIsometries

namespace R002.GCChallengeBridge
open Icosahedron GCPrimitive GCPrimitiveSurface
variable {k l : ℤ}

/-- A gluing with the two directed endpoint labels is the designated seam map. -/
theorem oriented_affine_normal (hk : 0<k) (hl : 0<l) (f g : Face) (e a b : Corner)
    (hfg : f≠g) (ha : faceVertex f e=faceVertex g a)
    (hb : faceVertex f (e+1)=faceVertex g b) (j : ℕ) (t : Lattice)
    (hp : ClaudeChallenge.rotN j (posMap k l f (corner k l e))+t=posMap k l g (corner k l a))
    (hq : ClaudeChallenge.rotN j (posMap k l f (corner k l (e+1)))+t=posMap k l g (corner k l b)) :
    g=(mate (f,e)).1 ∧ ∀ p,
      ClaudeChallenge.rotN j (posMap k l f p)+t=
        posMap k l g (unframe k l (mate (f,e)).2 (opposite k l (frame k l e p))) := by
  obtain ⟨hg,he,hm⟩ := two_labels_mate f g e a b hfg ha hb
  subst g; subst a; subst b
  obtain ⟨j0,t0,hg0,ht⟩ := aligned_glue (k:=k) (l:=l) (faceMap f) (faceMap (mate (f,e)).1)
    (cornerMap f e) (cornerMap (mate (f,e)).1 (mate (f,e)).2)
    (fun h => hfg (faceMap_bijective.1 h))
    (by rw [← cornerMap_add_one,labels_agree,labels_agree]; exact ha)
    (by rw [← cornerMap_add_one,labels_agree,labels_agree]; exact hb)
  have hmap : ∀ p, ClaudeChallenge.rotN j0 (posMap k l f p)+t0=
      posMap k l (mate (f,e)).1 (unframe k l (mate (f,e)).2 (opposite k l (frame k l e p))) := by
    intro p; rw [ht,unfold_posMap]
  have hne : corner k l e≠corner k l (e+1) := by
    intro h
    have he := corner_injective k l hk hl h
    fin_cases e <;> simp at he
  have hstart := hmap (corner k l e)
  rw [unfold_corner_start] at hstart
  have hend := hmap (corner k l (e+1))
  rw [unfold_corner_end] at hend
  have hsame := affine_unique j j0 t t0 _ _
    (fun h => hne (posMap_injective f h)) (hp.trans hstart.symm) (hq.trans hend.symm)
  exact ⟨rfl,fun p => (hsame _).trans (hmap p)⟩

/-- Every gluing allowed by the independent specification has the research seam form. -/
theorem glue_normal (hk : 0<k) (hl : 0<l) (f g : Face) (j : ℕ) (t : Lattice)
    (h : ClaudeChallenge.Glue k l (faceMap f) (faceMap g) j t) :
    ∃ e : Corner, g=(mate (f,e)).1 ∧ ∀ p,
      ClaudeChallenge.rotN j (posMap k l f p)+t=
        posMap k l g (unframe k l (mate (f,e)).2 (opposite k l (frame k l e p))) := by
  rcases h with ⟨hfg,x,y,hxy,pa,pb,qa,qb,
    ⟨i',hfi,rfl⟩,⟨j',hfj,rfl⟩,⟨a',hga,rfl⟩,⟨b',hgb,rfl⟩,hp,hq⟩
  obtain ⟨i,rfl⟩ := (cornerMap_bijective f).2 i'
  obtain ⟨s,rfl⟩ := (cornerMap_bijective f).2 j'
  obtain ⟨a,rfl⟩ := (cornerMap_bijective g).2 a'
  obtain ⟨b,rfl⟩ := (cornerMap_bijective g).2 b'
  rw [labels_agree] at hfi hfj hga hgb
  rw [← corners_agree,← corners_agree] at hp hq
  have hne : i≠s := by intro he; subst s; exact hxy (hfi.symm.trans hfj)
  have hfg' : f≠g := fun he => hfg (congrArg faceMap he)
  rcases pair_oriented i s hne with hs | hi
  · subst s
    exact ⟨i,oriented_affine_normal hk hl f g i a b hfg'
      (hfi.trans hga.symm) (hfj.trans hgb.symm) j t hp hq⟩
  · subst i
    exact ⟨s,oriented_affine_normal hk hl f g s b a hfg'
      (hfj.trans hgb.symm) (hfi.trans hga.symm) j t hq hp⟩

end R002.GCChallengeBridge
