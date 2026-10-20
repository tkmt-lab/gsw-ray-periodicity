import Formal.ClaudeBeltRegions

/-!
# Belt case of A3, part 3: challenge edges between developed regions

Written by a Claude worker (2026-10-19). For each band region and each of its three
edges, the neighboring region's chart is carried to the band chart by an explicit
`rotN j · + t`, and this map is a `ClaudeChallenge.Glue` (two shared labels with
matching corners). Consequently every unit step in the developed plane with one end in
a band region is an edge of `ClaudeChallenge.gcGraph`.
-/

namespace ClaudeBelt
open R002 R002.Icosahedron R002.GCPrimitive R002.GCPrimitiveSurface R002.GCChallengeBridge

variable {k l : ℤ}

/-- The challenge site of a point in a region. -/
def site (R : Reg) (p : Lattice) (h : InR k l R p) : ClaudeChallenge.Site k l :=
  ⟨(R.face,chart k l R p),(inTri_iff_closed _).mpr (interior_closed k l _ h)⟩

theorem glue_mk (g f : Fin 20) (j : ℕ) (t : Lattice) (ca cb ca' cb' : Fin 3) (hgf : g≠f)
    (hab : ClaudeChallenge.face g ca≠ClaudeChallenge.face g cb)
    (ha : ClaudeChallenge.face g ca=ClaudeChallenge.face f ca')
    (hb : ClaudeChallenge.face g cb=ClaudeChallenge.face f cb')
    (hpa : ClaudeChallenge.rotN j (ClaudeChallenge.corner k l ca)+t=ClaudeChallenge.corner k l ca')
    (hpb : ClaudeChallenge.rotN j (ClaudeChallenge.corner k l cb)+t=ClaudeChallenge.corner k l cb') :
    ClaudeChallenge.Glue k l g f j t :=
  ⟨hgf,_,_,hab,_,_,_,_,⟨ca,rfl,rfl⟩,⟨cb,rfl,rfl⟩,⟨ca',ha.symm,rfl⟩,⟨cb',hb.symm,rfl⟩,hpa,hpb⟩

theorem labels_a : ∀ r : Fin 5, kindFace .up r≠kindFace .low (r+1) ∧
    ClaudeChallenge.face (kindFace .up r) 0≠ClaudeChallenge.face (kindFace .up r) 2 ∧
    ClaudeChallenge.face (kindFace .up r) 0=ClaudeChallenge.face (kindFace .low (r+1)) 0 ∧
    ClaudeChallenge.face (kindFace .up r) 2=ClaudeChallenge.face (kindFace .low (r+1)) 1 := by
  decide
theorem labels_b : ∀ r : Fin 5, kindFace .up r≠kindFace .low r ∧
    ClaudeChallenge.face (kindFace .up r) 0≠ClaudeChallenge.face (kindFace .up r) 1 ∧
    ClaudeChallenge.face (kindFace .up r) 0=ClaudeChallenge.face (kindFace .low r) 2 ∧
    ClaudeChallenge.face (kindFace .up r) 1=ClaudeChallenge.face (kindFace .low r) 1 := by
  decide
theorem labels_c : ∀ r : Fin 5, kindFace .top r≠kindFace .low r ∧
    ClaudeChallenge.face (kindFace .top r) 1≠ClaudeChallenge.face (kindFace .top r) 2 ∧
    ClaudeChallenge.face (kindFace .top r) 1=ClaudeChallenge.face (kindFace .low r) 0 ∧
    ClaudeChallenge.face (kindFace .top r) 2=ClaudeChallenge.face (kindFace .low r) 2 := by
  decide
theorem labels_d : ∀ r : Fin 5, kindFace .low r≠kindFace .up r ∧
    ClaudeChallenge.face (kindFace .low r) 2≠ClaudeChallenge.face (kindFace .low r) 1 ∧
    ClaudeChallenge.face (kindFace .low r) 2=ClaudeChallenge.face (kindFace .up r) 0 ∧
    ClaudeChallenge.face (kindFace .low r) 1=ClaudeChallenge.face (kindFace .up r) 1 := by
  decide
theorem labels_e : ∀ r : Fin 5, kindFace .bot r≠kindFace .up r ∧
    ClaudeChallenge.face (kindFace .bot r) 1≠ClaudeChallenge.face (kindFace .bot r) 2 ∧
    ClaudeChallenge.face (kindFace .bot r) 1=ClaudeChallenge.face (kindFace .up r) 2 ∧
    ClaudeChallenge.face (kindFace .bot r) 2=ClaudeChallenge.face (kindFace .up r) 1 := by
  decide
theorem labels_f : ∀ r : Fin 5, kindFace .low (r+1)≠kindFace .up r ∧
    ClaudeChallenge.face (kindFace .low (r+1)) 0≠ClaudeChallenge.face (kindFace .low (r+1)) 1 ∧
    ClaudeChallenge.face (kindFace .low (r+1)) 0=ClaudeChallenge.face (kindFace .up r) 0 ∧
    ClaudeChallenge.face (kindFace .low (r+1)) 1=ClaudeChallenge.face (kindFace .up r) 2 := by
  decide

theorem kindFace_inj (K K' : Kind) (r r' : Fin 5) (h : kindFace K r=kindFace K' r') :
    K=K' ∧ r=r' := by
  cases K <;> cases K' <;> revert r r' <;> decide

theorem r5_sub_one (i : ℤ) : r5 i=r5 (i-1)+1 := by
  rw [← r5_add_one]; congr 1; ring

/-- Explicit edge identifications between a band region and its neighbors. -/
theorem nbr_glue (R : Reg) (hR : IsBand R) (e : Corner) : ∃ j t,
    ClaudeChallenge.Glue k l (nbr R e).face R.face j t ∧
      ∀ y, ClaudeChallenge.rotN j (chart k l (nbr R e) y)+t=chart k l R y := by
  rcases R with ⟨_|_|_|_,i⟩
  · fin_cases e
    · obtain ⟨h1,h2,h3,h4⟩ := labels_a (r5 (i-1))
      refine ⟨5,(0,0),?_,?_⟩
      · show ClaudeChallenge.Glue k l (kindFace .up (r5 (i-1))) (kindFace .low (r5 i)) 5 (0,0)
        rw [r5_sub_one i]
        refine glue_mk _ _ _ _ 0 2 0 1 h1 h2 h3 h4 ?_ ?_ <;>
          ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,ClaudeChallenge.corner]
      · intro y; ext <;> simp [nbr,chart,ClaudeChallenge.rotN,ClaudeChallenge.rot] <;> ring
    · obtain ⟨h1,h2,h3,h4⟩ := labels_b (r5 i)
      refine ⟨5,(-l,k+l),?_,?_⟩
      · exact glue_mk _ _ _ _ 0 1 2 1 h1 h2 h3 h4
          (by ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,ClaudeChallenge.corner])
          (by ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,ClaudeChallenge.corner] <;> ring)
      · intro y; ext <;> simp [nbr,chart,ClaudeChallenge.rotN,ClaudeChallenge.rot] <;> ring
    · obtain ⟨h1,h2,h3,h4⟩ := labels_c (r5 i)
      refine ⟨5,(-l-k,k),?_,?_⟩
      · exact glue_mk _ _ _ _ 1 2 0 2 h1 h2 h3 h4
          (by ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,ClaudeChallenge.corner] <;> ring)
          (by ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,ClaudeChallenge.corner] <;> ring)
      · intro y; ext <;> simp [nbr,chart,ClaudeChallenge.rotN,ClaudeChallenge.rot] <;> ring
  · fin_cases e
    · obtain ⟨h1,h2,h3,h4⟩ := labels_d (r5 i)
      refine ⟨1,(k+l,-k),?_,?_⟩
      · exact glue_mk _ _ _ _ 2 1 0 1 h1 h2 h3 h4
          (by ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,ClaudeChallenge.corner] <;> ring)
          (by ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,ClaudeChallenge.corner] <;> ring)
      · intro y; ext <;> simp [nbr,chart,ClaudeChallenge.rotN,ClaudeChallenge.rot] <;> ring
    · obtain ⟨h1,h2,h3,h4⟩ := labels_e (r5 i)
      refine ⟨3,(k-l,k+2*l),?_,?_⟩
      · exact glue_mk _ _ _ _ 1 2 2 1 h1 h2 h3 h4
          (by ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,ClaudeChallenge.corner] <;> ring)
          (by ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,ClaudeChallenge.corner] <;> ring)
      · intro y; ext <;> simp [nbr,chart,ClaudeChallenge.rotN,ClaudeChallenge.rot] <;> ring
    · obtain ⟨h1,h2,h3,h4⟩ := labels_f (r5 i)
      refine ⟨1,(0,0),?_,?_⟩
      · show ClaudeChallenge.Glue k l (kindFace .low (r5 (i+1))) (kindFace .up (r5 i)) 1 (0,0)
        rw [r5_add_one i]
        exact glue_mk _ _ _ _ 0 1 0 2 h1 h2 h3 h4
          (by ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,ClaudeChallenge.corner])
          (by ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,ClaudeChallenge.corner])
      · intro y; ext <;> simp [nbr,chart,ClaudeChallenge.rotN,ClaudeChallenge.rot] <;> ring
  · exact absurd hR (by simp [IsBand])
  · exact absurd hR (by simp [IsBand])

/-- A unit step from a point of `R` to a point of `R'` gives a challenge step,
when `R'` is `R` or a neighbor of the band region `R`. -/
theorem step_of_rel (R R' : Reg) (p q : Lattice) (hp : InR k l R p) (hq : InR k l R' q)
    (hu : GCPrimitive.Unit p q) (hrel : R'=R ∨ (IsBand R ∧ ∃ e, R'=nbr R e)) :
    ClaudeChallenge.StepTo k l (site R p hp) (site R' q hq) := by
  obtain ⟨u,hu,he⟩ := (unit_list_iff _ _).mpr (chart_unit R p q hu)
  refine ⟨u,hu,?_⟩
  rcases hrel with rfl | ⟨hR,e,rfl⟩
  · exact Or.inl ⟨rfl,he⟩
  · obtain ⟨j,t,hg,hiso⟩ := nbr_glue (k:=k) (l:=l) R hR e
    exact Or.inr ⟨j,t,hg,(hiso q).trans he⟩

theorem adj_of_steps (s s' : ClaudeChallenge.Site k l)
    (hne : ClaudeChallenge.vtx s≠ClaudeChallenge.vtx s')
    (h : ClaudeChallenge.StepTo k l s s' ∨ ClaudeChallenge.StepTo k l s' s) :
    (ClaudeChallenge.gcGraph k l).Adj (ClaudeChallenge.vtx s) (ClaudeChallenge.vtx s') := by
  refine ⟨hne,?_⟩
  rcases h with h | h
  · exact Or.inl ⟨s,s',rfl,rfl,h⟩
  · exact Or.inr ⟨s',s,rfl,rfl,h⟩

/-- Edges between two developed points, one of them in a band region. -/
theorem interior_adj (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) (R R' : Reg) (p q : Lattice)
    (hp : InR k l R p) (hq : InR k l R' q) (hu : GCPrimitive.Unit p q)
    (hcase : IsBand R ∨ IsBand R' ∨ R=R')
    (hne : ClaudeChallenge.vtx (site R p hp)≠ClaudeChallenge.vtx (site R' q hq)) :
    (ClaudeChallenge.gcGraph k l).Adj (ClaudeChallenge.vtx (site R p hp))
      (ClaudeChallenge.vtx (site R' q hq)) := by
  apply adj_of_steps _ _ hne
  rcases hcase with hR | hR | rfl
  · left
    rcases band_step hk hl hprim R R' hR p q hp hu hq with h | h
    · exact step_of_rel R R' p q hp hq hu (Or.inl h)
    · exact step_of_rel R R' p q hp hq hu (Or.inr ⟨hR,h⟩)
  · right
    have hu' := unit_symm p q hu
    rcases band_step hk hl hprim R' R hR q p hq hu' hp with h | h
    · exact step_of_rel R' R q p hq hp hu' (Or.inl h)
    · exact step_of_rel R' R q p hq hp hu' (Or.inr ⟨hR,h⟩)
  · left; exact step_of_rel R R p q hp hq hu (Or.inl rfl)

/-- Edge from a developed point to a parent corner of its own region. -/
theorem corner_adj (hk : 0<k) (hl : 0<l) (R : Reg) (p q : Lattice) (hp : InR k l R p)
    (c : Fin 3) (hc : chart k l R q=ClaudeChallenge.corner k l c) (hu : GCPrimitive.Unit p q)
    (hne : ClaudeChallenge.vtx (site R p hp)≠ClaudeChallenge.vtx (cornerSite hk hl R.face c)) :
    (ClaudeChallenge.gcGraph k l).Adj (ClaudeChallenge.vtx (site R p hp))
      (ClaudeChallenge.vtx (cornerSite hk hl R.face c)) := by
  apply adj_of_steps _ _ hne
  left
  obtain ⟨u,hu,he⟩ := (unit_list_iff _ _).mpr (chart_unit R p q hu)
  refine ⟨u,hu,Or.inl ⟨rfl,?_⟩⟩
  show ClaudeChallenge.corner k l c=chart k l R p+u
  rw [← hc]; exact he

/-- Two developed points with the same challenge vertex and nearby first coordinates
are the same plane point. -/
theorem site_vtx_eq (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) {R R' : Reg} {p q : Lattice}
    (hp : InR k l R p) (hq : InR k l R' q)
    (h : ClaudeChallenge.vtx (site R p hp)=ClaudeChallenge.vtx (site R' q hq))
    (hx1 : -1≤p.1-q.1) (hx2 : p.1-q.1≤1) : p=q := by
  have hs := vtx_interior_inj hk hl hprim (site R p hp) (site R' q hq) hp h
  have hface : R.face=R'.face := congrArg (fun s : ClaudeChallenge.Site k l => s.val.1) hs
  have hchart : chart k l R p=chart k l R' q :=
    congrArg (fun s : ClaudeChallenge.Site k l => s.val.2) hs
  obtain ⟨hK,hr⟩ := kindFace_inj _ _ _ _ hface
  rcases R with ⟨K,i⟩; rcases R' with ⟨K',i'⟩
  simp only at hK hr; subst hK
  have hmod : i%5=i'%5 := by
    have := congrArg Fin.val hr; simp only [r5] at this; omega
  have key : ∀ d : ℤ, d%5=0 → -1≤d*l → d*l≤1 → d=0 := by
    intro d hd h1 h2
    rcases lt_trichotomy d 0 with hd' | hd' | hd'
    · have : d ≤ -5 := by omega
      nlinarith
    · exact hd'
    · have : 5 ≤ d := by omega
      nlinarith
  cases K <;> simp only [chart,ClaudeChallenge.rot,Prod.mk_add_mk,Prod.mk.injEq] at hchart <;>
    obtain ⟨c1,c2⟩ := hchart
  · have := key (i'-i) (by omega) (by nlinarith) (by nlinarith)
    have hi : i'=i := by omega
    subst hi; ext <;> linarith
  · have := key (i'-i) (by omega) (by nlinarith) (by nlinarith)
    have hi : i'=i := by omega
    subst hi; ext <;> linarith
  · have := key (i'-i) (by omega) (by nlinarith) (by nlinarith)
    have hi : i'=i := by omega
    subst hi; ext <;> linarith
  · have := key (i'-i) (by omega) (by nlinarith) (by nlinarith)
    have hi : i'=i := by omega
    subst hi; ext <;> linarith

end ClaudeBelt
