import Formal.ClaudePosChart

/-!
# Positive side of A3, part 3: from developed plane points to a literal path

Written by a Claude worker (2026-10-19). Generic version of `ClaudeBelt.literal_of_plane`
for the coarse-triangle development: a finite unit zigzag `P 0, …, P (N-1)` whose interior
points lie in coarse triangles that are faces for a labeling `L`, with the two ends at
parent vertices, gives a `ClaudeChallenge.LiteralPath`.
-/

namespace ClaudePos
open R002 R002.Icosahedron R002.GCPrimitive R002.GCPrimitiveSurface R002.GCChallengeBridge
open ClaudeChallenge (rot rotN)

variable {k l : ℤ}

open Classical in
/-- The challenge vertex of a developed plane point. -/
noncomputable def pv (hk : 0<k) (hl : 0<l) (L : ℤ × ℤ → Fin 12) (x : Lattice) :
    ClaudeChallenge.Vertex k l :=
  if h : ∃ D, InCT k l D x then ClaudeChallenge.vtx (site L (Classical.choose h) x (Classical.choose_spec h))
  else ClaudeChallenge.vtx (cornerSite hk hl 0 0)

theorem site_congr (L : ℤ × ℤ → Fin 12) {D D' : CT} (h : D=D') (x : Lattice) (hD : InCT k l D x)
    (hD' : InCT k l D' x) : site L D x hD=site L D' x hD' := by
  subst h; rfl

theorem pv_eq (hk : 0<k) (hl : 0<l) (L : ℤ × ℤ → Fin 12) (D : CT) (x : Lattice) (h : InCT k l D x) :
    pv hk hl L x=ClaudeChallenge.vtx (site L D x h) := by
  have hex : ∃ D, InCT k l D x := ⟨D,h⟩
  rw [pv,dif_pos hex]
  congr 1
  exact site_congr L (inCT_unique hk hl _ _ x (Classical.choose_spec hex) h) x _ _

noncomputable def posPath (hk : 0<k) (hl : 0<l) (L : ℤ × ℤ → Fin 12) (N : ℕ) (P : ℕ → Lattice)
    (fs : Fin 20) (cs : Fin 3) (fe : Fin 20) (ce : Fin 3) (n : ℕ) : ClaudeChallenge.Vertex k l :=
  if n=0 then ClaudeChallenge.vtx (cornerSite hk hl fs cs)
  else if n=N-1 then ClaudeChallenge.vtx (cornerSite hk hl fe ce)
  else pv hk hl L (P n)

/-- Adjacency of a developed point with a parent corner of its coarse triangle. -/
theorem corner_adj_ct (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) (L : ℤ × ℤ → Fin 12)
    (D : CT) (m : Fin 3) (x : Lattice) (hx : InCT k l D x) (hD : FaceOK L D)
    (f : Fin 20) (c : Fin 3) (hlab : L (D.vert m)=ClaudeChallenge.face f c)
    (hu : GCPrimitive.Unit x (pos k l (D.vert m))) :
    (ClaudeChallenge.gcGraph k l).Adj (ClaudeChallenge.vtx (site L D x hx))
      (ClaudeChallenge.vtx (cornerSite hk hl f c)) := by
  have hv : ClaudeChallenge.vtx (cornerSite hk hl (fr L D).1 ((fr L D).2+m))=
      ClaudeChallenge.vtx (cornerSite hk hl f c) :=
    ClaudeBelt.vtx_corner_eq hk hl _ _ _ _ ((hD m).trans hlab)
  rw [← hv]
  have hne := (ClaudeBelt.vtx_corner_ne_interior hk hl hprim (fr L D).1 ((fr L D).2+m) _
    (site_interior L D x hx)).symm
  apply ClaudeBelt.adj_of_steps _ _ hne
  left
  obtain ⟨u,hu',he⟩ := (unit_list_iff _ _).mpr (chart_unit (k:=k) (l:=l) D (fr L D).2 _ _ hu)
  refine ⟨u,hu',Or.inl ⟨rfl,?_⟩⟩
  show ClaudeChallenge.corner k l ((fr L D).2+m)=chart k l D (fr L D).2 x+u
  rw [← he,chart_vert]

theorem literal_of_ct (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) (L : ℤ × ℤ → Fin 12)
    (N : ℕ) (P : ℕ → Lattice) (fs : Fin 20) (cs : Fin 3) (fe : Fin 20) (ce : Fin 3)
    (hN : 4≤N) (hEven : Even N)
    (hct : ∀ n, 0<n → n<N-1 → ∃ D, InCT k l D (P n) ∧ FaceOK L D)
    (hunit : ∀ n m, n<m → m≤n+2 → m<N → GCPrimitive.Unit (P n) (P m))
    (hinj : ∀ n m D D', 0<n → n<N-1 → 0<m → m<N-1 → InCT k l D (P n) → InCT k l D' (P m) →
      FaceOK L D → FaceOK L D' → (fr L D).1=(fr L D').1 →
      chart k l D (fr L D).2 (P n)=chart k l D' (fr L D').2 (P m) → n=m)
    (hstart : ∀ n, 0<n → n≤2 → ∃ D m, InCT k l D (P n) ∧ FaceOK L D ∧
      pos k l (D.vert m)=P 0 ∧ L (D.vert m)=ClaudeChallenge.face fs cs)
    (hend : ∀ n, N-3≤n → n<N-1 → ∃ D m, InCT k l D (P n) ∧ FaceOK L D ∧
      pos k l (D.vert m)=P (N-1) ∧ L (D.vert m)=ClaudeChallenge.face fe ce)
    (hse : ClaudeChallenge.face fs cs≠ClaudeChallenge.face fe ce) :
    ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) N
      (posPath (by omega) hl L N P fs cs fe ce) := by
  have hk : 0<k := by omega
  set p := posPath hk hl L N P fs cs fe ce with hpdef
  have p0 : p 0=ClaudeChallenge.vtx (cornerSite hk hl fs cs) := by simp [hpdef,posPath]
  have pN : p (N-1)=ClaudeChallenge.vtx (cornerSite hk hl fe ce) := by
    simp [hpdef,posPath,show N-1≠0 by omega]
  have pmid : ∀ n, 0<n → n<N-1 → ∀ D (h : InCT k l D (P n)),
      p n=ClaudeChallenge.vtx (site L D (P n) h) := by
    intro n h0 h1 D h
    simp only [hpdef,posPath]; rw [if_neg (by omega),if_neg (by omega)]
    exact pv_eq hk hl L D _ h
  -- injectivity
  have hinjp : ∀ i j, i<N → j<N → p i=p j → i=j := by
    have corner_mid : ∀ (f : Fin 20) (c : Fin 3) n, 0<n → n<N-1 →
        ClaudeChallenge.vtx (cornerSite hk hl f c)≠p n := by
      intro f c n h0 h1
      obtain ⟨D,hD,-⟩ := hct n h0 h1
      rw [pmid n h0 h1 D hD]
      exact ClaudeBelt.vtx_corner_ne_interior hk hl hprim f c _ (site_interior L D _ hD)
    intro i j hi hj he
    by_cases hi0 : i=0 <;> by_cases hj0 : j=0
    · omega
    · by_cases hjN : j=N-1
      · subst hi0; rw [p0,hjN,pN] at he
        exact absurd he (ClaudeBelt.vtx_corner_ne hk hl hprim _ _ _ _ hse)
      · subst hi0; rw [p0] at he
        exact absurd he (corner_mid _ _ j (by omega) (by omega))
    · by_cases hiN : i=N-1
      · subst hj0; rw [p0,hiN,pN] at he
        exact absurd he.symm (ClaudeBelt.vtx_corner_ne hk hl hprim _ _ _ _ hse)
      · subst hj0; rw [p0] at he
        exact absurd he.symm (corner_mid _ _ i (by omega) (by omega))
    · by_cases hiN : i=N-1 <;> by_cases hjN : j=N-1
      · omega
      · rw [hiN,pN] at he
        exact absurd he (corner_mid _ _ j (by omega) (by omega))
      · rw [hjN,pN] at he
        exact absurd he.symm (corner_mid _ _ i (by omega) (by omega))
      · obtain ⟨D,hD,hDo⟩ := hct i (by omega) (by omega)
        obtain ⟨D',hD',hDo'⟩ := hct j (by omega) (by omega)
        rw [pmid i (by omega) (by omega) D hD,pmid j (by omega) (by omega) D' hD'] at he
        have hs := ClaudeBelt.vtx_interior_inj hk hl hprim _ _ (site_interior L D _ hD) he
        have hf := congrArg (fun s : ClaudeChallenge.Site k l => s.val.1) hs
        have hc := congrArg (fun s : ClaudeChallenge.Site k l => s.val.2) hs
        exact hinj i j D D' (by omega) (by omega) (by omega) (by omega) hD hD' hDo hDo' hf hc
  -- adjacency for nearby indices
  have hadj : ∀ i j, i<j → j ≤ i+2 → j<N → (ClaudeChallenge.gcGraph k l).Adj (p i) (p j) := by
    intro i j hij hji hjN
    by_cases hi0 : i=0
    · subst hi0
      obtain ⟨D,m,hD,hDo,hpos,hlab⟩ := hstart j (by omega) (by omega)
      rw [p0,pmid j (by omega) (by omega) D hD]
      have hu := unit_symm _ _ (hunit 0 j hij hji hjN)
      rw [← hpos] at hu
      exact (corner_adj_ct hk hl hprim L D m _ hD hDo fs cs hlab hu).symm
    by_cases hjN' : j=N-1
    · subst hjN'
      obtain ⟨D,m,hD,hDo,hpos,hlab⟩ := hend i (by omega) (by omega)
      rw [pN,pmid i (by omega) (by omega) D hD]
      have hu := hunit i (N-1) hij hji hjN
      rw [← hpos] at hu
      exact corner_adj_ct hk hl hprim L D m _ hD hDo fe ce hlab hu
    · obtain ⟨D,hD,hDo⟩ := hct i (by omega) (by omega)
      obtain ⟨D',hD',hDo'⟩ := hct j (by omega) (by omega)
      have hne : p i≠p j := fun h => absurd (hinjp i j (by omega) hjN h) (by omega)
      rw [pmid i (by omega) (by omega) D hD,pmid j (by omega) (by omega) D' hD'] at hne ⊢
      exact ClaudeBelt.adj_of_steps _ _ hne
        (Or.inl (step_sites hk hl hprim L D D' _ _ hDo hDo' hD hD' (hunit i j hij hji hjN)))
  refine ⟨hN,hEven,fun i j hi hj h => hinjp i j hi hj h,
    fun i hi => hadj i (i+1) (by omega) (by omega) hi,
    fun i hi => hadj i (i+2) (by omega) (by omega) hi,?_,?_,?_,?_⟩
  · rw [p0]; exact ClaudeBelt.deg_corner hkl hl hprim fs cs
  · rw [pN]; exact ClaudeBelt.deg_corner hkl hl hprim fe ce
  · obtain ⟨D,hD,-⟩ := hct 1 (by omega) (by omega)
    rw [pmid 1 (by omega) (by omega) D hD]
    exact ClaudeBelt.deg_interior hkl hl hprim _ (site_interior L D _ hD)
  · obtain ⟨D,hD,-⟩ := hct (N-2) (by omega) (by omega)
    rw [pmid (N-2) (by omega) (by omega) D hD]
    exact ClaudeBelt.deg_interior hkl hl hprim _ (site_interior L D _ hD)

end ClaudePos
