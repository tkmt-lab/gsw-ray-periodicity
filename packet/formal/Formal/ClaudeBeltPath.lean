import Formal.ClaudeBeltGlue

/-!
# Belt case of A3, part 4: from a plane zigzag to a literal path

Written by a Claude worker (2026-10-19). A finite sequence of plane lattice points whose
interior members lie in developed regions, whose ends are parent corners of the
neighboring regions, and which is a unit zigzag, gives a `ClaudeChallenge.LiteralPath`.
-/

namespace ClaudeBelt
open R002 R002.Icosahedron R002.GCPrimitive R002.GCPrimitiveSurface R002.GCChallengeBridge

variable {k l : ℤ}

open Classical in
/-- The challenge vertex of a developed plane point. -/
noncomputable def pv (hk : 0<k) (hl : 0<l) (x : Lattice) : ClaudeChallenge.Vertex k l :=
  if h : ∃ R, InR k l R x then ClaudeChallenge.vtx (site (Classical.choose h) x (Classical.choose_spec h))
  else ClaudeChallenge.vtx (cornerSite hk hl 0 0)

theorem site_congr {R R' : Reg} (h : R=R') (x : Lattice) (hR : InR k l R x) (hR' : InR k l R' x) :
    site R x hR=site R' x hR' := by
  subst h; rfl

theorem pv_eq (hk : 0<k) (hl : 0<l) (R : Reg) (x : Lattice) (h : InR k l R x) :
    pv hk hl x=ClaudeChallenge.vtx (site R x h) := by
  have hex : ∃ R, InR k l R x := ⟨R,h⟩
  rw [pv,dif_pos hex]
  congr 1
  exact site_congr (region_unique hk hl _ _ x (Classical.choose_spec hex) h) x _ _

/-- The path: two parent corners at the ends, developed points in between. -/
noncomputable def beltPath (hk : 0<k) (hl : 0<l) (N : ℕ) (P : ℕ → Lattice)
    (fs : Fin 20) (cs : Fin 3) (fe : Fin 20) (ce : Fin 3) (n : ℕ) : ClaudeChallenge.Vertex k l :=
  if n=0 then ClaudeChallenge.vtx (cornerSite hk hl fs cs)
  else if n=N-1 then ClaudeChallenge.vtx (cornerSite hk hl fe ce)
  else pv hk hl (P n)

theorem literal_of_plane (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (N : ℕ) (P : ℕ → Lattice) (fs : Fin 20) (cs : Fin 3) (fe : Fin 20) (ce : Fin 3)
    (hN : 4≤N) (hEven : Even N)
    (hreg : ∀ n, 0<n → n<N-1 → ∃ R, InR k l R (P n))
    (hcap : ∀ n m R R', 0<n → n<m → m≤n+2 → m<N-1 → InR k l R (P n) → InR k l R' (P m) →
      IsBand R ∨ IsBand R' ∨ R=R')
    (hunit : ∀ n m, n<m → m≤n+2 → m<N → GCPrimitive.Unit (P n) (P m))
    (hx : ∀ n m, n<N → m<N → -1≤(P n).1-(P m).1 ∧ (P n).1-(P m).1≤1)
    (hinj : ∀ n m, n<N → m<N → P n=P m → n=m)
    (hstart : ∀ n, 0<n → n≤2 → ∃ R c, InR k l R (P n) ∧
      chart k l R (P 0)=ClaudeChallenge.corner k l c ∧
      ClaudeChallenge.face R.face c=ClaudeChallenge.face fs cs)
    (hend : ∀ n, N-3≤n → n<N-1 → ∃ R c, InR k l R (P n) ∧
      chart k l R (P (N-1))=ClaudeChallenge.corner k l c ∧
      ClaudeChallenge.face R.face c=ClaudeChallenge.face fe ce)
    (hse : ClaudeChallenge.face fs cs≠ClaudeChallenge.face fe ce) :
    ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) N
      (beltPath (by omega) hl N P fs cs fe ce) := by
  have hk : 0<k := by omega
  set p := beltPath hk hl N P fs cs fe ce with hpdef
  have p0 : p 0=ClaudeChallenge.vtx (cornerSite hk hl fs cs) := by simp [hpdef,beltPath]
  have pN : p (N-1)=ClaudeChallenge.vtx (cornerSite hk hl fe ce) := by
    simp [hpdef,beltPath,show N-1≠0 by omega]
  have pmid : ∀ n, 0<n → n<N-1 → ∀ R (h : InR k l R (P n)),
      p n=ClaudeChallenge.vtx (site R (P n) h) := by
    intro n h0 h1 R h
    simp only [hpdef,beltPath]; rw [if_neg (by omega),if_neg (by omega)]
    exact pv_eq hk hl R _ h
  -- injectivity
  have hinjp : ∀ i j, i<N → j<N → p i=p j → i=j := by
    have corner_mid : ∀ (f : Fin 20) (c : Fin 3) n, 0<n → n<N-1 →
        ClaudeChallenge.vtx (cornerSite hk hl f c)≠p n := by
      intro f c n h0 h1
      obtain ⟨R,hR⟩ := hreg n h0 h1
      rw [pmid n h0 h1 R hR]
      exact vtx_corner_ne_interior hk hl hprim f c _ hR
    intro i j hi hj he
    by_cases hi0 : i=0 <;> by_cases hj0 : j=0
    · omega
    · by_cases hjN : j=N-1
      · subst hi0; rw [p0,hjN,pN] at he
        exact absurd he (vtx_corner_ne hk hl hprim _ _ _ _ hse)
      · subst hi0; rw [p0] at he
        exact absurd he (corner_mid _ _ j (by omega) (by omega))
    · by_cases hiN : i=N-1
      · subst hj0; rw [p0,hiN,pN] at he
        exact absurd he.symm (vtx_corner_ne hk hl hprim _ _ _ _ hse)
      · subst hj0; rw [p0] at he
        exact absurd he.symm (corner_mid _ _ i (by omega) (by omega))
    · by_cases hiN : i=N-1 <;> by_cases hjN : j=N-1
      · omega
      · rw [hiN,pN] at he
        exact absurd he (corner_mid _ _ j (by omega) (by omega))
      · rw [hjN,pN] at he
        exact absurd he.symm (corner_mid _ _ i (by omega) (by omega))
      · obtain ⟨R,hR⟩ := hreg i (by omega) (by omega)
        obtain ⟨R',hR'⟩ := hreg j (by omega) (by omega)
        rw [pmid i (by omega) (by omega) R hR,pmid j (by omega) (by omega) R' hR'] at he
        have hxx := hx i j hi hj
        exact hinj i j hi hj (site_vtx_eq hk hl hprim hR hR' he hxx.1 hxx.2)
  -- adjacency for nearby indices
  have hadj : ∀ i j, i<j → j≤ i+2 → j<N → (ClaudeChallenge.gcGraph k l).Adj (p i) (p j) := by
    intro i j hij hji hjN
    have hne : p i≠p j := fun h => absurd (hinjp i j (by omega) hjN h) (by omega)
    by_cases hi0 : i=0
    · subst hi0
      obtain ⟨R,c,hR,hc,hlab⟩ := hstart j (by omega) (by omega)
      rw [p0,pmid j (by omega) (by omega) R hR] at hne ⊢
      have hv := vtx_corner_eq hk hl R.face fs c cs hlab
      rw [← hv] at hne ⊢
      exact (corner_adj hk hl R (P j) (P 0) hR c hc (unit_symm _ _ (hunit 0 j hij hji hjN))
        (Ne.symm hne)).symm
    by_cases hjN' : j=N-1
    · subst hjN'
      obtain ⟨R,c,hR,hc,hlab⟩ := hend i (by omega) (by omega)
      rw [pN,pmid i (by omega) (by omega) R hR] at hne ⊢
      have hv := vtx_corner_eq hk hl R.face fe c ce hlab
      rw [← hv] at hne ⊢
      exact corner_adj hk hl R (P i) (P (N-1)) hR c hc (hunit i (N-1) hij hji hjN) hne
    · obtain ⟨R,hR⟩ := hreg i (by omega) (by omega)
      obtain ⟨R',hR'⟩ := hreg j (by omega) (by omega)
      rw [pmid i (by omega) (by omega) R hR,pmid j (by omega) (by omega) R' hR'] at hne ⊢
      exact interior_adj hk hl hprim R R' (P i) (P j) hR hR' (hunit i j hij hji hjN)
        (hcap i j R R' (by omega) hij hji (by omega) hR hR') hne
  refine ⟨hN,hEven,fun i j hi hj h => hinjp i j hi hj h,
    fun i hi => hadj i (i+1) (by omega) (by omega) hi,
    fun i hi => hadj i (i+2) (by omega) (by omega) hi,?_,?_,?_,?_⟩
  · rw [p0]; exact deg_corner hkl hl hprim fs cs
  · rw [pN]; exact deg_corner hkl hl hprim fe ce
  · obtain ⟨R,hR⟩ := hreg 1 (by omega) (by omega)
    rw [pmid 1 (by omega) (by omega) R hR]
    exact deg_interior hkl hl hprim _ hR
  · obtain ⟨R,hR⟩ := hreg (N-2) (by omega) (by omega)
    rw [pmid (N-2) (by omega) (by omega) R hR]
    exact deg_interior hkl hl hprim _ hR

end ClaudeBelt
