import Formal.ClaudePosCover

/-!
# Positive side of A3, part 8: covering the four band/row-sign combinations

Written by a Claude worker (2026-10-19).
-/

namespace ClaudePos
open R002 R002.Icosahedron R002.GCPrimitive R002.GCPrimitiveSurface R002.GCChallengeBridge

variable {k l : ℤ}

/-- A point strictly between two consecutive rows is not a parent vertex. -/
theorem nv_strict (hk : 0<k) (hl : 0<l) (v m : ℤ) (x : Lattice)
    (h0 : m*norm k l<a k l x+v*b k l x) (h1 : a k l x+v*b k l x<(m+1)*norm k l) :
    ∀ c, x≠pos k l c := by
  intro c hc
  have hT := norm_pos k l hk hl.le
  rw [hc,sigma_pos] at h0 h1
  have := lt_of_mul_lt_mul_T hT h0
  have := lt_of_mul_lt_mul_T hT h1
  omega

/-- Strip case for a band point other than `0` and `E`. -/
theorem cover_pt (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) (v p σ0 σE : ℤ) (hv : 1≤v)
    (good : List (Bool × ℤ × ℤ))
    (hstrip : ∀ D : CT, σ0+1-v≤sOf v D+(if D.up then 0 else 1) →
      sOf v D+(if D.up then 0 else 1)≤σ0 → (D.up,sOf v D,D.j%p) ∈ good)
    (Ec : ℤ × ℤ) (hEy : (pos k l Ec).2=σE) (hσE : σE=1 ∨ σE=-1)
    (hd : 2≤k+l-v*l ∨ k+l-v*l≤ -2)
    (hrows : (σ0=0 ∧ Ec.1+v*Ec.2=1) ∨ (σ0=-1 ∧ Ec.1+v*Ec.2=-1))
    (x : Lattice) (hx0 : x≠(0,0)) (hxE : x≠pos k l Ec) (hy : x.2=0 ∨ x.2=σE)
    (h0 : σ0*norm k l≤a k l x+v*b k l x) (h1 : a k l x+v*b k l x≤(σ0+1)*norm k l) :
    ∃ D, InCT k l D x ∧ (D.up,sOf v D,D.j%p) ∈ good := by
  refine cover_main hk hl hprim v p σ0 hv good hstrip x ?_ h0 h1
  intro c hc
  subst hc
  rcases vertex_cases hk hl v σ0 σE Ec c hEy hσE hd hrows h0 h1 hy with h | h
  · exact hx0 h
  · exact hxE (by rw [h])

/-- Exceptional points just below the origin row. -/
theorem cover_four (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) (v p : ℤ)
    (good : List (Bool × ℤ × ℤ))
    (hfour : ∀ (up : Bool) (i : ℤ), (i=0 ∨ i=1) → (up,sOf v ⟨up,i,-1⟩,(-1)%p) ∈ good)
    (x : Lattice) (hnv : ∀ c, x≠pos k l c)
    (ha0 : 0<a k l x) (ha1 : a k l x<2*norm k l) (hb0 : -norm k l<b k l x) (hb1 : b k l x<0) :
    ∃ D, InCT k l D x ∧ (D.up,sOf v D,D.j%p) ∈ good := by
  obtain ⟨D,hD⟩ := inCT_exists hk hl hprim x hnv
  obtain ⟨hj,hi⟩ := pin_four hk hl D x hD ha0 ha1 hb0 hb1
  refine ⟨D,hD,?_⟩
  rcases D with ⟨up,i,j⟩
  simp only at hj hi; subst hj
  exact hfour up i hi

/-- The same, reflected through `E`. -/
theorem cover_four_refl (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) (v p : ℤ)
    (good : List (Bool × ℤ × ℤ)) (Ec : ℤ × ℤ)
    (hfour' : ∀ (up : Bool) (i : ℤ), (i=0 ∨ i=1) →
      ((refl Ec ⟨up,i,-1⟩).up,sOf v (refl Ec ⟨up,i,-1⟩),(refl Ec ⟨up,i,-1⟩).j%p) ∈ good)
    (x : Lattice) (hnv : ∀ c, pos k l Ec-x≠pos k l c)
    (ha0 : 0<a k l (pos k l Ec-x)) (ha1 : a k l (pos k l Ec-x)<2*norm k l)
    (hb0 : -norm k l<b k l (pos k l Ec-x)) (hb1 : b k l (pos k l Ec-x)<0) :
    ∃ D, InCT k l D x ∧ (D.up,sOf v D,D.j%p) ∈ good := by
  obtain ⟨D,hD⟩ := inCT_exists hk hl hprim _ hnv
  obtain ⟨hj,hi⟩ := pin_four hk hl D _ hD ha0 ha1 hb0 hb1
  refine ⟨refl Ec D,by have := (inCT_refl Ec D _).mp hD; rwa [sub_sub_cancel] at this,?_⟩
  rcases D with ⟨up,i,j⟩
  simp only at hj hi; subst hj
  exact hfour' up i hi

theorem a_xy (t y : ℤ) : a k l (t,y)=(k+l)*t+l*y := rfl
theorem b_xy (t y : ℤ) : b k l (t,y)=-l*t+k*y := rfl

theorem sub_xy (A s t y : ℤ) : ((A,s) : Lattice)-(t,y)=(A-t,s-y) := rfl

/-! ## Upper band, `s(E)=1` (no exceptional points) -/

theorem cover_up_pos (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) (v p : ℤ) (hv : 1≤v)
    (good : List (Bool × ℤ × ℤ))
    (hstrip : ∀ D : CT, 0+1-v≤sOf v D+(if D.up then 0 else 1) →
      sOf v D+(if D.up then 0 else 1)≤0 → (D.up,sOf v D,D.j%p) ∈ good)
    (hd : 2≤k+l-v*l) (he : 0<l+v*k)
    (Ec : ℤ × ℤ) (A : ℕ) (hE : pos k l Ec=((A:ℤ),1)) (hsE : Ec.1+v*Ec.2=1) :
    ∀ n, 0<n → n<2*A+1 → ∃ D, InCT k l D (upperP n) ∧ (D.up,sOf v D,D.j%p) ∈ good := by
  have hk : 0<k := by omega
  have hTE : norm k l=(k+l-v*l)*A+(l+v*k) := by
    have := sigma_pos (k:=k) (l:=l) v Ec; rw [hE,sigma_xy,hsE] at this; linarith
  intro n h0 h1
  rcases upper_param A n h0 h1 with ⟨t,hP,t1,t2⟩ | ⟨t,hP,t1,t2⟩ <;> rw [hP] <;>
    refine cover_pt hk hl hprim v p 0 1 hv good hstrip Ec (by rw [hE]) (Or.inl rfl) (Or.inl hd)
      (Or.inl ⟨rfl,hsE⟩) _ ?_ ?_ ?_ ?_ ?_
  · intro h; simp at h; omega
  · rw [hE]; intro h; simp at h
  · simp
  · rw [sigma_xy]; nlinarith
  · rw [sigma_xy]; nlinarith
  · intro h; simp at h
  · rw [hE]; intro h; simp at h; omega
  · simp
  · rw [sigma_xy]; nlinarith
  · rw [sigma_xy]; nlinarith

/-! ## Lower band, `s(E)=-1` (no exceptional points) -/

theorem cover_low_neg (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) (v p : ℤ) (hv : 1≤v)
    (good : List (Bool × ℤ × ℤ))
    (hstrip : ∀ D : CT, -1+1-v≤sOf v D+(if D.up then 0 else 1) →
      sOf v D+(if D.up then 0 else 1)≤ -1 → (D.up,sOf v D,D.j%p) ∈ good)
    (hd : k+l-v*l≤ -2) (he : 0<l+v*k)
    (Ec : ℤ × ℤ) (A : ℕ) (hE : pos k l Ec=((A:ℤ),-1)) (hsE : Ec.1+v*Ec.2=-1) :
    ∀ n, 0<n → n<2*A-1 → ∃ D, InCT k l D (lowerP n) ∧ (D.up,sOf v D,D.j%p) ∈ good := by
  have hk : 0<k := by omega
  have hTE : -norm k l=(k+l-v*l)*A-(l+v*k) := by
    have := sigma_pos (k:=k) (l:=l) v Ec; rw [hE,sigma_xy,hsE] at this; linarith
  intro n h0 h1
  rcases lower_param A n h0 h1 with ⟨t,hP,t1,t2⟩ | ⟨t,hP,t1,t2⟩ <;> rw [hP] <;>
    refine cover_pt hk hl hprim v p (-1) (-1) hv good hstrip Ec (by rw [hE]) (Or.inr rfl)
      (Or.inr hd) (Or.inr ⟨rfl,hsE⟩) _ ?_ ?_ ?_ ?_ ?_
  · intro h; simp at h; omega
  · rw [hE]; intro h; simp at h
  · simp
  · rw [sigma_xy]; nlinarith
  · rw [sigma_xy]; nlinarith
  · intro h; simp at h
  · rw [hE]; intro h; simp at h; omega
  · simp
  · rw [sigma_xy]; nlinarith
  · rw [sigma_xy]; nlinarith

/-! ## Lower band, `s(E)=1` (outer and middle-upper regions with `ε=-1`) -/

theorem cover_low_pos (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) (v p : ℤ) (hv : 1≤v)
    (good : List (Bool × ℤ × ℤ))
    (hstrip : ∀ D : CT, 0+1-v≤sOf v D+(if D.up then 0 else 1) →
      sOf v D+(if D.up then 0 else 1)≤0 → (D.up,sOf v D,D.j%p) ∈ good)
    (Ec : ℤ × ℤ)
    (hfour : ∀ (up : Bool) (i : ℤ), (i=0 ∨ i=1) → (up,sOf v ⟨up,i,-1⟩,(-1)%p) ∈ good)
    (hfour' : ∀ (up : Bool) (i : ℤ), (i=0 ∨ i=1) →
      ((refl Ec ⟨up,i,-1⟩).up,sOf v (refl Ec ⟨up,i,-1⟩),(refl Ec ⟨up,i,-1⟩).j%p) ∈ good)
    (hd : 2≤k+l-v*l) (he : 0<l+v*k) (he' : l+v*k<norm k l)
    (hbd : ∀ x : ℤ, 1≤x → (k+l-v*l)*x<l+v*k → (k+l)*x-l<2*norm k l ∧ l*x+k<norm k l)
    (A : ℕ) (hE : pos k l Ec=((A:ℤ),-1)) (hsE : Ec.1+v*Ec.2=1) :
    ∀ n, 0<n → n<2*A-1 → ∃ D, InCT k l D (lowerP n) ∧ (D.up,sOf v D,D.j%p) ∈ good := by
  have hk : 0<k := by omega
  have hT := norm_pos k l hk hl.le
  have hTE : norm k l=(k+l-v*l)*A-(l+v*k) := by
    have := sigma_pos (k:=k) (l:=l) v Ec; rw [hE,sigma_xy,hsE] at this; linarith
  -- the exceptional points (x,-1) with σ<0
  have exc : ∀ x : ℤ, 1≤x → (k+l-v*l)*x<l+v*k →
      (∀ c, ((x,-1) : Lattice)≠pos k l c) ∧ 0<a k l (x,-1) ∧ a k l (x,-1)<2*norm k l ∧
        -norm k l<b k l (x,-1) ∧ b k l (x,-1)<0 := by
    intro x h1 h2
    obtain ⟨b1,b2⟩ := hbd x h1 h2
    refine ⟨nv_strict hk hl v (-1) _ (by rw [sigma_xy]; nlinarith) (by rw [sigma_xy]; nlinarith),
      ?_,?_,?_,?_⟩ <;> simp only [a_xy,b_xy] <;> nlinarith
  intro n h0 h1
  rcases lower_param A n h0 h1 with ⟨t,hP,t1,t2⟩ | ⟨t,hP,t1,t2⟩ <;> rw [hP]
  · by_cases hs : (k+l-v*l)*t≤norm k l
    · refine cover_pt hk hl hprim v p 0 (-1) hv good hstrip Ec (by rw [hE]) (Or.inr rfl) (Or.inl hd)
        (Or.inl ⟨rfl,hsE⟩) _ ?_ ?_ (by simp) ?_ ?_
      · intro h; simp at h; omega
      · rw [hE]; intro h; simp at h
      · rw [sigma_xy]; nlinarith
      · rw [sigma_xy]; nlinarith
    · obtain ⟨e1,e2,e3,e4,e5⟩ := exc (A-t) (by omega) (by nlinarith)
      have hy : pos k l Ec-((t,0) : Lattice)=((A:ℤ)-t,-1) := by rw [hE]; ext <;> simp
      refine cover_four_refl hk hl hprim v p good Ec hfour' _ ?_ ?_ ?_ ?_ ?_ <;>
        rw [hy] <;> assumption
  · by_cases hs : 0≤(k+l-v*l)*t-(l+v*k)
    · refine cover_pt hk hl hprim v p 0 (-1) hv good hstrip Ec (by rw [hE]) (Or.inr rfl) (Or.inl hd)
        (Or.inl ⟨rfl,hsE⟩) _ ?_ ?_ (by simp) ?_ ?_
      · intro h; simp at h
      · rw [hE]; intro h; simp at h; omega
      · rw [sigma_xy]; nlinarith
      · rw [sigma_xy]; nlinarith
    · obtain ⟨e1,e2,e3,e4,e5⟩ := exc t t1 (by linarith)
      exact cover_four hk hl hprim v p good hfour _ e1 e2 e3 e4 e5

/-! ## Upper band, `s(E)=-1` (middle-lower region with `ε=-1`) -/

theorem cover_up_neg (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) (v p : ℤ) (hv : 1≤v)
    (good : List (Bool × ℤ × ℤ))
    (hstrip : ∀ D : CT, -1+1-v≤sOf v D+(if D.up then 0 else 1) →
      sOf v D+(if D.up then 0 else 1)≤ -1 → (D.up,sOf v D,D.j%p) ∈ good)
    (Ec : ℤ × ℤ)
    (hinit : (true,sOf v ⟨true,0,0⟩,(0:ℤ)%p) ∈ good)
    (hinit' : ((refl Ec ⟨true,0,0⟩).up,sOf v (refl Ec ⟨true,0,0⟩),(refl Ec ⟨true,0,0⟩).j%p) ∈ good)
    (hfour : ∀ (up : Bool) (i : ℤ), (i=0 ∨ i=1) → (up,sOf v ⟨up,i,-1⟩,(-1)%p) ∈ good)
    (hfour' : ∀ (up : Bool) (i : ℤ), (i=0 ∨ i=1) →
      ((refl Ec ⟨up,i,-1⟩).up,sOf v (refl Ec ⟨up,i,-1⟩),(refl Ec ⟨up,i,-1⟩).j%p) ∈ good)
    (hd : k+l-v*l≤ -2) (he : 0<l+v*k) (he' : l+v*k<norm k l) (hsmall : 2*k+l<norm k l)
    (hbd : ∀ x : ℤ, 2≤x → 0<(k+l-v*l)*x+(l+v*k) →
      (k+l)*x+l<2*norm k l ∧ k-l*x<0 ∧ l*x-k<norm k l)
    (A : ℕ) (hE : pos k l Ec=((A:ℤ),1)) (hsE : Ec.1+v*Ec.2=-1) :
    ∀ n, 0<n → n<2*A+1 → ∃ D, InCT k l D (upperP n) ∧ (D.up,sOf v D,D.j%p) ∈ good := by
  have hk : 0<k := by omega
  have hT := norm_pos k l hk hl.le
  have hTE : -norm k l=(k+l-v*l)*A+(l+v*k) := by
    have := sigma_pos (k:=k) (l:=l) v Ec; rw [hE,sigma_xy,hsE] at this; linarith
  -- the exceptional points (x,1) with σ>0
  have exc : ∀ x : ℤ, 0≤x → 0<(k+l-v*l)*x+(l+v*k) → ∃ D, InCT k l D (x,1) ∧
      (D=⟨true,0,0⟩ ∨ (D.j=-1 ∧ (D.i=0 ∨ D.i=1))) := by
    intro x h1 h2
    obtain ⟨D,hD⟩ := inCT_exists hk hl hprim (x,1)
      (nv_strict hk hl v 0 _ (by rw [sigma_xy]; nlinarith) (by rw [sigma_xy]; nlinarith))
    refine ⟨D,hD,?_⟩
    by_cases hx : x≤1
    · left
      exact pin_up00 hk hl D _ hD (by rw [a_xy]; nlinarith) (by rw [b_xy]; nlinarith)
        (by rw [a_xy,b_xy]; nlinarith)
    · right
      obtain ⟨b1,b2,b3⟩ := hbd x (by omega) h2
      exact pin_four hk hl D _ hD (by rw [a_xy]; nlinarith) (by rw [a_xy]; nlinarith)
        (by rw [b_xy]; nlinarith) (by rw [b_xy]; nlinarith)
  intro n h0 h1
  rcases upper_param A n h0 h1 with ⟨t,hP,t1,t2⟩ | ⟨t,hP,t1,t2⟩ <;> rw [hP]
  · by_cases hs : -norm k l≤(k+l-v*l)*t
    · refine cover_pt hk hl hprim v p (-1) 1 hv good hstrip Ec (by rw [hE]) (Or.inl rfl)
        (Or.inr hd) (Or.inr ⟨rfl,hsE⟩) _ ?_ ?_ (by simp) ?_ ?_
      · intro h; simp at h; omega
      · rw [hE]; intro h; simp at h
      · rw [sigma_xy]; nlinarith
      · rw [sigma_xy]; nlinarith
    · obtain ⟨D,hD,hD'⟩ := exc (A-t) (by omega) (by nlinarith)
      have hy : pos k l Ec-((t,0) : Lattice)=((A:ℤ)-t,1) := by rw [hE]; ext <;> simp
      refine ⟨refl Ec D,?_,?_⟩
      · have := (inCT_refl Ec D _).mp hD
        rwa [← hy,sub_sub_cancel] at this
      · rcases hD' with rfl | ⟨hj,hi⟩
        · exact hinit'
        · rcases D with ⟨up,i,j⟩
          simp only at hj hi; subst hj
          exact hfour' up i hi
  · by_cases hs : (k+l-v*l)*t+(l+v*k)≤0
    · refine cover_pt hk hl hprim v p (-1) 1 hv good hstrip Ec (by rw [hE]) (Or.inl rfl)
        (Or.inr hd) (Or.inr ⟨rfl,hsE⟩) _ ?_ ?_ (by simp) ?_ ?_
      · intro h; simp at h
      · rw [hE]; intro h; simp at h; omega
      · rw [sigma_xy]; nlinarith
      · rw [sigma_xy]; nlinarith
    · obtain ⟨D,hD,hD'⟩ := exc t t1 (by linarith)
      refine ⟨D,hD,?_⟩
      rcases hD' with rfl | ⟨hj,hi⟩
      · exact hinit
      · rcases D with ⟨up,i,j⟩
        simp only at hj hi; subst hj
        exact hfour up i hi

end ClaudePos
