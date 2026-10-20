import Formal.ClaudePosStrip

/-!
# Positive side of A3, part 5: the two zigzag bands

Written by a Claude worker (2026-10-19), following the verifier's construction
(`.worktrees/verify/studies/R004/a3-positive-remaining-proof.md`, section 1).

* upper band (`σ=1`): `p_(2t)=(t,0)`, `p_(2t+1)=(t,1)`, `0≤t≤A`, `N=2A+2`;
* lower band (`σ=-1`): `p_(2t)=(t,0)`, `p_(2t+1)=(t+1,-1)`, `0≤t≤A-1`, `N=2A`.

`band_core` turns a strip labeling (`SL v p Lab`) whose relevant triangle types are
listed in `good` (checked faces, pairwise different faces) into a literal path, provided
every interior band point lies in a triangle of a good type.
-/

namespace ClaudePos
open R002 R002.Icosahedron R002.GCPrimitive R002.GCPrimitiveSurface R002.GCChallengeBridge
open ClaudeChallenge (rot rotN)

variable {k l : ℤ}

theorem band_core (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (v p : ℤ) (Lab : ℤ → ℤ → Fin 12) (good : List (Bool × ℤ × ℤ))
    (hOK : ∀ t ∈ good, TriOK v p Lab t.1 t.2.1 t.2.2)
    (hInj : ∀ t ∈ good, ∀ t' ∈ good,
      (triF v p Lab t.1 t.2.1 t.2.2).1=(triF v p Lab t'.1 t'.2.1 t'.2.2).1 → t=t')
    (hW : 2≤p*(k+l-v*l) ∨ p*(k+l-v*l)≤ -2)
    (Ec : ℤ × ℤ) (N : ℕ) (P : ℕ → Lattice) (hN : 4≤N) (hEven : Even N)
    (hP0 : P 0=(0,0)) (hrefl : ∀ n, n<N → P (N-1-n)=pos k l Ec-P n)
    (hy : ∀ n m, n<N → m<N → -1≤(P n).2-(P m).2 ∧ (P n).2-(P m).2≤1)
    (hPinj : ∀ n m, n<N → m<N → P n=P m → n=m)
    (hunit : ∀ n m, n<m → m ≤ n+2 → m<N → GCPrimitive.Unit (P n) (P m))
    (hct : ∀ n, 0<n → n<N-1 → ∃ D, InCT k l D (P n) ∧ (D.up,sOf v D,D.j%p) ∈ good)
    (D1 D2 : CT) (m1 m2 : Fin 3) (h1 : InCT k l D1 (P 1)) (h2 : InCT k l D2 (P 2))
    (hv1 : D1.vert m1=(0,0)) (hv2 : D2.vert m2=(0,0))
    (hg1 : (D1.up,sOf v D1,D1.j%p) ∈ good) (hg2 : (D2.up,sOf v D2,D2.j%p) ∈ good)
    (hg1' : ((refl Ec D1).up,sOf v (refl Ec D1),(refl Ec D1).j%p) ∈ good)
    (hg2' : ((refl Ec D2).up,sOf v (refl Ec D2),(refl Ec D2).j%p) ∈ good)
    (hse : SL v p Lab (0,0)≠SL v p Lab Ec) :
    ∃ n q, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) n q := by
  have hk : 0<k := by omega
  set L := SL v p Lab
  have okOf : ∀ D : CT, (D.up,sOf v D,D.j%p) ∈ good → FaceOK L D :=
    fun D hD => faceOK_of_tri v p Lab D (hOK _ hD)
  have hPN : P (N-1)=pos k l Ec := by
    have := hrefl 0 (by omega); rw [Nat.sub_zero,hP0] at this; rw [this]; ext <;> simp
  -- the end triangles
  have h1' : InCT k l (refl Ec D1) (P (N-2)) := by
    rw [show N-2=N-1-1 by omega,hrefl 1 (by omega)]; exact (inCT_refl Ec D1 _).mp h1
  have h2' : InCT k l (refl Ec D2) (P (N-3)) := by
    rw [show N-3=N-1-2 by omega,hrefl 2 (by omega)]; exact (inCT_refl Ec D2 _).mp h2
  obtain ⟨m1',hm1'⟩ := refl_vert Ec D1 m1
  obtain ⟨m2',hm2'⟩ := refl_vert Ec D2 m2
  have hz : Ec-((0,0) : ℤ × ℤ)=Ec := by ext <;> simp
  rw [hv1,hz] at hm1'
  rw [hv2,hz] at hm2'
  refine ⟨N,_,literal_of_ct hkl hl hprim L N P (fr L D1).1 ((fr L D1).2+m1)
    (fr L (refl Ec D1)).1 ((fr L (refl Ec D1)).2+m1') hN hEven ?_ hunit ?_ ?_ ?_ ?_⟩
  · intro n h0 h1
    obtain ⟨D,hD,hg⟩ := hct n h0 h1
    exact ⟨D,hD,okOf D hg⟩
  · intro n m D D' hn0 hn1 hm0 hm1 hD hD' _ _ hf hc
    obtain ⟨D0,hD0,hg0⟩ := hct n hn0 hn1
    obtain ⟨D0',hD0',hg0'⟩ := hct m hm0 hm1
    rw [inCT_unique hk hl _ _ _ hD hD0] at hf hc
    rw [inCT_unique hk hl _ _ _ hD' hD0'] at hf hc
    rw [fr_SL,fr_SL] at hf
    have ht := hInj _ hg0 _ hg0' hf
    simp only [Prod.mk.injEq] at ht
    obtain ⟨m',hm'⟩ := same_type_translate v p Lab D0 D0' (P n) (P m) ht.1 ht.2.1 ht.2.2 hc
    have hy2 := hy m n (by omega) (by omega)
    rw [hm'] at hy2
    simp only [pos,Prod.snd_add,add_sub_cancel_left] at hy2
    have hm0' : m'=0 := by
      rcases lt_trichotomy m' 0 with h | h | h
      · rcases hW with hW | hW <;> nlinarith
      · exact h
      · rcases hW with hW | hW <;> nlinarith
    subst hm0'
    apply hPinj n m (by omega) (by omega)
    rw [hm']; ext <;> simp [pos]
  · intro n hn0 hn2
    have hn : n=1 ∨ n=2 := by omega
    rcases hn with rfl | rfl
    · exact ⟨D1,m1,h1,okOf D1 hg1,by rw [hv1,hP0]; ext <;> simp [pos],
        (okOf D1 hg1 m1).symm⟩
    · refine ⟨D2,m2,h2,okOf D2 hg2,by rw [hv2,hP0]; ext <;> simp [pos],?_⟩
      rw [hv2,← hv1]; exact (okOf D1 hg1 m1).symm
  · intro n hn0 hn2
    have hn : n=N-2 ∨ n=N-3 := by omega
    rcases hn with rfl | rfl
    · refine ⟨refl Ec D1,m1',h1',okOf _ hg1',?_,(okOf _ hg1' m1').symm⟩
      rw [hm1',hPN]
    · refine ⟨refl Ec D2,m2',h2',okOf _ hg2',by rw [hm2',hPN],?_⟩
      have := (okOf _ hg1' m1').symm; rw [hm1'] at this; rw [hm2']; exact this
  · rw [okOf D1 hg1 m1,okOf _ hg1' m1',hv1,hm1']; exact hse

/-! ## The upper band -/

def upperP (n : ℕ) : Lattice := (((n/2 : ℕ) : ℤ),((n%2 : ℕ) : ℤ))

theorem upper_refl (A : ℕ) (n : ℕ) (hn : n<2*A+2) :
    upperP (2*A+2-1-n)=((A:ℤ),1)-upperP n := by
  simp only [upperP]; ext <;> simp <;> omega

theorem upper_unit (n m : ℕ) (h1 : n<m) (h2 : m ≤ n+2) : GCPrimitive.Unit (upperP n) (upperP m) := by
  have : m=n+1 ∨ m=n+2 := by omega
  rcases this with rfl | rfl
  · rcases Nat.mod_two_eq_zero_or_one n with h | h
    · exact ⟨1,by simp only [upperP,direction]; ext <;> simp <;> omega⟩
    · exact ⟨5,by simp only [upperP,direction]; ext <;> simp <;> omega⟩
  · exact ⟨0,by simp only [upperP,direction]; ext <;> simp <;> omega⟩

theorem upper_inj (n m : ℕ) (h : upperP n=upperP m) : n=m := by
  simp only [upperP,Prod.mk.injEq] at h; omega

theorem upper_y (n : ℕ) : (upperP n).2=0 ∨ (upperP n).2=1 := by
  simp only [upperP]; omega

/-! ## The lower band -/

def lowerP (n : ℕ) : Lattice := (((n/2+n%2 : ℕ) : ℤ),-((n%2 : ℕ) : ℤ))

theorem lower_refl (A : ℕ) (n : ℕ) (hn : n<2*A) :
    lowerP (2*A-1-n)=((A:ℤ),-1)-lowerP n := by
  simp only [lowerP]; ext <;> simp <;> omega

theorem lower_unit (n m : ℕ) (h1 : n<m) (h2 : m ≤ n+2) : GCPrimitive.Unit (lowerP n) (lowerP m) := by
  have : m=n+1 ∨ m=n+2 := by omega
  rcases this with rfl | rfl
  · rcases Nat.mod_two_eq_zero_or_one n with h | h
    · exact ⟨5,by simp only [lowerP,direction]; ext <;> simp <;> omega⟩
    · exact ⟨1,by simp only [lowerP,direction]; ext <;> simp <;> omega⟩
  · exact ⟨0,by simp only [lowerP,direction]; ext <;> simp <;> omega⟩

theorem lower_inj (n m : ℕ) (h : lowerP n=lowerP m) : n=m := by
  simp only [lowerP,Prod.mk.injEq] at h; omega

theorem lower_y (n : ℕ) : (lowerP n).2=0 ∨ (lowerP n).2=-1 := by
  simp only [lowerP]; omega

/-! ## Start triangles -/

theorem T_big (hkl : l<k) (hl : 0<l) : k+l<norm k l := by
  simp only [norm]; nlinarith

theorem start_up00 (hkl : l<k) (hl : 0<l) : InCT k l ⟨true,0,0⟩ (0,1) := by
  have := T_big hkl hl
  simp only [InCT,ite_true,a,b]; refine ⟨?_,?_,?_⟩ <;> nlinarith

theorem start_down0m1 (hkl : l<k) (hl : 0<l) : InCT k l ⟨false,0,-1⟩ (1,0) := by
  have := T_big hkl hl
  simp only [InCT,Bool.false_eq_true,ite_false,a,b]; refine ⟨?_,?_,?_⟩ <;> nlinarith

theorem start_up0m1 (hkl : l<k) (hl : 0<l) : InCT k l ⟨true,0,-1⟩ (1,-1) := by
  have := T_big hkl hl
  simp only [InCT,ite_true,a,b]; refine ⟨?_,?_,?_⟩ <;> nlinarith

/-- Literal path from the upper band. -/
theorem upper_path (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (v p : ℤ) (Lab : ℤ → ℤ → Fin 12) (good : List (Bool × ℤ × ℤ))
    (hOK : ∀ t ∈ good, TriOK v p Lab t.1 t.2.1 t.2.2)
    (hInj : ∀ t ∈ good, ∀ t' ∈ good,
      (triF v p Lab t.1 t.2.1 t.2.2).1=(triF v p Lab t'.1 t'.2.1 t'.2.2).1 → t=t')
    (hW : 2≤p*(k+l-v*l) ∨ p*(k+l-v*l)≤ -2)
    (Ec : ℤ × ℤ) (A : ℕ) (hA : 1≤A) (hE : pos k l Ec=((A:ℤ),1))
    (hct : ∀ n, 0<n → n<2*A+1 → ∃ D, InCT k l D (upperP n) ∧ (D.up,sOf v D,D.j%p) ∈ good)
    (hg1 : (true,sOf v ⟨true,0,0⟩,(0:ℤ)%p) ∈ good)
    (hg2 : (false,sOf v ⟨false,0,-1⟩,(-1:ℤ)%p) ∈ good)
    (hg1' : ((refl Ec ⟨true,0,0⟩).up,sOf v (refl Ec ⟨true,0,0⟩),(refl Ec ⟨true,0,0⟩).j%p) ∈ good)
    (hg2' : ((refl Ec ⟨false,0,-1⟩).up,sOf v (refl Ec ⟨false,0,-1⟩),
      (refl Ec ⟨false,0,-1⟩).j%p) ∈ good)
    (hse : SL v p Lab (0,0)≠SL v p Lab Ec) :
    ∃ n q, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) n q := by
  refine band_core hkl hl hprim v p Lab good hOK hInj hW Ec (2*A+2) upperP (by omega)
    ⟨A+1,by ring⟩ (by simp [upperP]) (fun n hn => by rw [upper_refl A n hn,hE]) ?_
    (fun n m _ _ h => upper_inj n m h) (fun n m h1 h2 _ => upper_unit n m h1 h2)
    (fun n h0 h1 => hct n h0 (by omega)) ⟨true,0,0⟩ ⟨false,0,-1⟩ 0 2
    (start_up00 hkl hl) (start_down0m1 hkl hl) (by simp [CT.vert]) (by simp [CT.vert])
    hg1 hg2 hg1' hg2' hse
  intro n m _ _
  rcases upper_y n with h | h <;> rcases upper_y m with h' | h' <;> rw [h,h'] <;> norm_num

/-- Literal path from the lower band. -/
theorem lower_path (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (v p : ℤ) (Lab : ℤ → ℤ → Fin 12) (good : List (Bool × ℤ × ℤ))
    (hOK : ∀ t ∈ good, TriOK v p Lab t.1 t.2.1 t.2.2)
    (hInj : ∀ t ∈ good, ∀ t' ∈ good,
      (triF v p Lab t.1 t.2.1 t.2.2).1=(triF v p Lab t'.1 t'.2.1 t'.2.2).1 → t=t')
    (hW : 2≤p*(k+l-v*l) ∨ p*(k+l-v*l)≤ -2)
    (Ec : ℤ × ℤ) (A : ℕ) (hA : 2≤A) (hE : pos k l Ec=((A:ℤ),-1))
    (hct : ∀ n, 0<n → n<2*A-1 → ∃ D, InCT k l D (lowerP n) ∧ (D.up,sOf v D,D.j%p) ∈ good)
    (hg1 : (true,sOf v ⟨true,0,-1⟩,(-1:ℤ)%p) ∈ good)
    (hg2 : (false,sOf v ⟨false,0,-1⟩,(-1:ℤ)%p) ∈ good)
    (hg1' : ((refl Ec ⟨true,0,-1⟩).up,sOf v (refl Ec ⟨true,0,-1⟩),(refl Ec ⟨true,0,-1⟩).j%p) ∈ good)
    (hg2' : ((refl Ec ⟨false,0,-1⟩).up,sOf v (refl Ec ⟨false,0,-1⟩),
      (refl Ec ⟨false,0,-1⟩).j%p) ∈ good)
    (hse : SL v p Lab (0,0)≠SL v p Lab Ec) :
    ∃ n q, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) n q := by
  refine band_core hkl hl hprim v p Lab good hOK hInj hW Ec (2*A) lowerP (by omega)
    ⟨A,by ring⟩ (by simp [lowerP]) (fun n hn => by rw [lower_refl A n hn,hE]) ?_
    (fun n m _ _ h => lower_inj n m h) (fun n m h1 h2 _ => lower_unit n m h1 h2)
    (fun n h0 h1 => hct n h0 (by omega)) ⟨true,0,-1⟩ ⟨false,0,-1⟩ 2 2
    (start_up0m1 hkl hl) (start_down0m1 hkl hl) (by simp [CT.vert]) (by simp [CT.vert])
    hg1 hg2 hg1' hg2' hse
  intro n m _ _
  rcases lower_y n with h | h <;> rcases lower_y m with h' | h' <;> rw [h,h'] <;> norm_num

end ClaudePos
