import Formal.ClaudePosCover2
import Formal.ClaudePosTables

/-!
# Positive side of A3, part 10: the two middle regions

Written by a Claude worker (2026-10-19).
* middle-upper `2l<k<3l`: `d=k-2l ≥ 2`, `l=n d+ε`, `E=[3n+1,-n]`, `V=3z-w`, ψ of order 2;
* middle-lower `3l/2<k<2l`: `d=2l-k ≥ 2`, `l=n d+ε`, `E=[3n-1,-n]`, `V=3z-w`, χ of order 2.
(`v=3`, `p=2` in both.)
-/

namespace ClaudePos
open R002 R002.Icosahedron R002.GCPrimitive R002.GCPrimitiveSurface R002.GCChallengeBridge

variable {k l : ℤ}

theorem goodU_up (s c : ℤ) (hc : 0≤c ∧ c<2) (h : s=-2 ∨ s=-1 ∨ s=0 ∨ (s=-3 ∧ c=1)) :
    (true,s,c) ∈ goodU := by
  have : c=0 ∨ c=1 := by omega
  rcases this with rfl | rfl <;> rcases h with rfl | rfl | rfl | ⟨rfl,h⟩ <;> first | decide | omega

theorem goodU_down (s c : ℤ) (hc : 0≤c ∧ c<2) (h : s=-3 ∨ s=-2 ∨ s=-1 ∨ s=0) :
    (false,s,c) ∈ goodU := by
  have : c=0 ∨ c=1 := by omega
  rcases this with rfl | rfl <;> rcases h with rfl | rfl | rfl | rfl <;> decide

theorem goodL_up (s c : ℤ) (hc : 0≤c ∧ c<2) (h : s=-3 ∨ s=-2 ∨ s=-1 ∨ (s=0 ∧ c=0)) :
    (true,s,c) ∈ goodL := by
  have : c=0 ∨ c=1 := by omega
  rcases this with rfl | rfl <;> rcases h with rfl | rfl | rfl | ⟨rfl,h⟩ <;> first | decide | omega

theorem goodL_down (s c : ℤ) (hc : 0≤c ∧ c<2) (h : s=-5 ∨ s=-4 ∨ s=-3 ∨ s=-2) :
    (false,s,c) ∈ goodL := by
  have : c=0 ∨ c=1 := by omega
  rcases this with rfl | rfl <;> rcases h with rfl | rfl | rfl | rfl <;> decide

theorem labU_ne (c : ℤ) (hc : 0≤c ∧ c<2) : labU 0 0≠labU 1 c := by
  have : c=0 ∨ c=1 := by omega
  rcases this with rfl | rfl <;> decide

theorem labL_ne (c : ℤ) (hc : 0≤c ∧ c<2) : labL 0 0≠labL (-1) c := by
  have : c=0 ∨ c=1 := by omega
  rcases this with rfl | rfl <;> decide

theorem pos_mid (m n : ℤ) : pos k l (m,-n)=(m*k+n*l,m*l-n*(k+l)) := by
  ext <;> simp [pos] <;> ring

/-- Middle-upper region: `d=k-2l ≥ 2`, `l ≡ ±1 (mod d)`. -/
theorem upper_mid_path (hl : 0<l) (d n : ℤ) (hd : 2≤d) (hn : 1≤n) (hkd : k=2*l+d)
    (hlε : l=n*d+1 ∨ l=n*d-1) (hprim : Primitive k l) :
    ∃ N q, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) N q := by
  have hkl : l<k := by omega
  have hT : norm k l=k*k+k*l+l*l := rfl
  set Ec : ℤ × ℤ := (3*n+1,-n) with hEc
  have hA0 : 0≤(3*n+1)*k+n*l := by nlinarith
  set A : ℕ := ((3*n+1)*k+n*l).toNat with hA
  have hAc : (A : ℤ)=(3*n+1)*k+n*l := Int.toNat_of_nonneg hA0
  have hA2 : 2≤A := by have : (2:ℤ)≤A := by rw [hAc]; nlinarith
                       omega
  have hstrip : ∀ D : CT, 0+1-3≤sOf 3 D+(if D.up then 0 else 1) →
      sOf 3 D+(if D.up then 0 else 1)≤0 → (D.up,sOf 3 D,D.j%2) ∈ goodU := by
    intro D h1 h2
    cases hD : D.up <;> simp only [hD,ite_true,ite_false,Bool.false_eq_true,sOf] at h1 h2 ⊢
    · exact goodU_down _ _ (by omega) (by omega)
    · exact goodU_up _ _ (by omega) (by omega)
  have hse : SL 3 2 labU (0,0)≠SL 3 2 labU Ec := by
    simp only [SL,hEc]
    rw [show (0:ℤ)+3*0=0 by norm_num,show (0:ℤ)%2=0 by norm_num,show 3*n+1+3*(-n)=1 by ring]
    exact labU_ne _ (by omega)
  have hpos : pos k l Ec=((A:ℤ),(2*n+1)*l-n*k) := by
    rw [hEc,pos_mid,hAc]; ext <;> simp <;> ring
  rcases hlε with hlε | hlε
  · -- ε=1: upper band
    have hE : pos k l Ec=((A:ℤ),1) := by rw [hpos]; ext <;> simp <;> nlinarith
    refine upper_path hkl hl hprim 3 2 labU goodU goodU_ok goodU_inj (Or.inl (by nlinarith))
      Ec A (by omega) hE ?_ (by decide) (by decide) ?_ ?_ hse
    · exact cover_up_pos hkl hl hprim 3 2 (by norm_num) goodU hstrip (by nlinarith) (by nlinarith)
        Ec A hE (by simp [hEc])
    · simp only [refl,sOf,hEc,Bool.not_true,Bool.not_false]
      exact goodU_down _ _ (by omega) (by omega)
    · simp only [refl,sOf,hEc,Bool.not_true,Bool.not_false]
      exact goodU_up _ _ (by omega) (by omega)
  · -- ε=-1: lower band
    have hE : pos k l Ec=((A:ℤ),-1) := by rw [hpos]; ext <;> simp <;> nlinarith
    refine lower_path hkl hl hprim 3 2 labU goodU goodU_ok goodU_inj (Or.inl (by nlinarith))
      Ec A hA2 hE ?_ (by decide) (by decide) ?_ ?_ hse
    · refine cover_low_pos hkl hl hprim 3 2 (by norm_num) goodU hstrip Ec ?_ ?_ (by nlinarith)
        (by nlinarith) (by nlinarith) ?_ A hE (by simp [hEc])
      · intro up i hi
        cases up <;> simp only [sOf]
        · exact goodU_down _ _ (by omega) (by omega)
        · exact goodU_up _ _ (by omega) (by omega)
      · intro up i hi
        cases up <;> simp only [refl,sOf,hEc,Bool.not_true,Bool.not_false]
        · exact goodU_up _ _ (by omega) (by omega)
        · exact goodU_down _ _ (by omega) (by omega)
      · intro x h1 h2
        have e : k+l-3*l=d := by omega
        rw [e] at h2
        have h3 : 2*x≤l+3*k-1 := by nlinarith
        have h4 : (k+l)*(2*x)≤(k+l)*(l+3*k-1) := mul_le_mul_of_nonneg_left h3 (by omega)
        have h5 : l*(2*x)≤l*(l+3*k-1) := mul_le_mul_of_nonneg_left h3 (by omega)
        rw [hT]; constructor <;> nlinarith
    · simp only [refl,sOf,hEc,Bool.not_true,Bool.not_false]
      exact goodU_down _ _ (by omega) (by omega)
    · simp only [refl,sOf,hEc,Bool.not_true,Bool.not_false]
      exact goodU_up _ _ (by omega) (by omega)

/-- Middle-lower region: `d=2l-k ≥ 2`, `l ≡ ±1 (mod d)`. -/
theorem lower_mid_path (hl : 0<l) (hkl : l<k) (d n : ℤ) (hd : 2≤d) (hn : 1≤n) (hkd : k=2*l-d)
    (hlε : l=n*d+1 ∨ l=n*d-1) (hprim : Primitive k l) :
    ∃ N q, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) N q := by
  have hT : norm k l=k*k+k*l+l*l := rfl
  set Ec : ℤ × ℤ := (3*n-1,-n) with hEc
  have hA0 : 0≤(3*n-1)*k+n*l := by nlinarith
  set A : ℕ := ((3*n-1)*k+n*l).toNat with hA
  have hAc : (A : ℤ)=(3*n-1)*k+n*l := Int.toNat_of_nonneg hA0
  have hA2 : 2≤A := by have : (2:ℤ)≤A := by rw [hAc]; nlinarith
                       omega
  have hse : SL 3 2 labL (0,0)≠SL 3 2 labL Ec := by
    simp only [SL,hEc]
    rw [show (0:ℤ)+3*0=0 by norm_num,show (0:ℤ)%2=0 by norm_num,show 3*n-1+3*(-n)=-1 by ring]
    exact labL_ne _ (by omega)
  have hpos : pos k l Ec=((A:ℤ),(2*n-1)*l-n*k) := by
    rw [hEc,pos_mid,hAc]; ext <;> simp <;> ring
  rcases hlε with hlε | hlε
  · -- ε=1: lower band, s(E)=-1
    have hstrip : ∀ D : CT, -1+1-3≤sOf 3 D+(if D.up then 0 else 1) →
        sOf 3 D+(if D.up then 0 else 1)≤ -1 → (D.up,sOf 3 D,D.j%2) ∈ goodL := by
      intro D h1 h2
      cases hD : D.up <;> simp only [hD,ite_true,ite_false,Bool.false_eq_true,sOf] at h1 h2 ⊢
      · exact goodL_down _ _ (by omega) (by omega)
      · exact goodL_up _ _ (by omega) (by omega)
    have hE : pos k l Ec=((A:ℤ),-1) := by rw [hpos]; ext <;> simp <;> nlinarith
    refine lower_path hkl hl hprim 3 2 labL goodL goodL_ok goodL_inj (Or.inr (by nlinarith))
      Ec A hA2 hE ?_ (by decide) (by decide) ?_ ?_ hse
    · exact cover_low_neg hkl hl hprim 3 2 (by norm_num) goodL hstrip (by nlinarith) (by nlinarith)
        Ec A hE (by simp [hEc]; ring)
    · simp only [refl,sOf,hEc,Bool.not_true,Bool.not_false]
      exact goodL_down _ _ (by omega) (by omega)
    · simp only [refl,sOf,hEc,Bool.not_true,Bool.not_false]
      exact goodL_up _ _ (by omega) (by omega)
  · -- ε=-1: upper band, s(E)=-1
    have hstrip : ∀ D : CT, -1+1-3≤sOf 3 D+(if D.up then 0 else 1) →
        sOf 3 D+(if D.up then 0 else 1)≤ -1 → (D.up,sOf 3 D,D.j%2) ∈ goodL := by
      intro D h1 h2
      cases hD : D.up <;> simp only [hD,ite_true,ite_false,Bool.false_eq_true,sOf] at h1 h2 ⊢
      · exact goodL_down _ _ (by omega) (by omega)
      · exact goodL_up _ _ (by omega) (by omega)
    have hE : pos k l Ec=((A:ℤ),1) := by rw [hpos]; ext <;> simp <;> nlinarith
    refine upper_path hkl hl hprim 3 2 labL goodL goodL_ok goodL_inj (Or.inr (by nlinarith))
      Ec A (by omega) hE ?_ (by decide) (by decide) ?_ ?_ hse
    · refine cover_up_neg hkl hl hprim 3 2 (by norm_num) goodL hstrip Ec (by decide) ?_ ?_ ?_
        (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith) ?_ A hE (by simp [hEc]; ring)
      · simp only [refl,sOf,hEc,Bool.not_true,Bool.not_false]
        exact goodL_down _ _ (by omega) (by omega)
      · intro up i hi
        cases up <;> simp only [sOf]
        · exact goodL_down _ _ (by omega) (by omega)
        · exact goodL_up _ _ (by omega) (by omega)
      · intro up i hi
        cases up <;> simp only [refl,sOf,hEc,Bool.not_true,Bool.not_false]
        · exact goodL_up _ _ (by omega) (by omega)
        · exact goodL_down _ _ (by omega) (by omega)
      · intro x h1 h2
        have e : k+l-3*l=-d := by omega
        rw [e] at h2
        have h3 : 2*x≤l+3*k-1 := by nlinarith
        have h4 : (k+l)*(2*x)≤(k+l)*(l+3*k-1) := mul_le_mul_of_nonneg_left h3 (by omega)
        have h5 : l*(2*x)≤l*(l+3*k-1) := mul_le_mul_of_nonneg_left h3 (by omega)
        rw [hT]; refine ⟨?_,?_,?_⟩ <;> nlinarith
    · simp only [refl,sOf,hEc,Bool.not_true,Bool.not_false]
      exact goodL_down _ _ (by omega) (by omega)
    · simp only [refl,sOf,hEc,Bool.not_true,Bool.not_false]
      exact goodL_up _ _ (by omega) (by omega)

end ClaudePos
