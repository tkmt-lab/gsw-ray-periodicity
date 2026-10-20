import Formal.ClaudePosCover2
import Formal.ClaudePosTables

/-!
# Positive side of A3, part 9: the outer region `k ≤ 3l/2`

Written by a Claude worker (2026-10-19). Verifier's notation: `d=k-l ≥ 2`, `k=n d+ε`,
`E=[2n-1,1-n]`, period `V=2z-w`, permutation φ of order 3 (here `v=2`, `p=3`).
-/

namespace ClaudePos
open R002 R002.Icosahedron R002.GCPrimitive R002.GCPrimitiveSurface R002.GCChallengeBridge

variable {k l : ℤ}

theorem goodO_mem (up : Bool) (s c : ℤ) (hc : 0≤c ∧ c<3)
    (h : (up=true ∧ (s=-1 ∨ s=0)) ∨ (up=false ∧ (s=-2 ∨ s=-1 ∨ s=0)) ∨
      (up=true ∧ s=-2 ∧ c=2)) : (up,s,c) ∈ goodO := by
  have : c=0 ∨ c=1 ∨ c=2 := by omega
  rcases this with rfl | rfl | rfl <;>
    rcases h with ⟨rfl,rfl | rfl⟩ | ⟨rfl,rfl | rfl | rfl⟩ | ⟨rfl,rfl,h⟩ <;>
    first | decide | omega

theorem goodO_up (s c : ℤ) (hc : 0≤c ∧ c<3) (h : s=-1 ∨ s=0 ∨ (s=-2 ∧ c=2)) :
    (true,s,c) ∈ goodO :=
  goodO_mem true s c hc (by rcases h with h | h | h <;> simp [h])

theorem goodO_down (s c : ℤ) (hc : 0≤c ∧ c<3) (h : s=-2 ∨ s=-1 ∨ s=0) :
    (false,s,c) ∈ goodO :=
  goodO_mem false s c hc (by simp [h])

theorem labO_ne (c : ℤ) (hc : 0≤c ∧ c<3) : labO 0 0≠labO 1 c := by
  have : c=0 ∨ c=1 ∨ c=2 := by omega
  rcases this with rfl | rfl | rfl <;> decide

theorem pos_outer (n : ℤ) :
    pos k l (2*n-1,1-n)=((2*n-1)*k+(n-1)*l,n*l-(n-1)*k) := by
  ext <;> simp [pos] <;> ring

/-- Outer region: `d=k-l ≥ 2`, `k ≡ ±1 (mod d)`. -/
theorem outer_path (hl : 0<l) (d n : ℤ) (hd : 2≤d) (hn : 2≤n) (hkd : k=l+d)
    (hk : k=n*d+1 ∨ k=n*d-1) (hprim : Primitive k l) :
    ∃ N q, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) N q := by
  have hkl : l<k := by omega
  have hT : norm k l=k*k+k*l+l*l := rfl
  set Ec : ℤ × ℤ := (2*n-1,1-n) with hEc
  have hA0 : 0≤(2*n-1)*k+(n-1)*l := by nlinarith
  set A : ℕ := ((2*n-1)*k+(n-1)*l).toNat with hA
  have hAc : (A : ℤ)=(2*n-1)*k+(n-1)*l := Int.toNat_of_nonneg hA0
  have hA2 : 2≤A := by have : (2:ℤ)≤A := by rw [hAc]; nlinarith
                       omega
  have hstrip : ∀ D : CT, 0+1-2≤sOf 2 D+(if D.up then 0 else 1) →
      sOf 2 D+(if D.up then 0 else 1)≤0 → (D.up,sOf 2 D,D.j%3) ∈ goodO := by
    intro D h1 h2
    cases hD : D.up <;> simp only [hD,ite_true,ite_false,Bool.false_eq_true,sOf] at h1 h2 ⊢
    · exact goodO_down _ _ (by omega) (by omega)
    · exact goodO_up _ _ (by omega) (by omega)
  have hse : SL 2 3 labO (0,0)≠SL 2 3 labO Ec := by
    simp only [SL,hEc]
    rw [show (0:ℤ)+2*0=0 by norm_num,show (0:ℤ)%3=0 by norm_num,
      show 2*n-1+2*(1-n)=1 by ring]
    exact labO_ne _ (by omega)
  rcases hk with hk | hk
  · -- ε=1: upper band
    have hE : pos k l Ec=((A:ℤ),1) := by rw [hEc,pos_outer,hAc]; ext <;> simp <;> nlinarith
    refine upper_path hkl hl hprim 2 3 labO goodO goodO_ok goodO_inj (Or.inl (by nlinarith))
      Ec A (by omega) hE ?_ (by decide) (by decide) ?_ ?_ hse
    · exact cover_up_pos hkl hl hprim 2 3 (by norm_num) goodO hstrip (by nlinarith) (by nlinarith)
        Ec A hE (by simp [hEc]; ring)
    · simp only [refl,sOf,hEc,Bool.not_true,Bool.not_false]
      first | exact goodO_up _ _ (by omega) (by omega) | exact goodO_down _ _ (by omega) (by omega)
    · simp only [refl,sOf,hEc,Bool.not_true,Bool.not_false]
      first | exact goodO_up _ _ (by omega) (by omega) | exact goodO_down _ _ (by omega) (by omega)
  · -- ε=-1: lower band
    have hE : pos k l Ec=((A:ℤ),-1) := by rw [hEc,pos_outer,hAc]; ext <;> simp <;> nlinarith
    refine lower_path hkl hl hprim 2 3 labO goodO goodO_ok goodO_inj (Or.inl (by nlinarith))
      Ec A hA2 hE ?_ (by decide) (by decide) ?_ ?_ hse
    · refine cover_low_pos hkl hl hprim 2 3 (by norm_num) goodO hstrip Ec ?_ ?_ (by nlinarith)
        (by nlinarith) (by nlinarith) ?_ A hE (by simp [hEc]; ring)
      · intro up i hi
        cases up <;> simp only [sOf]
        · exact goodO_down _ _ (by omega) (by omega)
        · exact goodO_up _ _ (by omega) (by omega)
      · intro up i hi
        cases up <;> simp only [refl,sOf,hEc,Bool.not_true,Bool.not_false]
        · exact goodO_up _ _ (by omega) (by omega)
        · exact goodO_down _ _ (by omega) (by omega)
      · intro x h1 h2
        have e : k+l-2*l=d := by omega
        rw [e] at h2
        have h3 : 2*x≤l+2*k-1 := by nlinarith
        have h4 : (k+l)*(2*x)≤(k+l)*(l+2*k-1) := mul_le_mul_of_nonneg_left h3 (by omega)
        have h5 : l*(2*x)≤l*(l+2*k-1) := mul_le_mul_of_nonneg_left h3 (by omega)
        rw [hT]; constructor <;> nlinarith
    · simp only [refl,sOf,hEc,Bool.not_true,Bool.not_false]
      first | exact goodO_up _ _ (by omega) (by omega) | exact goodO_down _ _ (by omega) (by omega)
    · simp only [refl,sOf,hEc,Bool.not_true,Bool.not_false]
      first | exact goodO_up _ _ (by omega) (by omega) | exact goodO_down _ _ (by omega) (by omega)

end ClaudePos
