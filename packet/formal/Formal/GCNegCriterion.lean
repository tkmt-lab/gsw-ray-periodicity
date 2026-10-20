import Formal.GCNegCompFinal
import Formal.GCNegNearFinal
import Formal.GCSectorCriterion

namespace R002.GCNeg
open GCPrimitive GCSector

def Rule (k m : ℕ) : Prop := m=1 ∨
  (2≤m ∧ 3≤k/m ∧ (k%m=1 ∨ k%m=m-1)) ∨
  (2≤m ∧ k/m=2 ∧ (k-2*m=1 ∨ m%(k-2*m)=1 ∨ m%(k-2*m)=k-2*m-1))

theorem interior_residue (n d : ℕ) (hd : 0<d) (hd1 : d≠1) (hg : Nat.gcd n d=1)
    (h1 : n%d≠1) (hlast : n%d≠d-1) : 2≤n%d ∧ n%d≤d-2 := by
  have hs := Nat.mod_lt n hd
  have hz : n%d≠0 := by
    intro he
    have hdiv := Nat.dvd_of_mod_eq_zero he
    have hh : Nat.gcd n d=d := Nat.gcd_eq_right_iff_dvd.mpr hdiv
    omega
  omega

theorem large_no_path (k l m : ℕ) (hkl : l<k) (hl : 0<l) (hg : Nat.gcd k l=1)
    (hm : m=l ∨ m=k-l) (hmpos : 0<m) (hq : 3≤k/m)
    (hs : 2≤k%m ∧ k%m≤m-2) :
    ¬∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) n p := by
  let P : Parameters := ⟨k/m,m,k%m,by exact_mod_cast hq,by exact_mod_cast hs.1,by omega⟩
  have heK : P.k=(k:ℤ) := by
    dsimp [P,Parameters.k]
    exact_mod_cast (show k/m*m+k%m=k by nlinarith [Nat.mod_add_div k m])
  rcases hm with hm|hm
  · have heL : P.l=(l:ℤ) := by dsimp [P]; omega
    have hprim : Primitive P.k P.l := by rw [heK,heL]; simpa [Primitive] using hg
    have hh := GCSector.no_challenge_path P hprim
    rw [heK,heL] at hh
    exact hh
  · have heL : compL P=(l:ℤ) := by dsimp [compL]; rw [heK]; dsimp [P]; omega
    have hprim : Primitive P.k (compL P) := by rw [heK,heL]; simpa [Primitive] using hg
    have hh := comp_no_challenge_path P hprim
    rw [heK,heL] at hh
    exact hh

theorem double_no_path (k l m r : ℕ) (hkl : l<k) (hl : 0<l) (hg : Nat.gcd k l=1)
    (hm : m=l ∨ m=k-l) (h2 : 2*m≤k) (hr : r=k-2*m) (hrpos : 0<r) (hrm : r<m)
    (hs : 2≤m%r ∧ m%r≤r-2) :
    ¬∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) n p := by
  have ha : 1≤m/r := (Nat.le_div_iff_mul_le hrpos).mpr (by omega)
  rcases hm with hm|hm
  · let P : TailParameters := ⟨m/r,r,m%r,by exact_mod_cast ha,by exact_mod_cast hs.1,by omega⟩
    have hLm : P.l=(m:ℤ) := by
      dsimp [P,TailParameters.l]
      exact_mod_cast (show m/r*r+m%r=m by nlinarith [Nat.mod_add_div m r])
    have hL : P.l=(l:ℤ) := by rw [hLm]; omega
    have hK : plusK P=(k:ℤ) := by dsimp [plusK]; rw [hLm]; dsimp [P]; omega
    have hp : Primitive (plusK P) P.l := by rw [hK,hL]; simpa [Primitive] using hg
    have hh := plus_no_challenge_path P hp
    rw [hK,hL] at hh
    exact hh
  · let P : TailParameters := ⟨((m/r:ℕ):ℤ)+1,r,m%r,by exact_mod_cast (show 1≤m/r+1 by omega),by exact_mod_cast hs.1,by omega⟩
    have ha2 : 2≤P.a := by dsimp [P]; omega
    have hLm : P.l=((m+r:ℕ):ℤ) := by
      dsimp [P,TailParameters.l]
      push_cast
      exact_mod_cast (show (m/r+1)*r+m%r=m+r by nlinarith [Nat.mod_add_div m r])
    have hL : P.l=(l:ℤ) := by rw [hLm]; omega
    have hK : minusK P=(k:ℤ) := by dsimp [minusK]; rw [hL]; dsimp [P]; omega
    have hp : Primitive (minusK P) P.l := by rw [hK,hL]; simpa [Primitive] using hg
    have hh := minus_no_challenge_path P ha2 hp
    rw [hK,hL] at hh
    exact hh

/-- Complete necessity in the primitive domain; no positive construction is used. -/
theorem primitive_criterion_necessary (k l : ℕ) (hkl : l<k) (hl : 0<l) (hg : Nat.gcd k l=1)
    (hp : ∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) n p) :
    ClaudeChallenge.criterion k l := by
  by_contra hc
  let m := min l (k-l)
  have hmpos : 0<m := by dsimp [m]; omega
  have hm : m=l ∨ m=k-l := by dsimp [m]; omega
  have h2 : 2*m≤k := by dsimp [m]; omega
  have hgm : Nat.gcd k m=1 := by
    rcases hm with hm|hm
    · rwa [hm]
    · rw [hm,Nat.gcd_self_sub_right (by omega)]; exact hg
  have hn : ¬Rule k m := by simpa only [ClaudeChallenge.criterion,hg,true_and,Rule,m] using hc
  have hm1 : m≠1 := fun he => hn (Or.inl he)
  have hm2 : 2≤m := by omega
  have hq2 : 2≤k/m := (Nat.le_div_iff_mul_le hmpos).mpr h2
  by_cases hq : 3≤k/m
  · have h1 : k%m≠1 := fun he => hn (Or.inr (Or.inl ⟨hm2,hq,Or.inl he⟩))
    have hlast : k%m≠m-1 := fun he => hn (Or.inr (Or.inl ⟨hm2,hq,Or.inr he⟩))
    exact large_no_path k l m hkl hl hg hm hmpos hq (interior_residue k m hmpos hm1 hgm h1 hlast) hp
  · have hq : k/m=2 := by omega
    let r := k-2*m
    have hgr : Nat.gcd m r=1 := by
      dsimp [r]
      rw [Nat.gcd_sub_mul_right_right h2,Nat.gcd_comm]
      exact hgm
    have hbad : ¬(r=1 ∨ m%r=1 ∨ m%r=r-1) := fun he => hn (Or.inr (Or.inr ⟨hm2,hq,he⟩))
    have hr0 : r≠0 := by intro he; rw [he,Nat.gcd_zero_right] at hgr; omega
    have hr1 : r≠1 := fun he => hbad (Or.inl he)
    have hrpos : 0<r := by omega
    have hrm : r<m := by
      have hh := Nat.mod_add_div k m
      have hmod := Nat.mod_lt k hmpos
      rw [hq] at hh
      dsimp [r]; omega
    have hs := interior_residue m r hrpos hr1 hgr
      (fun he => hbad (Or.inr (Or.inl he))) (fun he => hbad (Or.inr (Or.inr he)))
    exact double_no_path k l m r hkl hl hg hm h2 rfl hrpos hrm hs hp

theorem primitive_negative (k l : ℕ) (hkl : l<k) (hl : 0<l) (hg : Nat.gcd k l=1)
    (hc : ¬ClaudeChallenge.criterion k l) :
    ¬∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) n p :=
  fun hp => hc (primitive_criterion_necessary k l hkl hl hg hp)

end R002.GCNeg
