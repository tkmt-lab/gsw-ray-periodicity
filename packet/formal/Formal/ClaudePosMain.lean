import Formal.ClaudePosOuter
import Formal.ClaudePosMiddle
import Formal.ClaudeBeltMain
import Mathlib.Tactic.LinearCombination

/-!
# Positive side of A3, part 11: sufficiency of the two-stage rule

Written by a Claude worker (2026-10-19), following section 5 of the verifier's proof.
For `k>l≥1`, `ClaudeChallenge.criterion k l` implies a literal path in
`ClaudeChallenge.gcGraph k l`. With `m=min(l,k-l)`:

* `m=1`, or `m=l` with `k/l ≥ 3`, or `k/m=2` with `r=1`: belt (`ClaudeBelt.belt_literal_path`);
* `m=k-l` with `k/m ≥ 3` (so `k ≤ 3l/2`): outer region (`outer_path`, `d=m`);
* `m=l`, `k/l=2`, `r=k-2l ≥ 2`: middle-upper region (`upper_mid_path`, `d=r`);
* `m=k-l`, `k/m=2`, `r=2l-k ≥ 2`: middle-lower region (`lower_mid_path`, `d=r`).
-/

namespace ClaudePos
open R002 R002.GCPrimitive

theorem prim_nat (k l : ℕ) (h : Nat.gcd k l=1) : Primitive (k:ℤ) (l:ℤ) := by
  simp only [Primitive,Int.gcd_natCast_natCast,h]

/-- Remainder `±1` as an integer identity. -/
theorem pm_one (k m : ℕ) (hm : 2≤m) (hr : k%m=1 ∨ k%m=m-1) :
    ((k:ℤ)=((k/m : ℕ):ℤ)*m+1) ∨ ((k:ℤ)=(((k/m : ℕ):ℤ)+1)*m-1) := by
  have hdiv := Nat.div_add_mod k m
  generalize k/m=Q at hdiv ⊢
  rcases hr with hr | hr
  · left
    rw [hr] at hdiv
    have : (((m*Q+1 : ℕ)) : ℤ)=k := by rw [hdiv]
    push_cast at this; linarith
  · right
    rw [hr] at hdiv
    have : (((m*Q+(m-1) : ℕ)) : ℤ)=k := by rw [hdiv]
    push_cast [Nat.cast_sub (show 1≤m by omega)] at this; linarith

theorem not_double (l : ℕ) (hl : 2≤l) (hg : Nat.gcd (2*l) l=1) : False := by
  rw [Nat.gcd_mul_left_left] at hg; omega

/-- **Sufficiency of the classification rule** on the independent challenge graph. -/
theorem criterion_sufficient (k l : ℕ) (hl : 1≤l) (hkl : l<k) (h : ClaudeChallenge.criterion k l) :
    ∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph (k:ℤ) (l:ℤ)) n p := by
  obtain ⟨hg,hc⟩ := h
  have hprim := prim_nat k l hg
  have hl' : (0:ℤ)<l := by exact_mod_cast hl
  have hkl' : (l:ℤ)<k := by exact_mod_cast hkl
  have belt : ∀ q : ℤ, ((k:ℤ)=q*l+1 ∨ (k:ℤ)=q*l-1) →
      ∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph (k:ℤ) (l:ℤ)) n p :=
    fun q hq => ClaudeBelt.belt_literal_path (k:ℤ) (l:ℤ) hl' hkl' hprim
      (hq.imp (fun h => ⟨q,h⟩) (fun h => ⟨q,h⟩))
  dsimp only at hc
  rcases le_total l (k-l) with hle | hle
  · -- m = l
    rw [min_eq_left hle] at hc
    rcases hc with h1 | ⟨h2,hq,hr⟩ | ⟨h2,hq,hr⟩
    · subst h1; exact belt ((k:ℤ)-1) (Or.inl (by ring))
    · rcases pm_one k l h2 hr with e | e
      · exact belt _ (Or.inl e)
      · exact belt _ (Or.inr e)
    · have hk3 : k<3*l := by
        have := Nat.lt_div_mul_add (a:=k) (b:=l) (by omega); rw [hq] at this; linarith
      have hk2 : 2*l≤k := by have := Nat.div_mul_le_self k l; rw [hq] at this; linarith
      by_cases hr1 : k-2*l=1
      · exact belt 2 (Or.inl (by omega))
      by_cases hr0 : k-2*l=0
      · exact (not_double l h2 (by rw [show 2*l=k by omega]; exact hg)).elim
      have hr' : l%(k-2*l)=1 ∨ l%(k-2*l)=(k-2*l)-1 := by omega
      have hn1 : 1≤l/(k-2*l) := (Nat.one_le_div_iff (by omega)).mpr (by omega)
      rcases pm_one l (k-2*l) (by omega) hr' with e | e
      · exact upper_mid_path hl' ((k-2*l : ℕ):ℤ) ((l/(k-2*l) : ℕ):ℤ) (by omega) (by omega)
          (by omega) (Or.inl e) hprim
      · exact upper_mid_path hl' ((k-2*l : ℕ):ℤ) (((l/(k-2*l) : ℕ):ℤ)+1) (by omega) (by omega)
          (by omega) (Or.inr e) hprim
  · -- m = k-l
    rw [min_eq_right hle] at hc
    rcases hc with h1 | ⟨h2,hq,hr⟩ | ⟨h2,hq,hr⟩
    · exact belt 1 (Or.inl (by omega))
    · rcases pm_one k (k-l) h2 hr with e | e
      · exact outer_path hl' ((k-l : ℕ):ℤ) ((k/(k-l) : ℕ):ℤ) (by omega) (by omega) (by omega)
          (Or.inl e) hprim
      · exact outer_path hl' ((k-l : ℕ):ℤ) (((k/(k-l) : ℕ):ℤ)+1) (by omega) (by omega) (by omega)
          (Or.inr e) hprim
    · have hk3 : k<3*(k-l) := by
        have := Nat.lt_div_mul_add (a:=k) (b:=k-l) (by omega); rw [hq] at this; linarith
      have hk2 : 2*(k-l)≤k := by have := Nat.div_mul_le_self k (k-l); rw [hq] at this; linarith
      by_cases hr1 : k-2*(k-l)=1
      · exact belt 2 (Or.inr (by omega))
      by_cases hr0 : k-2*(k-l)=0
      · exact (not_double l (by omega) (by rw [show 2*l=k by omega]; exact hg)).elim
      set r := k-2*(k-l) with hrdef
      set m := k-l with hmdef
      have hr' : m%r=1 ∨ m%r=r-1 := by omega
      have hm : (m:ℤ)=(l:ℤ)-(r:ℤ) := by omega
      rcases pm_one m r (by omega) hr' with e | e <;> generalize m/r=Q at e
      · exact lower_mid_path hl' hkl' (r:ℤ) ((Q:ℤ)+1) (by omega) (by omega) (by omega)
          (Or.inl (by linear_combination e-hm)) hprim
      · exact lower_mid_path hl' hkl' (r:ℤ) ((Q:ℤ)+2) (by omega) (by omega) (by omega)
          (Or.inr (by linear_combination e-hm)) hprim

end ClaudePos

#print axioms ClaudePos.criterion_sufficient
#print axioms ClaudePos.outer_path
#print axioms ClaudePos.upper_mid_path
#print axioms ClaudePos.lower_mid_path
