import Formal.GCSectorNegative

/-! The proved first sector covers every primitive negative criterion with k≥3l. -/
namespace R002.GCSector
open GCPrimitive

theorem negative_residue (k l : ℕ) (hl : 0<l) (hk : 3*l≤k) (hg : Nat.gcd k l=1)
    (hn : ¬ClaudeChallenge.criterion k l) : 3≤k/l ∧ 2≤k%l ∧ k%l≤l-2 := by
  have hm : min l (k-l)=l := by omega
  have hq : 3≤k/l := (Nat.le_div_iff_mul_le hl).mpr hk
  have hs : k%l<l := Nat.mod_lt k hl
  have hn' : ¬(l=1 ∨ (2≤l ∧ 3≤k/l ∧ (k%l=1 ∨ k%l=l-1)) ∨
      (2≤l ∧ k/l=2 ∧ (k-2*l=1 ∨ l%(k-2*l)=1 ∨ l%(k-2*l)=k-2*l-1))) := by
    simpa [ClaudeChallenge.criterion,hg,hm] using hn
  have hl1 : l≠1 := fun h => hn' (Or.inl h)
  have hs0 : k%l≠0 := by
    intro hz
    have hd : l∣k := Nat.dvd_of_mod_eq_zero hz
    have he : Nat.gcd k l=l := Nat.gcd_eq_right_iff_dvd.mpr hd
    omega
  have hs1 : k%l≠1 := fun h => hn' (Or.inr (Or.inl ⟨by omega,hq,Or.inl h⟩))
  have hsl : k%l≠l-1 := fun h => hn' (Or.inr (Or.inl ⟨by omega,hq,Or.inr h⟩))
  exact ⟨hq,by omega,by omega⟩

/-- This implication uses the independent literal-path definition and no classification assumption. -/
theorem criterion_necessary_ge_three (k l : ℕ) (hl : 0<l) (hk : 3*l≤k)
    (hg : Nat.gcd k l=1)
    (hp : ∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) n p) :
    ClaudeChallenge.criterion k l := by
  by_contra hn
  have h := negative_residue k l hl hk hg hn
  let P : Parameters := ⟨k/l,l,k%l,by exact_mod_cast h.1,by exact_mod_cast h.2.1,by omega⟩
  have he : P.k=(k:ℤ) := by
    dsimp [P,Parameters.k]
    exact_mod_cast (show k/l*l+k%l=k by nlinarith [Nat.mod_add_div k l])
  have hprim : Primitive P.k P.l := by
    rw [he]
    simpa [P,Primitive] using hg
  have hh := no_challenge_path P hprim
  rw [he] at hh
  exact hh hp

end R002.GCSector
