import Formal.ClaudeBeltMinus

/-!
# Belt case of A3: main statements

Written by a Claude worker (2026-10-19).

For primitive `k > l ≥ 1` with `k ≡ ±1 (mod l)` the dual of `GC(k,l)[C20]`, as defined
independently in `ClaudeChallengeSpec.lean`, has a literal gSW path. This is the positive
"belt" part of the A3 classification only; no negative statement is claimed here.
-/

namespace ClaudeBelt
open R002 R002.GCPrimitive

/-- Integer form of the belt theorem on the independent challenge graph. -/
theorem belt_literal_path (k l : ℤ) (hl : 0<l) (hkl : l<k) (hprim : Int.gcd k l=1)
    (hmod : (∃ q : ℤ, k=q*l+1) ∨ (∃ q : ℤ, k=q*l-1)) :
    ∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) n p := by
  rcases hmod with ⟨q,hq⟩ | ⟨q,hq⟩
  · have hq1 : 1≤q := by
      by_contra h; push Not at h
      have : q*l≤0*l := mul_le_mul_of_nonneg_right (by omega) hl.le
      omega
    exact plus_path hl q hq1 hq hprim
  · by_cases hl1 : l=1
    · subst hl1
      exact plus_path hl (k-1) (by omega) (by ring) hprim
    · exact minus_path (by omega) q hq hkl hprim

/-- Natural-number form: `k % l = 1 % l` or `k % l = l - 1` (this covers `l = 1`). -/
theorem belt_literal_path_nat (k l : ℕ) (hl : 0<l) (hkl : l<k) (hprim : Nat.gcd k l=1)
    (hmod : k%l=1%l ∨ k%l=l-1) :
    ∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph (k:ℤ) (l:ℤ)) n p := by
  have hdiv := Nat.div_add_mod k l
  generalize k/l=Q at hdiv
  apply belt_literal_path (k:ℤ) (l:ℤ) (by omega) (by omega) (by simpa using hprim)
  by_cases hl1 : l=1
  · subst hl1
    left; exact ⟨(k:ℤ)-1,by ring⟩
  · have h1 : 1%l=1 := Nat.mod_eq_of_lt (by omega)
    rcases hmod with h | h
    · left
      refine ⟨(Q:ℤ),?_⟩
      rw [h,h1] at hdiv
      have := congrArg (fun x : ℕ => (x:ℤ)) hdiv
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] at this; linarith
    · right
      refine ⟨(Q:ℤ)+1,?_⟩
      rw [h] at hdiv
      have := congrArg (fun x : ℕ => (x:ℤ)) hdiv
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_sub (show 1≤l by omega)] at this
      linarith

/-- The same paths in the research formulation (`LiteralPathFrom` on the primitive surface). -/
theorem belt_research_path (k l : ℤ) (hl : 0<l) (hkl : l<k) (hprim : Primitive k l)
    (hmod : (∃ q : ℤ, k=q*l+1) ∨ (∃ q : ℤ, k=q*l-1)) :
    ∃ n p, ∃ t : R002.OrderedTriangle (GCPrimitiveSurface.graph k l),
      R002.LiteralPathFrom (GCPrimitiveSurface.graph k l)
        (fun v => ClaudeChallenge.deg (GCPrimitiveSurface.graph k l) v=5) t p n :=
  (GCChallengeBridge.challenge_has_path_iff hkl hl hprim).mpr
    (belt_literal_path k l hl hkl hprim hmod)

end ClaudeBelt

#print axioms ClaudeBelt.belt_literal_path
#print axioms ClaudeBelt.belt_literal_path_nat
#print axioms ClaudeBelt.belt_research_path
#print axioms ClaudeBelt.plus_path
#print axioms ClaudeBelt.minus_path
