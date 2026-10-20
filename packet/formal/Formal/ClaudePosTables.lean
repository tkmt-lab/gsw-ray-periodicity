import Formal.ClaudePosBand

/-!
# Positive side of A3, part 6: the three label tables

Written by a Claude worker (2026-10-19). The labels are the verifier's tables
(`a3-positive-remaining-proof.md`, section 2: `S4`, `S6plus`, `S6minus`, `upper`, `lower`,
`caps`, and the permutations φ, ψ, χ) transported to the challenge labels by the
orientation preserving bijection
`10↦0, 0↦2, 1↦1, 5↦6, 2↦5, 4↦3, 6↦10, 7↦9, 3↦4, 8↦8, 11↦11, 9↦7`,
and rewritten as `Lab s c` (row `s=i+v*j`, `c=j mod p`) of `ClaudePos.SL`.
All facts about them are finite and checked by `decide`.
-/

namespace ClaudePos

/-- Table lookup: rows `s0, s0+1, …`, each with `p` entries. -/
def tab (s0 p : ℤ) (t : List (Fin 12)) (s c : ℤ) : Fin 12 := t.getD ((s-s0)*p+c).toNat 0

/-- Outer region (`k ≤ 3l/2`, `d=k-l`): `v=2`, `p=3`, rows `-2..3`. -/
def labO : ℤ → ℤ → Fin 12 := tab (-2) 3 [0,0,2, 2,0,1, 6,3,5, 10,7,4, 9,11,8, 8,9,11]

def goodO : List (Bool × ℤ × ℤ) :=
  [(true,-1,0),(true,-1,1),(true,-1,2),(true,0,0),(true,0,1),(true,0,2),
   (false,-2,0),(false,-2,1),(false,-2,2),(false,-1,0),(false,-1,1),(false,-1,2),
   (true,-2,2),(false,0,0),(false,0,1),(false,0,2)]

theorem goodO_ok : ∀ t ∈ goodO, TriOK 2 3 labO t.1 t.2.1 t.2.2 := by decide

theorem goodO_inj : ∀ t ∈ goodO, ∀ t' ∈ goodO,
    (triF 2 3 labO t.1 t.2.1 t.2.2).1=(triF 2 3 labO t'.1 t'.2.1 t'.2.2).1 → t=t' := by decide

/-- Middle-upper region (`2l<k<3l`, `d=k-2l`): `v=3`, `p=2`, rows `-3..4`. -/
def labU : ℤ → ℤ → Fin 12 := tab (-3) 2 [0,2, 0,1, 2,5, 6,4, 10,3, 9,7, 8,11, 7,9]

def goodU : List (Bool × ℤ × ℤ) :=
  [(true,-2,0),(true,-2,1),(true,-1,0),(true,-1,1),(true,0,0),(true,0,1),
   (false,-3,0),(false,-3,1),(false,-2,0),(false,-2,1),(false,-1,0),(false,-1,1),
   (true,-3,1),(false,0,0),(false,0,1)]

theorem goodU_ok : ∀ t ∈ goodU, TriOK 3 2 labU t.1 t.2.1 t.2.2 := by decide

theorem goodU_inj : ∀ t ∈ goodU, ∀ t' ∈ goodU,
    (triF 3 2 labU t.1 t.2.1 t.2.2).1=(triF 3 2 labU t'.1 t'.2.1 t'.2.2).1 → t=t' := by decide

/-- Middle-lower region (`3l/2<k<2l`, `d=2l-k`): `v=3`, `p=2`, rows `-4..3`. -/
def labL : ℤ → ℤ → Fin 12 := tab (-4) 2 [0,2, 0,2, 3,1, 7,5, 6,4, 10,8, 9,11, 0,11]

def goodL : List (Bool × ℤ × ℤ) :=
  [(true,-3,0),(true,-3,1),(true,-2,0),(true,-2,1),(true,-1,0),(true,-1,1),
   (false,-4,0),(false,-4,1),(false,-3,0),(false,-3,1),(false,-2,0),(false,-2,1),
   (true,0,0),(false,-5,0),(false,-5,1)]

theorem goodL_ok : ∀ t ∈ goodL, TriOK 3 2 labL t.1 t.2.1 t.2.2 := by decide

theorem goodL_inj : ∀ t ∈ goodL, ∀ t' ∈ goodL,
    (triF 3 2 labL t.1 t.2.1 t.2.2).1=(triF 3 2 labL t'.1 t'.2.1 t'.2.2).1 → t=t' := by decide

end ClaudePos
