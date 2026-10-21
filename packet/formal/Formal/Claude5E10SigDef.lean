import Formal.Claude5E10SigInt2
import Formal.Claude3ChallengeSpec

/-!
# E10 as a Theorem 1a signature: the signature

Written by a Claude worker (2026-10-21, E10 bridge session).

`e10S Q` is a signature of `ClaudeChallenge2` (Theorem 1a) whose parameters `p, r, s, w` are
affine functions `Q.P, Q.R, Q.S, Q.W` of `t`.  Its charts are the two caps and the three tube
sectors (`QD`), its 75 records are those of `Claude5E10SigInt` and its 12 marks are the cap
corners.

* `mem_iff` : chart membership is `QD`;
* `rec_eval` : a record acts by `recMap`;
* `corn_eval` : the marks are at `cornZ`.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge2 (Aff Chart)

/-- Affine parameters `p, r, s, w` of `t`. -/
structure RP where
  P : Aff
  R : Aff
  S : Aff
  W : Aff

namespace RP

variable (Q : RP)

/-- The parameters at `t`. -/
abbrev p (t : ℕ) : ℤ := Q.P.eval t
abbrev r (t : ℕ) : ℤ := Q.R.eval t
abbrev s (t : ℕ) : ℤ := Q.S.eval t
abbrev w (t : ℕ) : ℤ := Q.W.eval t

/-- The affine function `k0 + kp p + kr r + ks s + kw w`. -/
def lin (k0 kp kr ks kw : ℤ) : Aff :=
  ⟨kp * Q.P.a + kr * Q.R.a + ks * Q.S.a + kw * Q.W.a,
    k0 + kp * Q.P.b + kr * Q.R.b + ks * Q.S.b + kw * Q.W.b⟩

theorem lin_eval (k0 kp kr ks kw : ℤ) (t : ℕ) :
    (Q.lin k0 kp kr ks kw).eval t = k0 + kp * Q.p t + kr * Q.r t + ks * Q.s t + kw * Q.w t := by
  simp only [lin, Aff.eval, p, r, s, w]; ring

/-- Sum of affine functions. -/
def aadd (A B : Aff) : Aff := ⟨A.a + B.a, A.b + B.b⟩

theorem aadd_eval (A B : Aff) (t : ℕ) : (aadd A B).eval t = A.eval t + B.eval t := by
  simp only [aadd, Aff.eval]; ring

/-- The side translations `gτ` as affine functions. -/
def gτA : ℕ → ℕ → Aff × Aff
  | 0, 0 => (Q.lin 0 0 6 3 0, Q.lin 0 0 (-6) (-3) 0)
  | 0, 1 => (Q.lin 0 0 5 3 0, Q.lin 0 0 (-6) (-3) 0)
  | 0, 2 => (Q.lin 0 0 3 2 0, Q.lin 0 0 (-5) (-3) 0)
  | 0, 3 => (Q.lin 0 0 1 1 0, Q.lin 0 0 (-3) (-2) 0)
  | 0, 4 => (Q.lin 0 0 0 0 0, Q.lin 0 0 (-1) (-1) 0)
  | 0, _ => (Q.lin 0 0 0 0 0, Q.lin 0 0 0 0 0)
  | _, 0 => (Q.lin 0 0 0 0 1, Q.lin 0 2 0 0 (-1))
  | _, 1 => (Q.lin 0 0 1 1 1, Q.lin 0 2 0 0 (-1))
  | _, 2 => (Q.lin 0 0 3 2 1, Q.lin 0 2 (-1) (-1) (-1))
  | _, 3 => (Q.lin 0 0 5 3 1, Q.lin 0 2 (-3) (-2) (-1))
  | _, 4 => (Q.lin 0 0 6 3 1, Q.lin 0 2 (-5) (-3) (-1))
  | _, _ => (Q.lin 0 0 6 3 1, Q.lin 0 2 (-6) (-3) (-1))

theorem gτA_eval (c i : ℕ) (t : ℕ) :
    ((Q.gτA c i).1.eval t, (Q.gτA c i).2.eval t) = gτ (Q.p t) (Q.r t) (Q.s t) (Q.w t) c i := by
  rcases c with _ | c <;> rcases i with _ | _ | _ | _ | _ | _ | i <;>
    simp only [gτA, gτ, lin_eval, Prod.mk.injEq] <;> constructor <;> ring

/-- Record translations. -/
def rdA (n : ℕ) : Aff × Aff :=
  if n < 2 then (Q.lin 0 0 0 0 0, Q.lin 0 0 0 0 0)
  else if n = 2 then (Q.lin 0 0 (-6) (-3) 0, Q.lin 0 0 6 3 0)
  else
    let e : ℤ := (((n - 3) % 2 : ℕ) : ℤ)
    (aadd (Q.gτA ((n - 3) / 36) ((n - 3) / 6 % 6)).1 (Q.lin 0 0 (-6 * e) (-3 * e) 0),
      aadd (Q.gτA ((n - 3) / 36) ((n - 3) / 6 % 6)).2 (Q.lin 0 0 (6 * e) (3 * e) 0))

/-- Record rotations. -/
def rrot (n : ℕ) : ℕ := if n < 3 then 0 else gk ((n - 3) / 36) ((n - 3) / 6 % 6)

theorem rotN_eq (n : ℕ) (z : ℤ × ℤ) : ClaudeChallenge2.rotN n z = ClaudeChallenge.rotN n z := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ClaudeChallenge2.rotN, ClaudeChallenge.rotN, ih,
      ClaudeChallenge2.rot, ClaudeChallenge.rot]

theorem unitVec_eq : ClaudeChallenge2.unitVec = ClaudeChallenge.unitVec := rfl

theorem rec_eval (n : ℕ) (t : ℕ) (z : ℤ × ℤ) :
    ClaudeChallenge2.rotN (RP.rrot n) z + ((Q.rdA n).1.eval t, (Q.rdA n).2.eval t) =
      recMap (Q.p t) (Q.r t) (Q.s t) (Q.w t) n z := by
  rw [rotN_eq]
  unfold rrot rdA recMap
  by_cases h2 : n < 2
  · simp only [if_pos h2, if_pos (show n < 3 by omega), lin_eval, ClaudeChallenge.rotN]
    ext <;> simp
  by_cases h3 : n = 2
  · subst h3
    simp only [if_neg h2, if_pos (show (2 : ℕ) < 3 by omega), ClaudeChallenge.rotN]
    ext <;> simp [per, lin_eval] <;> ring
  simp only [if_neg h2, if_neg h3, if_neg (show ¬ n < 3 by omega)]
  have g := Q.gτA_eval ((n - 3) / 36) ((n - 3) / 6 % 6) t
  simp only [gmap, aadd_eval, lin_eval]
  rw [← g]
  ext <;> simp [per] <;> ring

/-- The chart bounds. -/
def chartA (f : ℕ) : Chart :=
  if f = 0 then ⟨Q.lin 0 0 (-1) (-1) 0, Q.lin 0 0 1 0 0, Q.lin 0 0 0 0 0, Q.lin 0 0 2 1 0,
      Q.lin 0 0 0 0 0, Q.lin 0 0 2 1 0⟩
  else if f = 1 then ⟨Q.lin 0 0 (-1) 0 0, Q.lin 0 0 1 1 0, Q.lin 0 0 0 0 0, Q.lin 0 0 2 1 0,
      Q.lin 0 0 0 0 0, Q.lin 0 0 2 1 0⟩
  else if f = 2 then ⟨Q.lin 0 0 0 0 0, Q.lin 0 0 2 1 0, Q.lin 0 0 (-6) (-3) 0, Q.lin 0 2 0 0 0,
      Q.lin 0 0 0 0 0, Q.lin 0 2 0 0 0⟩
  else if f = 3 then ⟨Q.lin 0 0 2 1 0, Q.lin 0 0 4 2 0, Q.lin 0 0 (-6) (-3) 0, Q.lin 0 2 0 0 0,
      Q.lin 0 0 0 0 0, Q.lin 0 2 0 0 0⟩
  else ⟨Q.lin 0 0 4 2 0, Q.lin 0 0 6 3 0, Q.lin 0 0 (-6) (-3) 0, Q.lin 0 2 0 0 0,
      Q.lin 0 0 0 0 0, Q.lin 0 2 0 0 0⟩

theorem mem_iff {f : ℕ} (hf : f < 5) (t : ℕ) (hm : 0 ≤ 2 * Q.r t + Q.s t) (z : ℤ × ℤ) :
    (Q.chartA f).Mem t z ↔ QD (Q.p t) (Q.r t) (Q.s t) f z := by
  obtain ⟨x, y⟩ := z
  interval_cases f <;>
    simp only [chartA, Chart.Mem, lin_eval, QD, HL, HU, HT, if_true, if_false,
      show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
      show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega,
      show (4 : ℕ) ≠ 0 by omega, show (4 : ℕ) ≠ 1 by omega, show (4 : ℕ) ≠ 2 by omega,
      show (4 : ℕ) ≠ 3 by omega] <;>
    constructor <;> intro h <;> omega

/-- The marks as affine functions. -/
def cornA : ℕ → Aff × Aff
  | 0 => (Q.lin 0 0 0 0 0, Q.lin 0 0 0 0 0)
  | 1 => (Q.lin 0 0 1 0 0, Q.lin 0 0 0 0 0)
  | 2 => (Q.lin 0 0 1 0 0, Q.lin 0 0 1 1 0)
  | 3 => (Q.lin 0 0 0 0 0, Q.lin 0 0 2 1 0)
  | 4 => (Q.lin 0 0 (-1) (-1) 0, Q.lin 0 0 2 1 0)
  | 5 => (Q.lin 0 0 (-1) (-1) 0, Q.lin 0 0 1 1 0)
  | 6 => (Q.lin 0 0 0 0 0, Q.lin 0 0 0 0 0)
  | 7 => (Q.lin 0 0 1 1 0, Q.lin 0 0 0 0 0)
  | 8 => (Q.lin 0 0 1 1 0, Q.lin 0 0 1 0 0)
  | 9 => (Q.lin 0 0 0 0 0, Q.lin 0 0 2 1 0)
  | 10 => (Q.lin 0 0 (-1) 0 0, Q.lin 0 0 2 1 0)
  | _ => (Q.lin 0 0 (-1) 0 0, Q.lin 0 0 1 0 0)

theorem corn_eval (k t : ℕ) :
    ((Q.cornA k).1.eval t, (Q.cornA k).2.eval t) = cornZ (Q.r t) (Q.s t) k := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 =>
    simp only [cornA, cornZ, lin_eval, Prod.mk.injEq] <;> constructor <;> ring
  | k + 11 =>
    simp only [cornA, cornZ, lin_eval, Prod.mk.injEq]; constructor <;> ring

end RP

/-- **The E10 signature** of `ClaudeChallenge2`. -/
def e10S (Q : RP) : ClaudeChallenge2.Sig where
  C := 5
  chart f := Q.chartA f.val
  R := 75
  src n := ⟨rsrc n.val, by have := n.isLt; unfold rsrc; split_ifs <;> omega⟩
  tgt n := ⟨rtgt n.val, by have := n.isLt; unfold rtgt; split_ifs <;> omega⟩
  rotj n := RP.rrot n.val
  dx n := (Q.rdA n.val).1
  dy n := (Q.rdA n.val).2
  M := 12
  mchart k := ⟨cornF k.val, by unfold cornF; split_ifs <;> omega⟩
  mx k := (Q.cornA k.val).1
  my k := (Q.cornA k.val).2

end Claude5E10
