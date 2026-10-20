import Formal.Claude4C1TypeI
import Formal.Claude4C1TypeII
import Formal.Claude4C1TypeIII
import Formal.Claude4C1TypeIV
import Formal.Claude4C1TypeV

/-!
# C1 necessity: the start of a literal path

Written by a Claude worker (2026-10-20, C1 bridge session).

* `corner_norm`  : a corner can be moved to `C01 = (r+s, r, 0, 0)` (label 01) by a coordinate
                   permutation;
* `nbr_C01`      : the five neighbours `B0 … B4` of `C01` (R004 §3: `b0 … b4`);
* `no_typeI` … `no_typeV` : no literal path starts with the triangle of type I … V
                   (`noPath_of`: the forced walk is the strip of that type, which returns to its
                   start without an odd-indexed corner).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Claude4C1

open ClaudeChallenge Claude2Aligned

/-- The last point of a list of blocks. -/
def lastPt : List Blk → Fin 4 → ℤ
  | [] => 0
  | [b] => b.pt (2 * b.L)
  | _ :: b' :: bs => lastPt (b' :: bs)

theorem wk_end : ∀ bs : List Blk, wk bs (tot bs) = lastPt bs
  | [] => rfl
  | [b] => by simp [wk, tot, lastPt]
  | b :: b' :: bs => by
    rw [show tot (b :: b' :: bs) = 2 * b.L + tot (b' :: bs) from rfl, wk_tail, wk_end (b' :: bs)]
    rfl

theorem noPath_of {r s : ℤ} (hr : 0 < r) (hs : 0 < s) {b : Blk} {bs : List Blk}
    (hc : Chain r s (b :: bs)) (ho : ChainOdd r s (b :: bs)) (hret : lastPt (b :: bs) = b.pt 0)
    {n : ℕ} {p : ℕ → Surf r s} (hp : LiteralPath (G4 r s) n p) (h0 : (p 0).1 = b.pt 0)
    (h1 : (p 1).1 = b.pt 1) (h2 : (p 2).1 = b.pt 2) : False := by
  have hL : 1 ≤ b.L := by cases bs <;> [exact hc.2; exact hc.2.1]
  have hw := wk_head hc
  refine no_literal_of_strip hr hs (strip_of_chain _ hc) (by simp only [tot]; omega) ?_
    (oddOK_of_chain _ hc ho) hp ?_ ?_ ?_
  · rw [wk_end, hret, hw 0 (by omega)]
  · rw [hw 0 (by omega)]; exact h0
  · rw [hw 1 (by omega)]; exact h1
  · rw [hw 2 (by omega)]; exact h2

macro "vec_tac" : tactic =>
  `(tactic| (funext t; fin_cases t <;> simp [lastPt, pt_apply, bI0, bI3, bII0, bII3, bIII0, bIII5, bIV0,
      bIV5, bV0, bV2] <;> omega))

variable {r s : ℕ}

theorem no_typeI (hr : 1 ≤ r) (hs : 2 ≤ s) {n : ℕ} {p : ℕ → Surf r s}
    (hp : LiteralPath (G4 r s) n p) (h0 : (p 0).1 = (bI0 r s).pt 0) (h1 : (p 1).1 = (bI0 r s).pt 1)
    (h2 : (p 2).1 = (bI0 r s).pt 2) : False :=
  noPath_of (by omega) (by omega) (chain_I r s hr hs) (chainOdd_I r s hr hs) (by vec_tac) hp h0 h1 h2

theorem no_typeII (hr : 1 ≤ r) (hs : 2 ≤ s) {n : ℕ} {p : ℕ → Surf r s}
    (hp : LiteralPath (G4 r s) n p) (h0 : (p 0).1 = (bII0 r s).pt 0)
    (h1 : (p 1).1 = (bII0 r s).pt 1) (h2 : (p 2).1 = (bII0 r s).pt 2) : False :=
  noPath_of (by omega) (by omega) (chain_II r s hr hs) (chainOdd_II r s hr hs) (by vec_tac) hp h0 h1
    h2

theorem no_typeIII (hr : 1 ≤ r) (hs : 2 ≤ s) {n : ℕ} {p : ℕ → Surf r s}
    (hp : LiteralPath (G4 r s) n p) (h0 : (p 0).1 = (bIII0 r s).pt 0)
    (h1 : (p 1).1 = (bIII0 r s).pt 1) (h2 : (p 2).1 = (bIII0 r s).pt 2) : False :=
  noPath_of (by omega) (by omega) (chain_III r s hr hs) (chainOdd_III r s hr hs) (by vec_tac) hp h0
    h1 h2

theorem no_typeIV (hr : 2 ≤ r) (hs : 2 ≤ s) {n : ℕ} {p : ℕ → Surf r s}
    (hp : LiteralPath (G4 r s) n p) (h0 : (p 0).1 = (bIV0 r s).pt 0)
    (h1 : (p 1).1 = (bIV0 r s).pt 1) (h2 : (p 2).1 = (bIV0 r s).pt 2) : False :=
  noPath_of (by omega) (by omega) (chain_IV r s hr hs) (chainOdd_IV r s hr hs) (by vec_tac) hp h0
    h1 h2

theorem no_typeV (hr : 2 ≤ r) (hs : 2 ≤ s) {n : ℕ} {p : ℕ → Surf r s}
    (hp : LiteralPath (G4 r s) n p) (h0 : (p 0).1 = (bV0 r s).pt 0)
    (h1 : (p 1).1 = (bV0 r s).pt 1) (h2 : (p 2).1 = (bV0 r s).pt 2) : False :=
  noPath_of (by omega) (by omega) (chain_V r s hr hs) (chainOdd_V r s hr hs) (by vec_tac) hp h0 h1 h2

/-! ## The corner `01` and its neighbours -/

def C01 (r s : ℕ) : Fin 4 → ℤ := ![(r : ℤ) + s, r, 0, 0]
def B0 (r s : ℕ) : Fin 4 → ℤ := ![(r : ℤ) + s - 1, (r : ℤ) + 1, 0, 0]
def B1 (r s : ℕ) : Fin 4 → ℤ := ![(r : ℤ) + s - 1, r, 0, 1]
def B2 (r s : ℕ) : Fin 4 → ℤ := ![(r : ℤ) + s, (r : ℤ) - 1, 0, 1]
def B3 (r s : ℕ) : Fin 4 → ℤ := ![(r : ℤ) + s, (r : ℤ) - 1, 1, 0]
def B4 (r s : ℕ) : Fin 4 → ℤ := ![(r : ℤ) + s - 1, r, 1, 0]

theorem nbr_C01 {y : Fin 4 → ℤ} (hy : InS r s y) (h : AdjR r s (C01 r s) y) :
    y = B0 r s ∨ y = B1 r s ∨ y = B2 r s ∨ y = B3 r s ∨ y = B4 r s := by
  obtain ⟨i, j, hij, rfl, -⟩ := h
  rw [inS_iff] at hy
  fin_cases i <;> fin_cases j <;> simp [rt, C01] at hij hy <;>
  first
  | (exfalso; omega)
  | (left; funext t; fin_cases t <;> simp [rt, C01, B0] <;> omega)
  | (right; left; funext t; fin_cases t <;> simp [rt, C01, B1] <;> omega)
  | (right; right; left; funext t; fin_cases t <;> simp [rt, C01, B2] <;> omega)
  | (right; right; right; left; funext t; fin_cases t <;> simp [rt, C01, B3] <;> omega)
  | (right; right; right; right; funext t; fin_cases t <;> simp [rt, C01, B4] <;> omega)

end Claude4C1
