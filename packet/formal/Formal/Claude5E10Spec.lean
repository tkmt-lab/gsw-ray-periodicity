import Formal.Claude2AlignedSpec

/-!
# Specification of Graver's E10(p,r,s) in the aligned-family style

Written by Claude (statement writer) on 2026-10-20, before any proof. The cell data are
re-derived from the verification team's aligned retiling of E10 (R004 `e10_aligned.py`,
read-only; the second paper, `sec:families`: "move the longitudinal cut from `(p,p)` to `(0,2p)`,
obtaining three lattice parallelograms of width `m` and two caps: five disks, also when
`r = 1`"). Parameters: `p, r, s` are the second paper's E10 parameters and also R004's names.
Check: twice the total area is `2 (6r² + 6rs + s²) + 3 · 4pm = 12r² + 2s² + 12rs + 24pr + 12ps`
(`m = 2r + s`), the paper's E10 carbon order.

Geometry. The tube has circumference `3m` and is cut at positions `0, m, 2m` into three
parallelograms (cells 2, 3, 4) with lower side `m` in direction 5 and vertical side `2p`. Lower
cap corner `Lᵢ` (label `i`) sits at tube position `-γᵢ`, upper cap corner `Uᵢ` (label `6 + i`)
at `p - γᵢ` (mod `3m`), where `γ = 0, r, m, m + r, 2m, 2m + r`. The cuts meet the lower cap at
its corners `L0, L4, L2`; they meet the upper cap at its corners when `k = p mod m` is `0` or
`r`, and otherwise at three auxiliary straight-angle corners (labels `12, 13, 14` for the cuts at
`0, m, 2m`). Which upper corners lie in which sector depends on `j = (p div m) mod 3`.

The combinatorics of the cells therefore depend on `p mod 3m` (the paper: "cut-corner positions
involve `p mod C`"); on each of the four cases for `k` the corners are affine in `p, r, s, k`.
The mirror `studies/R002/analysis/2026-10-20-claude-e10-bridge/e10_mirror.py` checks this
Lean-literal surface against R004's construction (isomorphic in all 702 grid cases).
-/

namespace Claude2Aligned

open ClaudeChallenge

/-- The five E10 cells (labels, polygon). Cell 0: lower cap `L0 … L5`, sides
`r, r+s, r, r+s, r, r+s`. Cell 1: upper cap `U0 U5 U4 U3 U2 U1` (`Uᵢ = 6 + i`), sides
`r+s, r, r+s, r, r+s, r`, with the cut corners `12 + (c mod 3)` inserted on its `r`-sides
(`0 < k < r`) or its `(r+s)`-sides (`k > r`). Cells `2 + c` (`c = 0, 1, 2`): tube sector `c`
between positions `cm` and `(c+1)m`; lower corners `L(6-2c mod 6), L(5-2c), L(4-2c)`, then the
upper boundary from position `(c+1)m` down to `cm`, where `U(2i)` lies at offset `k` (`k ≠ 0`)
and `U(2i+1)` at offset `k - r` or `k - r + m`. -/
def e10Cell (p r s : ℤ) (f : Fin 5) : List ℕ × List (ℤ × ℤ) :=
  let m := 2 * r + s
  let k := p % m
  let j := ((p / m) % 3).toNat
  let e : ℕ → ℕ := fun i => 6 + 2 * (i % 3)
  let o : ℕ → ℕ := fun i => 7 + 2 * (i % 3)
  let cut : ℕ → ℕ := fun c => 12 + c % 3
  if f.val = 0 then
    ([0, 1, 2, 3, 4, 5],
      walk (0, 0) [(r, 0), (r + s, 1), (r, 2), (r + s, 3), (r, 4), (r + s, 5)])
  else if f.val = 1 then
    if k = 0 ∨ k = r then
      ([6, 11, 10, 9, 8, 7],
        walk (0, 0) [(r + s, 0), (r, 1), (r + s, 2), (r, 3), (r + s, 4), (r, 5)])
    else if k < r then
      ([6, 11, cut (j + 1), 10, 9, cut (j + 2), 8, 7, cut j],
        walk (0, 0) [(r + s, 0), (r - k, 1), (k, 1), (r + s, 2), (r - k, 3), (k, 3),
          (r + s, 4), (r - k, 5), (k, 5)])
    else
      ([6, cut (j + 1), 11, 10, cut (j + 2), 9, 8, cut j, 7],
        walk (0, 0) [(m - k, 0), (k - r, 0), (r, 1), (m - k, 2), (k - r, 2), (r, 3),
          (m - k, 4), (k - r, 4), (r, 5)])
  else
    let c := f.val - 2
    let a := (j + 3 - c) % 3
    let b := (j + 5 - c) % 3
    let low := [(6 - 2 * c) % 6, 5 - 2 * c, 4 - 2 * c]
    if k = 0 then
      (low ++ [e b, o b, e a],
        walk (0, 0) [(m - r, 5), (r, 5), (2 * p, 1), (r, 2), (m - r, 2), (2 * p, 4)])
    else if k < r then
      (low ++ [cut (c + 1), o b, e a, cut c],
        walk (0, 0) [(m - r, 5), (r, 5), (2 * p, 1), (r - k, 2), (m - r, 2), (k, 2), (2 * p, 4)])
    else if k = r then
      (low ++ [o b, e a, o a],
        walk (0, 0) [(m - r, 5), (r, 5), (2 * p, 1), (m - r, 2), (r, 2), (2 * p, 4)])
    else
      (low ++ [cut (c + 1), e a, o a, cut c],
        walk (0, 0) [(m - r, 5), (r, 5), (2 * p, 1), (m - k, 2), (r, 2), (k - r, 2), (2 * p, 4)])

/-- Corner labels of the E10 cells. -/
def e10Lab (p r s : ℤ) (f : Fin 5) : List ℕ := (e10Cell p r s f).1

/-- E10 cell polygons. -/
def e10Poly (p r s : ℤ) (f : Fin 5) : List (ℤ × ℤ) := (e10Cell p r s f).2

def e10Sig (p r s : ℤ) : Sig := ⟨5, e10Lab p r s, e10Poly p r s⟩

/-- The dual graph of Graver's E10(p,r,s). -/
def e10Graph (p r s : ℤ) : SimpleGraph (e10Sig p r s).Vertex := (e10Sig p r s).graph

end Claude2Aligned
