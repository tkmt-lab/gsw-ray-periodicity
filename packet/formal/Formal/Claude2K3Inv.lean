import Formal.Claude2AlignedK3Glue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-!
# K3 aligned surface, part 1: linear cells and a vertex invariant

Written by a Claude worker (2026-10-19) for the second paper (R002 第2弾).

For `0 < r, 0 < s`:
* `inCell_iff`  : membership in a K3 cell is a conjunction of linear inequalities
                  (`TriIn` for the eight `r`-triangles, `HexIn` for the three hexagons);
* `hgt`, `ang`  : two integer functions on sites.  On the three hexagons (the "tube"),
                  `hgt = y - x` and `ang = x + y + 2 r j` (cell `10, 9, 8` is `j = 0, 1, 2`),
                  i.e. the coordinates `w = 2v`, `u` of R004 `k3-positive-proof.md`; on the caps
                  they are extended piecewise-linearly;
* `samePoint_inv` / `vtx_inv` : `inv = (hgt, ang mod 6r)` is constant on every vertex
                  (checked for all 42 gluings, all `m`).
-/

namespace Claude2K3

open ClaudeChallenge Claude2Aligned

theorem rotN_add' (m n : ℕ) (x : ℤ × ℤ) : rotN (m + n) x = rotN m (rotN n x) := by
  induction m with
  | zero => simp [rotN]
  | succ m ih => rw [show m + 1 + n = (m + n) + 1 by omega]; simp only [rotN, ih]

theorem rotN_six_mul' (q : ℕ) (x : ℤ × ℤ) : rotN (6 * q) x = x := by
  induction q with
  | zero => simp [rotN]
  | succ q ih =>
    rw [show 6 * (q + 1) = 6 + 6 * q by ring, rotN_add', ih]
    ext <;> simp [rotN, rot]

theorem rotN_mod6 (n : ℕ) (x : ℤ × ℤ) : rotN n x = rotN (n % 6) x := by
  conv_lhs => rw [← Nat.mod_add_div n 6]
  rw [rotN_add', rotN_six_mul']

/-- The closed `r`-triangle `(0,0), (r,0), (0,r)`. -/
def TriIn (r : ℤ) (z : ℤ × ℤ) : Prop := 0 ≤ z.2 ∧ z.1 + z.2 ≤ r ∧ 0 ≤ z.1

/-- The closed hexagon `(0,0),(r,0),(r,r),(r-s,r+s),(-s,r+s),(-s,s)`. -/
def HexIn (r s : ℤ) (z : ℤ × ℤ) : Prop :=
  0 ≤ z.2 ∧ z.1 ≤ r ∧ z.1 + z.2 ≤ 2 * r ∧ z.2 ≤ r + s ∧ -s ≤ z.1 ∧ 0 ≤ z.1 + z.2

def CellIn (r s : ℤ) (f : Fin 11) (z : ℤ × ℤ) : Prop :=
  if f.val < 8 then TriIn r z else HexIn r s z

variable {r s : ℤ}

theorem inCell_tri (hr : 0 < r) (f : Fin 11) (hf : f.val < 8) (z : ℤ × ℤ) :
    (k3Sig r s).InCell f z ↔ TriIn r z := by
  have hp : (k3Sig r s).poly f = [(0, 0), (r, 0), (0, r)] := by
    simp [k3Sig, k3Poly, hf, walk, rotN, rot]
  simp only [Sig.InCell, Sig.pt, hp]
  constructor
  · intro h
    have h0 := h 0 (by simp); have h1 := h 1 (by simp); have h2 := h 2 (by simp)
    simp [cross] at h0 h1 h2
    exact ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨a, b, c⟩ i hi
    simp at hi
    interval_cases i <;> simp [cross] <;> nlinarith

theorem inCell_hex (hr : 0 < r) (hs : 0 < s) (f : Fin 11) (hf : ¬ f.val < 8) (z : ℤ × ℤ) :
    (k3Sig r s).InCell f z ↔ HexIn r s z := by
  have hp : (k3Sig r s).poly f =
      [(0, 0), (r, 0), (r, r), (r - s, r + s), (-s, r + s), (-s, s)] := by
    simp [k3Sig, k3Poly, hf, walk, rotN, rot]; ring_nf
  simp only [Sig.InCell, Sig.pt, hp]
  constructor
  · intro h
    have h0 := h 0 (by simp); have h1 := h 1 (by simp); have h2 := h 2 (by simp)
    have h3 := h 3 (by simp); have h4 := h 4 (by simp); have h5 := h 5 (by simp)
    simp [cross] at h0 h1 h2 h3 h4 h5
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨a, b, c, d, e, g⟩ i hi
    simp at hi
    interval_cases i <;> simp [cross] <;> nlinarith

theorem inCell_iff (hr : 0 < r) (hs : 0 < s) (f : Fin 11) (z : ℤ × ℤ) :
    (k3Sig r s).InCell f z ↔ CellIn r s f z := by
  unfold CellIn
  split_ifs with hf
  · exact inCell_tri hr f hf z
  · exact inCell_hex hr hs f hf z

/-- Height: `y - x` on the tube; `-r ≤ hgt ≤ 0` on the top cap, `2s ≤ hgt ≤ 2s + r` on the bottom. -/
def hgt (r s : ℤ) (f : Fin 11) (z : ℤ × ℤ) : ℤ :=
  match f.val with
  | 0 => -(z.1 + z.2)
  | 1 => -(z.1 + z.2)
  | 2 => -(z.1 + z.2)
  | 3 => -r
  | 4 => 2 * s + r - z.2
  | 5 => 2 * s + r - z.2
  | 6 => 2 * s + r - z.2
  | 7 => 2 * s + r
  | _ => z.2 - z.1

/-- Angle (to be read modulo `6r`): `x + y + 2rj` on the tube. -/
def ang (r : ℤ) (f : Fin 11) (z : ℤ × ℤ) : ℤ :=
  match f.val with
  | 0 => z.2 - z.1
  | 1 => 4 * r - z.1 + z.2
  | 2 => 2 * r - z.1 + z.2
  | 3 => if z.2 = 0 then 5 * r - 2 * z.1 else if z.1 = 0 then 2 * z.2 - r else 3 * r - 2 * z.2
  | 4 => r - 2 * z.1 - z.2
  | 5 => 5 * r - 2 * z.1 - z.2
  | 6 => 3 * r - 2 * z.1 - z.2
  | 7 => if z.2 = 0 then r + 2 * z.1 else if z.1 = 0 then r - 2 * z.2 else 3 * r + 2 * z.2
  | 8 => z.1 + z.2 + 4 * r
  | 9 => z.1 + z.2 + 2 * r
  | _ => z.1 + z.2

/-- Reduction of `[-6r, 12r)` into `[0, 6r)`. -/
def nrm (r a : ℤ) : ℤ := if a < 0 then a + 6 * r else if 6 * r ≤ a then a - 6 * r else a

/-- The invariant of a site. -/
def inv (r s : ℤ) (p : Fin 11 × (ℤ × ℤ)) : ℤ × ℤ := (hgt r s p.1 p.2, nrm r (ang r p.1 p.2))

set_option maxHeartbeats 0 in
theorem samePoint_inv_aux (hr : 0 < r) (hs : 0 < s) (g f : Fin 11) (z w : ℤ × ℤ)
    (hz : CellIn r s g z) (hw : CellIn r s f w) (i j m : ℕ) (τ : ℤ × ℤ)
    (hG : (k3Sig r s).Glue g i f j m τ) (hzw : rotN m z + τ = w) :
    inv r s (g, z) = inv r s (f, w) := by
  obtain ⟨hi, hj, h1, h2, h3, h4⟩ := hG
  rw [k3Sig_lb, k3Sig_lb] at h1 h2
  have hlg : ((k3Sig r s).poly g).length ≤ 6 := by
    rw [show (k3Sig r s).poly g = k3Poly r s g from rfl, k3_poly_length]
    fin_cases g <;> decide
  have hlf : ((k3Sig r s).poly f).length ≤ 6 := by
    rw [show (k3Sig r s).poly f = k3Poly r s f from rfl, k3_poly_length]
    fin_cases f <;> decide
  have hi' : i < (k3Lab g).length := by
    rw [← k3_poly_length r s g]; exact hi
  have hj' : j < (k3Lab f).length := by
    rw [← k3_poly_length r s f]; exact hj
  have hm := k3_pairs g ⟨i, by omega⟩ f ⟨j, by omega⟩ hi' hj' h1 h2
  simp only [k3GlueTable, List.map_cons, List.map_nil, List.mem_cons, Prod.mk.injEq,
    List.not_mem_nil, or_false] at hm
  rw [rotN_mod6] at h3 h4 hzw
  have hm6 : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize m % 6 = k at h3 h4 hzw hm6
  rcases hm with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
  · interval_cases k <;>
    · simp only [rotN, rot, Sig.pt, k3Sig, k3Poly, walk, Prod.ext_iff] at h3 h4 hzw
      simp [CellIn, TriIn, HexIn] at hz hw
      simp only [inv, hgt, ang, nrm, Fin.isValue, Prod.mk.injEq]
      norm_num at h3 h4 hzw ⊢
      split_ifs <;> omega

theorem samePoint_inv (hr : 0 < r) (hs : 0 < s) (a b : (k3Sig r s).Site)
    (h : (k3Sig r s).SamePoint a b) : inv r s a.1 = inv r s b.1 := by
  obtain ⟨⟨g, z⟩, hz⟩ := a
  obtain ⟨⟨f, w⟩, hw⟩ := b
  obtain ⟨i, j, m, τ, hG, hzw⟩ := h
  exact samePoint_inv_aux hr hs g f z w ((inCell_iff hr hs g z).1 hz) ((inCell_iff hr hs f w).1 hw)
    i j m τ hG hzw

end Claude2K3
