import Formal.Claude2K3Degree
import Mathlib.Tactic.LinearCombination

/-!
# K3 aligned surface, part 4: the tube development and paths in it

Written by a Claude worker (2026-10-19).

The three hexagons of K3 tile the strip ("tube") of R004 `k3-positive-proof.md`: the hexagon
`H + j(r,r)` (`H` the chart hexagon of `k3Poly`) is cell `hexCell j` (`10, 9, 8` for
`j ≡ 0, 1, 2 mod 3`).

* `tv z`            : the vertex of a tube point `z` (any `j` with `z - j(r,r) ∈ H` gives the same
                      vertex, `hex_same`);
* `inv_tube`        : on the tube, `inv = (y - x, (x + y) mod 6r)`;
* `tube_eq`         : two tube points with `|x - x'| ≤ 1` and the same vertex are equal;
* `literal_of_tube` : a unit zigzag of tube points with `|x - x'| ≤ 1`, every two members at
                      index distance `≤ 2` in a common hexagon, and the right end degrees, is a
                      `LiteralPath` of `k3Graph r s`.
-/

namespace Claude2K3
open ClaudeChallenge Claude2Aligned
variable {r s : ℤ}

/-- The cell of the `j`-th hexagon of the tube. -/
def hexCell (j : ℤ) : Fin 11 := if j % 3 = 0 then 10 else if j % 3 = 1 then 9 else 8

/-- Coordinates of the tube point `z` in the `j`-th hexagon. -/
def loc (r j : ℤ) (z : ℤ × ℤ) : ℤ × ℤ := (z.1 - j * r, z.2 - j * r)

theorem hexCell_cellIn (j : ℤ) {z : ℤ × ℤ} (h : HexIn r s z) : CellIn r s (hexCell j) z := by
  unfold hexCell CellIn; split_ifs <;> simp_all

theorem hexCell_cases (j : ℤ) :
    (j % 3 = 0 ∧ hexCell j = 10) ∨ (j % 3 = 1 ∧ hexCell j = 9) ∨ (j % 3 = 2 ∧ hexCell j = 8) := by
  unfold hexCell; split_ifs <;> omega

/-- Neighbouring hexagons are glued along the seam `x + y = 2(j+1)r`. -/
theorem hex_seam (hr : 0 < r) (hs : 0 < s) (j : ℤ) (z : ℤ × ℤ) (h : HexIn r s (loc r j z))
    (h' : HexIn r s (loc r (j + 1) z)) :
    V r s (hexCell j) (loc r j z) = V r s (hexCell (j + 1)) (loc r (j + 1) z) := by
  have hz : loc r j z + (-r, -r) = loc r (j + 1) z := by
    ext <;> simp [loc] <;> ring
  have hc := hexCell_cases j
  have hc' := hexCell_cases (j + 1)
  rcases hc with ⟨h1, e1⟩ | ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
  rcases hc' with ⟨h2, e2⟩ | ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
  (try omega) <;> rw [e1, e2] <;>
  first
    | exact V_glue hr hs (gl_10_2 (r := r) (s := s)) (by simpa [rotN] using hz)
        (hexCell_cellIn 10 h) (hexCell_cellIn 9 h')
    | exact V_glue hr hs (gl_9_2 (r := r) (s := s)) (by simpa [rotN] using hz)
        (hexCell_cellIn 9 h) (hexCell_cellIn 8 h')
    | exact V_glue hr hs (gl_8_2 (r := r) (s := s)) (by simpa [rotN] using hz)
        (hexCell_cellIn 8 h) (hexCell_cellIn 10 h')

theorem hex_same (hr : 0 < r) (hs : 0 < s) (j j' : ℤ) (z : ℤ × ℤ) (h : HexIn r s (loc r j z))
    (h' : HexIn r s (loc r j' z)) :
    V r s (hexCell j) (loc r j z) = V r s (hexCell j') (loc r j' z) := by
  have a := h.2.2.1; have b := h.2.2.2.2.2; have c := h'.2.2.1; have d := h'.2.2.2.2.2
  simp only [loc] at a b c d
  have e1 : j' ≤ j + 1 := by
    by_contra hc; push Not at hc
    have : (j + 2) * r ≤ j' * r := mul_le_mul_of_nonneg_right (by omega) hr.le
    nlinarith
  have e2 : j ≤ j' + 1 := by
    by_contra hc; push Not at hc
    have : (j' + 2) * r ≤ j * r := mul_le_mul_of_nonneg_right (by omega) hr.le
    nlinarith
  rcases (show j' = j ∨ j' = j + 1 ∨ j = j' + 1 by omega) with rfl | rfl | rfl
  · rfl
  · exact hex_seam hr hs j z h h'
  · exact (hex_seam hr hs j' z h' h).symm

open Classical in
/-- The vertex of a tube point. -/
noncomputable def tv (r s : ℤ) (z : ℤ × ℤ) : (k3Sig r s).Vertex :=
  if h : ∃ j, HexIn r s (loc r j z) then V r s (hexCell h.choose) (loc r h.choose z)
  else V r s 0 (0, 0)

theorem tv_eq (hr : 0 < r) (hs : 0 < s) {j : ℤ} {z : ℤ × ℤ} (h : HexIn r s (loc r j z)) :
    tv r s z = V r s (hexCell j) (loc r j z) := by
  have ex : ∃ j, HexIn r s (loc r j z) := ⟨j, h⟩
  rw [tv, dif_pos ex]
  exact hex_same hr hs _ _ z ex.choose_spec h

theorem tv_V (hr : 0 < r) (hs : 0 < s) (j : ℤ) {z w : ℤ × ℤ} (hw : loc r j z = w)
    (h : HexIn r s w) : tv r s z = V r s (hexCell j) w := by
  subst hw; exact tv_eq hr hs h

theorem hgt_hex (j : ℤ) (w : ℤ × ℤ) : hgt r s (hexCell j) w = w.2 - w.1 := by
  rcases hexCell_cases j with ⟨-, e1⟩ | ⟨-, e1⟩ | ⟨-, e1⟩ <;> rw [e1] <;> simp [hgt]

theorem ang_hex (j : ℤ) (w : ℤ × ℤ) : ang r (hexCell j) w = w.1 + w.2 + 2 * r * (j % 3) := by
  rcases hexCell_cases j with ⟨h1, e1⟩ | ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rw [e1, h1] <;> simp [ang] <;>
    ring

theorem inv_tube (hr : 0 < r) (j : ℤ) (z : ℤ × ℤ) (h : HexIn r s (loc r j z)) :
    inv r s (hexCell j, loc r j z) = (z.2 - z.1, (z.1 + z.2) % (6 * r)) := by
  obtain ⟨-, -, h2, -, -, h5⟩ := h
  simp only [loc] at h2 h5
  simp only [inv, hgt_hex, ang_hex, loc]
  have hj : j = j % 3 + 3 * (j / 3) := (Int.emod_add_mul_ediv j 3).symm
  have hX : z.1 + z.2 = (z.1 - j * r + (z.2 - j * r) + 2 * r * (j % 3)) + 6 * r * (j / 3) := by
    linear_combination (2 * r) * hj
  have hb : 0 ≤ z.1 - j * r + (z.2 - j * r) + 2 * r * (j % 3) ∧
      z.1 - j * r + (z.2 - j * r) + 2 * r * (j % 3) ≤ 6 * r := by
    have he : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases he with he | he | he <;> rw [he] <;> constructor <;> linarith
  refine Prod.ext (by simp only; ring) ?_
  simp only
  rw [hX, Int.add_mul_emod_self_left]
  rcases eq_or_lt_of_le hb.2 with he | he
  · rw [he, Int.emod_self]; unfold nrm; split_ifs <;> omega
  · rw [Int.emod_eq_of_lt hb.1 he]; unfold nrm; split_ifs <;> omega

/-- Two tube points of one vertex with `|x - x'| ≤ 1` coincide. -/
theorem tube_eq (hr : 0 < r) (hs : 0 < s) {j j' : ℤ} {z z' : ℤ × ℤ}
    (h : HexIn r s (loc r j z)) (h' : HexIn r s (loc r j' z'))
    (he : inv r s (hexCell j, loc r j z) = inv r s (hexCell j', loc r j' z'))
    (hx1 : z.1 - z'.1 ≤ 1) (hx2 : z'.1 - z.1 ≤ 1) : z = z' := by
  rw [inv_tube hr j z h, inv_tube hr j' z' h', Prod.mk.injEq] at he
  obtain ⟨e1, e2⟩ := he
  have hd : 6 * r ∣ (z'.1 + z'.2) - (z.1 + z.2) := Int.ModEq.dvd e2
  have h0 : (z'.1 + z'.2) - (z.1 + z.2) = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
    omega
  ext <;> omega

/-- From a zigzag of tube points to a literal path. -/
theorem literal_of_tube (hr : 0 < r) (hs : 0 < s) (N : ℕ) (P : ℕ → ℤ × ℤ) (hN : 4 ≤ N)
    (hE : Even N)
    (hpair : ∀ n m, n < m → m ≤ n + 2 → m < N →
      ∃ j, HexIn r s (loc r j (P n)) ∧ HexIn r s (loc r j (P m)))
    (hunit : ∀ n m, n < m → m ≤ n + 2 → m < N → P m - P n ∈ unitVec)
    (hx : ∀ n m, n < N → m < N → (P n).1 - (P m).1 ≤ 1)
    (hinj : ∀ n m, n < N → m < N → P n = P m → n = m)
    (hd0 : deg (k3Graph r s) (tv r s (P 0)) = 5) (hd1 : deg (k3Graph r s) (tv r s (P 1)) = 6)
    (hd2 : deg (k3Graph r s) (tv r s (P (N - 2))) = 6)
    (hd3 : deg (k3Graph r s) (tv r s (P (N - 1))) = 5) :
    LiteralPath (k3Graph r s) N (fun n => tv r s (P n)) := by
  have hreg : ∀ n, n < N → ∃ j, HexIn r s (loc r j (P n)) := by
    intro n hn
    by_cases h : n + 1 < N
    · obtain ⟨j, hj, -⟩ := hpair n (n + 1) (by omega) (by omega) h
      exact ⟨j, hj⟩
    · obtain ⟨j, -, hj⟩ := hpair (n - 1) n (by omega) (by omega) hn
      exact ⟨j, hj⟩
  have hinjp : ∀ a b, a < N → b < N → tv r s (P a) = tv r s (P b) → a = b := by
    intro a b ha hb he
    obtain ⟨j, hj⟩ := hreg a ha
    obtain ⟨j', hj'⟩ := hreg b hb
    rw [tv_eq hr hs hj, tv_eq hr hs hj'] at he
    have := V_inv hr hs (hexCell_cellIn j hj) (hexCell_cellIn j' hj') he
    exact hinj a b ha hb (tube_eq hr hs hj hj' this (hx a b ha hb) (hx b a hb ha))
  have hadj : ∀ n m, n < m → m ≤ n + 2 → m < N →
      (k3Graph r s).Adj (tv r s (P n)) (tv r s (P m)) := by
    intro n m h1 h2 h3
    obtain ⟨j, hj, hj'⟩ := hpair n m h1 h2 h3
    rw [tv_eq hr hs hj, tv_eq hr hs hj']
    refine V_adj hr hs rfl (hexCell_cellIn j hj) (hexCell_cellIn j hj') (P m - P n)
      (hunit n m h1 h2 h3) (by ext <;> simp [loc]) ?_
    intro he
    have := tube_eq hr hs hj hj' he (hx n m (by omega) h3) (hx m n h3 (by omega))
    have := hinj n m (by omega) h3 this
    omega
  exact ⟨hN, hE, hinjp, fun i hi => hadj i (i + 1) (by omega) (by omega) hi,
    fun i hi => hadj i (i + 2) (by omega) (by omega) hi, hd0, hd3, hd1, hd2⟩

end Claude2K3
