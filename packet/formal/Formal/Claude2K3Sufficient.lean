import Formal.Claude2K3Tube

/-!
# K3 aligned surface, part 5: sufficiency of `s ≡ ±1 (mod r)`

Written by a Claude worker (2026-10-19).  The explicit paths of R004 `k3-positive-proof.md`,
in tube coordinates:

* `s = q r + 1`: `(0,0), (-1,1), (0,1), (-1,2), …, (0,2s-2), (-1,2s-1)`  (`4s - 2` vertices);
* `s = q r - 1`: `(0,0), (1,0), (0,1), (1,1), …, (0,2s+1), (1,2s+1)`    (`4s + 4` vertices).

Both run from the top corner `A0` to the bottom corner of hexagon `q`; the second and the
penultimate vertices are on a seam or on the cap boundary, next to the corners.

Main result: `k3_sufficient : K3Sufficient` (statement in `Claude2AlignedSpec.lean`).
-/

namespace Claude2K3
open ClaudeChallenge Claude2Aligned
variable {r s : ℤ}

theorem hexCell_zero : hexCell 0 = 10 := by simp [hexCell]

theorem deg_bot_corner (hr : 2 ≤ r) (hs : 2 ≤ s) (j : ℤ) :
    deg (k3Graph r s) (V r s (hexCell j) (-s, s)) = 5 := by
  rcases hexCell_cases j with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
  exacts [deg_bot_corner_10 hr hs, deg_bot_corner_9 hr hs, deg_bot_corner_8 hr hs]

theorem deg_bot_seam (hr : 2 ≤ r) (hs : 2 ≤ s) (j : ℤ) :
    deg (k3Graph r s) (V r s (hexCell j) (-s + 1, s - 1)) = 6 := by
  rcases hexCell_cases j with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
  exacts [deg_bot_seam_10 hr hs, deg_bot_seam_9 hr hs, deg_bot_seam_8 hr hs]

theorem deg_bot_cap (hr : 2 ≤ r) (hs : 2 ≤ s) (j : ℤ) :
    deg (k3Graph r s) (V r s (hexCell j) (r - s - 1, r + s)) = 6 := by
  rcases hexCell_cases j with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
  exacts [deg_bot_cap_10 hr hs, deg_bot_cap_9 hr hs, deg_bot_cap_8 hr hs]

/-- The path for `s ≡ 1 (mod r)`: `(0,t), (-1,t+1)`. -/
def pathPlus (n : ℕ) : ℤ × ℤ := (-((n % 2 : ℕ) : ℤ), (((n + 1) / 2 : ℕ) : ℤ))

/-- The path for `s ≡ -1 (mod r)`: `(0,t), (1,t)`. -/
def pathMinus (n : ℕ) : ℤ × ℤ := (((n % 2 : ℕ) : ℤ), ((n / 2 : ℕ) : ℤ))

/-- `j = ⌊u / 2r⌋` puts `u` in the `j`-th hexagon's range of `x + y`. -/
theorem floor_hex (hr : 0 < r) (u : ℤ) :
    ∃ j : ℤ, 2 * (j * r) ≤ u ∧ u < 2 * (j * r) + 2 * r := by
  refine ⟨u / (2 * r), ?_, ?_⟩
  · have h1 := Int.emod_add_mul_ediv u (2 * r)
    have h2 := Int.emod_nonneg u (show 2 * r ≠ 0 by omega)
    have : 2 * r * (u / (2 * r)) = 2 * (u / (2 * r) * r) := by ring
    omega
  · have h1 := Int.emod_add_mul_ediv u (2 * r)
    have h2 := Int.emod_lt_of_pos u (show 0 < 2 * r by omega)
    have : 2 * r * (u / (2 * r)) = 2 * (u / (2 * r) * r) := by ring
    omega

theorem path_plus (hr : 2 ≤ r) (q : ℤ) (hq : 1 ≤ q) (hsq : s = q * r + 1) :
    LiteralPath (k3Graph r s) (4 * s - 2).toNat (fun n => tv r s (pathPlus n)) := by
  have hr0 : 0 < r := by omega
  have hB : r ≤ q * r := by nlinarith
  have hs : 2 ≤ s := by omega
  have hs0 : 0 < s := by omega
  apply literal_of_tube hr0 hs0
  · omega
  · exact ⟨(2 * s - 1).toNat, by omega⟩
  · intro n m h1 h2 h3
    obtain ⟨j, hj1, hj2⟩ := floor_hex hr0 ((n / 2 : ℕ) : ℤ)
    refine ⟨j, ?_, ?_⟩ <;> simp only [HexIn, loc, pathPlus] <;> omega
  · intro n m h1 h2 h3
    simp [unitVec, pathPlus, Prod.ext_iff]
    omega
  · intro n m _ _
    simp [pathPlus]
    omega
  · intro n m _ _ h
    simp [pathPlus, Prod.ext_iff] at h
    omega
  · rw [tv_V hr0 hs0 0 (w := (0, 0)) (by simp [loc, pathPlus]) (by simp [HexIn]; omega),
      hexCell_zero]
    exact deg_top_corner hr hs
  · rw [tv_V hr0 hs0 0 (w := (-1, 1)) (by simp [loc, pathPlus]) (by simp [HexIn]; omega),
      hexCell_zero]
    exact deg_top_seam hr hs
  · rw [tv_V hr0 hs0 q (w := (-s + 1, s - 1)) (by ext <;> simp [loc, pathPlus] <;> omega)
      (by simp [HexIn]; omega)]
    exact deg_bot_seam hr hs q
  · rw [tv_V hr0 hs0 q (w := (-s, s)) (by ext <;> simp [loc, pathPlus] <;> omega)
      (by simp [HexIn]; omega)]
    exact deg_bot_corner hr hs q

theorem path_minus (hr : 2 ≤ r) (q : ℤ) (hsq : s = q * r - 1) (hs : 2 ≤ s) :
    LiteralPath (k3Graph r s) (4 * s + 4).toNat (fun n => tv r s (pathMinus n)) := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  have hq1 : (q - 1) * r = q * r - r := by ring
  apply literal_of_tube hr0 hs0
  · omega
  · exact ⟨(2 * s + 2).toNat, by omega⟩
  · intro n m h1 h2 h3
    obtain ⟨j, hj1, hj2⟩ := floor_hex hr0 (((n + 1) / 2 : ℕ) : ℤ)
    refine ⟨j, ?_, ?_⟩ <;> simp only [HexIn, loc, pathMinus] <;> omega
  · intro n m h1 h2 h3
    simp [unitVec, pathMinus, Prod.ext_iff]
    omega
  · intro n m _ _
    simp [pathMinus]
    omega
  · intro n m _ _ h
    simp [pathMinus, Prod.ext_iff] at h
    omega
  · rw [tv_V hr0 hs0 0 (w := (0, 0)) (by simp [loc, pathMinus]) (by simp [HexIn]; omega),
      hexCell_zero]
    exact deg_top_corner hr hs
  · rw [tv_V hr0 hs0 0 (w := (1, 0)) (by simp [loc, pathMinus]) (by simp [HexIn]; omega),
      hexCell_zero]
    exact deg_top_cap hr hs
  · rw [tv_V hr0 hs0 (q - 1) (w := (r - s - 1, r + s))
      (by ext <;> simp [loc, pathMinus] <;> omega) (by simp [HexIn]; omega)]
    exact deg_bot_cap hr hs (q - 1)
  · rw [tv_V hr0 hs0 q (w := (-s, s)) (by ext <;> simp [loc, pathMinus] <;> omega)
      (by simp [HexIn]; omega)]
    exact deg_bot_corner hr hs q

/-- **Sufficiency for K3** (`K3Sufficient`, `Claude2AlignedSpec.lean`): for `r, s ≥ 2` with
`s ≡ ±1 (mod r)`, the dual graph of K3(r,s) has a literal gSW path. -/
theorem k3_sufficient : K3Sufficient := by
  intro r s hr hs h
  have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
  have hs' : (2 : ℤ) ≤ s := by exact_mod_cast hs
  rcases h with h | h
  · obtain ⟨c, hc⟩ := Int.ModEq.dvd h
    have hsq : (s : ℤ) = -c * r + 1 := by linear_combination -hc
    have hq : 1 ≤ -c := by
      by_contra hcon
      have : -c * (r : ℤ) ≤ 0 := by nlinarith
      omega
    exact ⟨_, _, path_plus hr' (-c) hq hsq⟩
  · obtain ⟨c, hc⟩ := Int.ModEq.dvd h
    have hsq : (s : ℤ) = -c * r - 1 := by linear_combination -hc
    exact ⟨_, _, path_minus hr' (-c) hsq hs'⟩

end Claude2K3

#print axioms Claude2K3.k3_sufficient
