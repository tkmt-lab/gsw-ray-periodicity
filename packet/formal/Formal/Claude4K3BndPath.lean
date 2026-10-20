import Formal.Claude4K3BndR1a
import Formal.Claude4K3BndR1b
import Formal.Claude4K3BndS1
import Formal.Claude2K3Sufficient
import Formal.Claude4K3Ray

/-!
# K3 boundary families: explicit literal paths in K3(1, s) and K3(r, 1)

Written by a Claude worker (2026-10-20, K3 bridge).  Both are zigzags in the tube development
(`Claude2K3Tube.lean`):

* `path_R1` : K3(1, s), `s ≥ 3`: the path `(0,t), (-1,t+1)` of `Claude2K3Sufficient.pathPlus`
  (`4s - 2` vertices, `q = s - 1`), from the top corner to the bottom corner of hexagon `s - 1`;
* `path_S1` : K3(r, 1), `r ≥ 3`: the path `(r,t), (r-1,t+1)` (`4r + 2` vertices), from the corner
  `(r,0)` of hexagon `0` to the corner `(-1, r+1)` of hexagon `1`.

The end degrees are `Claude4K3BndR1a/b.lean` and `Claude4K3BndS1.lean`.
-/

namespace Claude4K3

open ClaudeChallenge Claude2Aligned Claude2K3

variable {r s : ℤ}

theorem bR_bot_corner (hr : r = 1) (hs : 3 ≤ s) (j : ℤ) :
    deg (k3Graph r s) (V r s (hexCell j) (-s, s)) = 5 := by
  rcases hexCell_cases j with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
  exacts [bR_bot_corner_10 hr hs, bR_bot_corner_9 hr hs, bR_bot_corner_8 hr hs]

theorem bR_bot_seam (hr : r = 1) (hs : 3 ≤ s) (j : ℤ) :
    deg (k3Graph r s) (V r s (hexCell j) (-s + 1, s - 1)) = 6 := by
  rcases hexCell_cases j with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
  exacts [bR_bot_seam_10 hr hs, bR_bot_seam_9 hr hs, bR_bot_seam_8 hr hs]

/-- A literal path in K3(1, s), `s ≥ 3`. -/
theorem path_R1 (hr : r = 1) (hs : 3 ≤ s) :
    LiteralPath (k3Graph r s) (4 * s - 2).toNat (fun n => tv r s (pathPlus n)) := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  have hq : s = (s - 1) * r + 1 := by subst hr; ring
  apply literal_of_tube hr0 hs0
  · omega
  · exact ⟨(2 * s - 1).toNat, by omega⟩
  · intro n m h1 h2 h3
    obtain ⟨j, hj1, hj2⟩ := floor_hex hr0 ((n / 2 : ℕ) : ℤ)
    subst hr
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
    exact bR_top_corner hr hs
  · rw [tv_V hr0 hs0 0 (w := (-1, 1)) (by simp [loc, pathPlus]) (by simp [HexIn]; omega),
      hexCell_zero]
    exact bR_top_seam hr hs
  · rw [tv_V hr0 hs0 (s - 1) (w := (-s + 1, s - 1))
      (by subst hr; ext <;> simp [loc, pathPlus] <;> omega) (by subst hr; simp [HexIn]; omega)]
    exact bR_bot_seam hr hs (s - 1)
  · rw [tv_V hr0 hs0 (s - 1) (w := (-s, s))
      (by subst hr; ext <;> simp [loc, pathPlus] <;> omega) (by subst hr; simp [HexIn]; omega)]
    exact bR_bot_corner hr hs (s - 1)

/-- The zigzag `(r,t), (r-1,t+1)`. -/
def pathS (r : ℤ) (n : ℕ) : ℤ × ℤ := (r - ((n % 2 : ℕ) : ℤ), (((n + 1) / 2 : ℕ) : ℤ))

theorem hexCell_one : hexCell 1 = 9 := by simp [hexCell]

/-- A literal path in K3(r, 1), `r ≥ 3`. -/
theorem path_S1 (hs : s = 1) (hr : 3 ≤ r) :
    LiteralPath (k3Graph r s) (4 * r + 2).toNat (fun n => tv r s (pathS r n)) := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  apply literal_of_tube hr0 hs0
  · omega
  · exact ⟨(2 * r + 1).toNat, by omega⟩
  · intro n m h1 h2 h3
    by_cases hk : ((n / 2 : ℕ) : ℤ) + 1 ≤ r
    · refine ⟨0, ?_, ?_⟩ <;> simp only [HexIn, loc, pathS] <;> omega
    · refine ⟨1, ?_, ?_⟩ <;> simp only [HexIn, loc, pathS] <;> omega
  · intro n m h1 h2 h3
    simp [unitVec, pathS, Prod.ext_iff]
    omega
  · intro n m _ _
    simp [pathS]
    omega
  · intro n m _ _ h
    simp [pathS, Prod.ext_iff] at h
    omega
  · rw [tv_V hr0 hs0 0 (w := (r, 0)) (by simp [loc, pathS]) (by simp [HexIn]; omega),
      hexCell_zero]
    exact bS_start hs hr
  · rw [tv_V hr0 hs0 0 (w := (r - 1, 1)) (by simp [loc, pathS]) (by simp [HexIn]; omega),
      hexCell_zero]
    exact bS_second hs hr
  · rw [tv_V hr0 hs0 1 (w := (0, r)) (by ext <;> simp [loc, pathS] <;> omega)
      (by simp [HexIn]; omega), hexCell_one]
    exact bS_pen hs hr
  · rw [tv_V hr0 hs0 1 (w := (-1, r + 1)) (by ext <;> simp [loc, pathS] <;> omega)
      (by simp [HexIn]; omega), hexCell_one]
    exact bS_end hs hr

/-- Literal paths exist in K3(1, s) for `s ≥ 3`. -/
theorem pe_R1 : ∃ N : ℕ, ∀ s : ℕ, N ≤ s → PE 1 s :=
  ⟨3, fun s hs => ⟨_, _, path_R1 rfl (by exact_mod_cast hs)⟩⟩

/-- Literal paths exist in K3(r, 1) for `r ≥ 3`. -/
theorem pe_S1 : ∃ N : ℕ, ∀ r : ℕ, N ≤ r → PE r 1 :=
  ⟨3, fun r hr => ⟨_, _, path_S1 rfl (by exact_mod_cast hr)⟩⟩

end Claude4K3

#print axioms Claude4K3.pe_R1
#print axioms Claude4K3.pe_S1
