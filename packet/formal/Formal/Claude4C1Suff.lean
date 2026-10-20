import Formal.Claude4C1TypeS
import Formal.Claude4C1Iso

/-!
# C1 sufficiency: a literal path for `s = 1`

Written by a Claude worker (2026-10-20, C1 bridge session).

The path is the strip `blkS r 1` (R004 `c1-proof.md` §6 in `ℤ⁴` coordinates), cut after `4r + 2`
points: it runs from the corner `(r+1, r, 0, 0)` (label 01) to the corner `(0, 0, r, r+1)`
(label 32).  The linear form `x₀ + 3 x₂ + 2 x₃` takes the value `r + 1 + k` at the `k`-th point
(`phiS`), so the points are distinct.

* `literal_s1`  : a literal path in `G4 r 1` (`r ≥ 1`);
* `c1_path_s1`  : a literal path in `c1Graph r 1`.
-/

namespace Claude4C1

open ClaudeChallenge Claude2Aligned

theorem wS_head (r : ℕ) (hr : 1 ≤ r) (m : ℕ) (hm : m ≤ 2 * r) :
    wk (blkS r 1) m = (bS0 r 1).pt m := wk_head (chain_S r 1 hr) m (by simp [bS0]; omega)

theorem wS_tail (r m : ℕ) : wk (blkS r 1) (2 * r + m) = (bS1 r 1).pt m :=
  wk_tail (bS0 r 1) (bS1 r 1) [] m

theorem phiS (r : ℕ) (hr : 1 ≤ r) (k : ℕ) (hk : k ≤ 4 * r + 2) :
    wk (blkS r 1) k 0 + 3 * wk (blkS r 1) k 2 + 2 * wk (blkS r 1) k 3 = (r : ℤ) + 1 + k := by
  by_cases h : k ≤ 2 * r
  · rw [wS_head r hr k h]
    simp [pt_apply, bS0]; omega
  · obtain ⟨m, rfl⟩ : ∃ m, k = 2 * r + m := ⟨k - 2 * r, by omega⟩
    rw [wS_tail]
    simp [pt_apply, bS1]; omega

theorem literal_s1 (r : ℕ) (hr : 1 ≤ r) : ∃ n p, LiteralPath (G4 (r : ℤ) ((1 : ℕ) : ℤ)) n p := by
  have hS := strip_of_chain _ (chain_S r 1 hr)
  have htot : tot (blkS r 1) = 4 * r + 2 := by simp [blkS, tot, bS0, bS1]; ring
  rw [htot] at hS
  obtain ⟨h0, h1, h2, -⟩ := hS
  let p : ℕ → Surf (r : ℤ) ((1 : ℕ) : ℤ) := fun k =>
    if h : k ≤ 4 * r + 2 then ⟨wk (blkS r 1) k, h0 k h⟩ else ⟨wk (blkS r 1) 0, h0 0 (by omega)⟩
  have hp : ∀ k (h : k ≤ 4 * r + 2), (p k).1 = wk (blkS r 1) k := fun k h => by simp [p, h]
  have hW := wS_head r hr
  have hT := wS_tail r
  refine ⟨4 * r + 2, p, by omega, ⟨2 * r + 1, by ring⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj he
    have e := congrArg (fun x : Surf (r : ℤ) ((1 : ℕ) : ℤ) => x.1 0 + 3 * x.1 2 + 2 * x.1 3) he
    simp only [hp i (by omega), hp j (by omega)] at e
    rw [phiS r hr i (by omega), phiS r hr j (by omega)] at e
    omega
  · intro i hi
    show AdjR _ _ (p i).1 (p (i + 1)).1
    rw [hp i (by omega), hp (i + 1) (by omega)]; exact h1 i (by omega)
  · intro i hi
    show AdjR _ _ (p i).1 (p (i + 2)).1
    rw [hp i (by omega), hp (i + 2) (by omega)]; exact h2 i (by omega)
  · rw [deg_g4 (by omega) (by norm_num), hp 0 (by omega), hW 0 (by omega), if_pos]
    rw [cornerP_iff]; simp [pt_apply, bS0]
  · rw [deg_g4 (by omega) (by norm_num), hp _ (by omega),
      show 4 * r + 2 - 1 = 2 * r + (2 * r + 1) by omega, hT, if_pos]
    rw [cornerP_iff]; simp [pt_apply, bS1]; omega
  · rw [deg_g4 (by omega) (by norm_num), hp 1 (by omega), hW 1 (by omega), if_neg]
    rw [cornerP_iff]; simp [pt_apply, bS0]; omega
  · rw [deg_g4 (by omega) (by norm_num), hp _ (by omega),
      show 4 * r + 2 - 2 = 2 * r + 2 * r by omega, hT, if_neg]
    rw [cornerP_iff]; simp [pt_apply, bS1]; omega

/-- **Sufficiency**: C1(r, 1) has a literal path for every `r ≥ 1`. -/
theorem c1_path_s1 (r : ℕ) (hr : 1 ≤ r) :
    ∃ n p, LiteralPath (c1Graph (r : ℤ) ((1 : ℕ) : ℤ)) n p :=
  (c1_iff_g4 (by omega) (by norm_num)).2 (literal_s1 r hr)

end Claude4C1
