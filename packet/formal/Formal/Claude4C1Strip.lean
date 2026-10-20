import Formal.Claude4C1Three

/-!
# Triangle strips in the `ℤ⁴` model, and forced literal paths

Written by a Claude worker (2026-10-20, C1 bridge session).

A block `(A, D, E, L)` is the zigzag `A, A + E, A + D, A + D + E, …, A + L D` (`Blk.pt`); a list
of blocks is concatenated by `wk` (the last point of a block is the first of the next).

* `StripOK W N`  : the points `W 0 … W N` lie on the surface, consecutive and distance-two points
                   are adjacent, and `W (k+3) ≠ W k`;
* `blkOK_of`     : a block in one face with root steps is a strip;
* `strip_of_chain` : blocks that are strips and fit together at the junctions (`Junc`) give a
                   strip;
* `forced`       : a literal path whose first three vertices are `W 0, W 1, W 2` follows `W`
                   (no edge has three common neighbours, `next_unique`);
* `no_literal_of_strip` : if moreover `W N = W 0`, and every odd-indexed `W k` (`k < N`) is not a
                   corner (or follows a corner), no such literal path exists.
-/

namespace Claude4C1

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

/-- A block of a strip. -/
structure Blk where
  A : Fin 4 → ℤ
  D : Fin 4 → ℤ
  E : Fin 4 → ℤ
  L : ℕ

/-- The `m`-th point of a block. -/
def Blk.pt (b : Blk) (m : ℕ) : Fin 4 → ℤ := b.A + ((m / 2 : ℕ) : ℤ) • b.D + ((m % 2 : ℕ) : ℤ) • b.E

/-- Concatenation of blocks. -/
def wk : List Blk → ℕ → (Fin 4 → ℤ)
  | [], _ => 0
  | [b], k => b.pt k
  | b :: b' :: bs, k => if k < 2 * b.L then b.pt k else wk (b' :: bs) (k - 2 * b.L)

/-- Total number of steps. -/
def tot : List Blk → ℕ
  | [] => 0
  | b :: bs => 2 * b.L + tot bs

/-- A strip of `N` steps. -/
def StripOK (r s : ℤ) (W : ℕ → Fin 4 → ℤ) (N : ℕ) : Prop :=
  (∀ k, k ≤ N → InS r s (W k)) ∧ (∀ k, k + 1 ≤ N → AdjR r s (W k) (W (k + 1))) ∧
    (∀ k, k + 2 ≤ N → AdjR r s (W k) (W (k + 2))) ∧ (∀ k, k + 3 ≤ N → W (k + 3) ≠ W k)

/-- Junction of two blocks. -/
def Junc (r s : ℤ) (b b' : Blk) : Prop :=
  b.pt (2 * b.L) = b'.A ∧ AdjR r s (b.pt (2 * b.L - 1)) (b'.pt 1) ∧
    b'.pt 1 ≠ b.pt (2 * b.L - 2) ∧ b'.pt 2 ≠ b.pt (2 * b.L - 1)

/-- A list of blocks that fit together. -/
def Chain (r s : ℤ) : List Blk → Prop
  | [] => False
  | [b] => StripOK r s b.pt (2 * b.L) ∧ 1 ≤ b.L
  | b :: b' :: bs => StripOK r s b.pt (2 * b.L) ∧ 1 ≤ b.L ∧ Junc r s b b' ∧ Chain r s (b' :: bs)

theorem pt_zero (b : Blk) : b.pt 0 = b.A := by funext t; simp [Blk.pt]

theorem wk_head {b : Blk} {bs : List Blk} (h : Chain r s (b :: bs)) (m : ℕ) (hm : m ≤ 2 * b.L) :
    wk (b :: bs) m = b.pt m := by
  cases bs with
  | nil => rfl
  | cons b' bs =>
    simp only [wk]
    split_ifs with h1
    · rfl
    · obtain ⟨-, -, ⟨hj, -⟩, hc⟩ := h
      have hm' : m = 2 * b.L := by omega
      subst hm'
      rw [Nat.sub_self, hj]
      cases bs with
      | nil => exact pt_zero b'
      | cons b'' bs =>
        simp only [wk]
        rw [if_pos (by have := hc.2.1; omega)]
        exact pt_zero b'

theorem wk_tail (b b' : Blk) (bs : List Blk) (m : ℕ) :
    wk (b :: b' :: bs) (2 * b.L + m) = wk (b' :: bs) m := by
  simp only [wk]
  rw [if_neg (by omega)]
  congr 1; omega

theorem strip_of_chain : ∀ bs : List Blk, Chain r s bs → StripOK r s (wk bs) (tot bs)
  | [], h => h.elim
  | [b], h => by simpa [wk, tot] using h.1
  | b :: b' :: bs, h => by
    have ih := strip_of_chain (b' :: bs) h.2.2.2
    obtain ⟨hb, hL, ⟨hj0, hj1, hj2, hj3⟩, hc⟩ := h
    have hL' : 1 ≤ b'.L := by
      cases bs with
      | nil => exact hc.2
      | cons _ _ => exact hc.2.1
    have hW : ∀ m, m ≤ 2 * b.L → wk (b :: b' :: bs) m = b.pt m :=
      wk_head ⟨hb, hL, ⟨hj0, hj1, hj2, hj3⟩, hc⟩
    have hT : ∀ m, wk (b :: b' :: bs) (2 * b.L + m) = wk (b' :: bs) m := wk_tail b b' bs
    have hW' : ∀ m, m ≤ 2 * b'.L → wk (b' :: bs) m = b'.pt m := wk_head hc
    obtain ⟨i0, i1, i2, i3⟩ := ih
    obtain ⟨b0, b1, b2, b3⟩ := hb
    simp only [tot] at i0 i1 i2 i3 ⊢
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · by_cases h1 : k ≤ 2 * b.L
      · rw [hW k h1]; exact b0 k h1
      · obtain ⟨m, rfl⟩ : ∃ m, k = 2 * b.L + m := ⟨k - 2 * b.L, by omega⟩
        rw [hT]; exact i0 m (by omega)
    · by_cases h1 : k + 1 ≤ 2 * b.L
      · rw [hW k (by omega), hW (k + 1) h1]; exact b1 k h1
      · obtain ⟨m, rfl⟩ : ∃ m, k = 2 * b.L + m := ⟨k - 2 * b.L, by omega⟩
        rw [hT, show 2 * b.L + m + 1 = 2 * b.L + (m + 1) by omega, hT]; exact i1 m (by omega)
    · by_cases h1 : k + 2 ≤ 2 * b.L
      · rw [hW k (by omega), hW (k + 2) h1]; exact b2 k h1
      by_cases h2 : 2 * b.L ≤ k
      · obtain ⟨m, rfl⟩ : ∃ m, k = 2 * b.L + m := ⟨k - 2 * b.L, by omega⟩
        rw [hT, show 2 * b.L + m + 2 = 2 * b.L + (m + 2) by omega, hT]; exact i2 m (by omega)
      · have hk : k = 2 * b.L - 1 := by omega
        rw [hW k (by omega), show k + 2 = 2 * b.L + 1 by omega, hT, hW' 1 (by omega), hk]
        exact hj1
    · by_cases h1 : k + 3 ≤ 2 * b.L
      · rw [hW k (by omega), hW (k + 3) h1]; exact b3 k h1
      by_cases h2 : 2 * b.L ≤ k
      · obtain ⟨m, rfl⟩ : ∃ m, k = 2 * b.L + m := ⟨k - 2 * b.L, by omega⟩
        rw [hT, show 2 * b.L + m + 3 = 2 * b.L + (m + 3) by omega, hT]; exact i3 m (by omega)
      · by_cases h3 : k = 2 * b.L - 2
        · rw [hW k (by omega), show k + 3 = 2 * b.L + 1 by omega, hT, hW' 1 (by omega), h3]
          exact hj2
        · have hk : k = 2 * b.L - 1 := by omega
          rw [hW k (by omega), show k + 3 = 2 * b.L + 2 by omega, hT, hW' 2 (by omega), hk]
          exact hj3

/-! ## Literal paths along a strip -/

theorem forced (hr : 0 < r) (hs : 0 < s) {W : ℕ → Fin 4 → ℤ} {N : ℕ} (hS : StripOK r s W N)
    {n : ℕ} {p : ℕ → Surf r s} (hp : LiteralPath (G4 r s) n p) (h0 : (p 0).1 = W 0)
    (h1 : (p 1).1 = W 1) (h2 : (p 2).1 = W 2) : ∀ k, k < n → k ≤ N → (p k).1 = W k := by
  obtain ⟨hS0, hS1, hS2, hS3⟩ := hS
  obtain ⟨h4, -, hinj, hp1, hp2, -⟩ := hp
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk hkN
    match k, ih with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | j + 3, ih =>
      have e0 := ih j (by omega) (by omega) (by omega)
      have e1 := ih (j + 1) (by omega) (by omega) (by omega)
      have e2 := ih (j + 2) (by omega) (by omega) (by omega)
      let w : ℕ → Surf r s := fun i => if h : i ≤ N then ⟨W i, hS0 i h⟩ else p 0
      have hw : ∀ i (h : i ≤ N), w i = ⟨W i, hS0 i h⟩ := fun i h => by simp [w, h]
      have q0 : p j = w j := by rw [hw j (by omega)]; exact Subtype.ext e0
      have q1 : p (j + 1) = w (j + 1) := by rw [hw (j + 1) (by omega)]; exact Subtype.ext e1
      have q2 : p (j + 2) = w (j + 2) := by rw [hw (j + 2) (by omega)]; exact Subtype.ext e2
      have key : p (j + 3) = w (j + 3) := by
        refine next_unique hr hs (u := w j) (v := w (j + 1)) (w := w (j + 2)) ?_ ⟨?_, ?_⟩ ⟨?_, ?_⟩
          ⟨?_, ?_⟩ ?_ ?_
        · rw [← q1, ← q2]; exact hp1 (j + 1) (by omega)
        · rw [hw j (by omega), hw (j + 1) (by omega)]
          exact adjR_symm (hS1 j (by omega))
        · rw [hw j (by omega), hw (j + 2) (by omega)]
          exact adjR_symm (hS2 j (by omega))
        · rw [hw (j + 3) (by omega), hw (j + 1) (by omega)]
          exact hS2 (j + 1) (by omega)
        · rw [hw (j + 3) (by omega), hw (j + 2) (by omega)]
          exact hS1 (j + 2) (by omega)
        · rw [← q1]; exact hp2 (j + 1) (by omega)
        · rw [← q2]; exact hp1 (j + 2) (by omega)
        · rw [hw j (by omega), hw (j + 3) (by omega)]
          intro e; exact hS3 j (by omega) (congrArg Subtype.val e).symm
        · rw [← q0]; intro e; have := hinj _ _ (by omega) (by omega) e; omega
      rw [key, hw (j + 3) (by omega)]

theorem no_literal_of_strip (hr : 0 < r) (hs : 0 < s) {W : ℕ → Fin 4 → ℤ} {N : ℕ}
    (hS : StripOK r s W N) (hN : 1 ≤ N) (hret : W N = W 0)
    (hodd : ∀ k, k < N → k % 2 = 1 → ¬ CornerP r s (W k) ∨ CornerP r s (W (k - 1)))
    {n : ℕ} {p : ℕ → Surf r s} (hp : LiteralPath (G4 r s) n p) (h0 : (p 0).1 = W 0)
    (h1 : (p 1).1 = W 1) (h2 : (p 2).1 = W 2) : False := by
  have hf := forced hr hs hS hp h0 h1 h2
  obtain ⟨h4, ⟨c, hc⟩, hinj, -, -, -, d1, -, d3⟩ := hp
  have hnN : n ≤ N := by
    by_contra hlt
    have e := hf N (by omega) le_rfl
    rw [hret, ← h0] at e
    have := hinj N 0 (by omega) (by omega) (Subtype.ext e)
    omega
  have hodd' := hodd (n - 1) (by omega) (by omega)
  rw [deg_g4 hr hs, hf (n - 1) (by omega) (by omega)] at d1
  rw [deg_g4 hr hs, hf (n - 2) (by omega) (by omega)] at d3
  rw [show n - 2 = n - 1 - 1 by omega] at d3
  rcases hodd' with h | h
  · rw [if_neg h] at d1; omega
  · rw [if_pos h] at d3; omega

end Claude4C1
