import Formal.Claude5O2Deg

/-!
# O2 model: strips of triangles and forced literal paths

Written by a Claude worker (2026-10-20, O2 bridge session), adapting `Claude4C1Strip.lean`.

A block `(c, A, D, E, L)` is the zigzag `A, A + E, A + D, A + D + E, …, A + L D` in chart `c`
(`Blk.pos`, `Blk.pt`); `wk` concatenates blocks (the last point of a block is the first of the
next).

* `StripOK W N`   : `W 0 … W N` are vertices, consecutive and distance-two points are adjacent,
                    `W (k+3) ≠ W k`;
* `strip_of_chain`: blocks that are strips and fit together at the junctions give a strip;
* `IsCStrip W N`  : a closed strip of period `N` whose corners all have even index;
* `kill_fwd`, `kill_bwd` : a literal path cannot start with three consecutive points of a
                    closed strip at an even index, in either direction (no edge has three common
                    neighbours; the last point would be a corner at an odd index).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

variable {t d : ℤ}

/-- A block of a strip. -/
structure Blk where
  c : ℕ
  A : ℤ × ℤ
  D : ℤ × ℤ
  E : ℤ × ℤ
  L : ℕ

/-- The chart point of the `m`-th point of a block. -/
def Blk.pos (b : Blk) (m : ℕ) : ℤ × ℤ :=
  (b.A.1 + ((m / 2 : ℕ) : ℤ) * b.D.1 + ((m % 2 : ℕ) : ℤ) * b.E.1,
    b.A.2 + ((m / 2 : ℕ) : ℤ) * b.D.2 + ((m % 2 : ℕ) : ℤ) * b.E.2)

/-- The `m`-th vertex of a block. -/
def Blk.pt (t d : ℤ) (b : Blk) (m : ℕ) : MV := ch t d b.c (b.pos m)

/-- Concatenation of blocks. -/
def wk (t d : ℤ) : List Blk → ℕ → MV
  | [], _ => (0, (0, 0))
  | [b], k => b.pt t d k
  | b :: b' :: bs, k => if k < 2 * b.L then b.pt t d k else wk t d (b' :: bs) (k - 2 * b.L)

/-- Total number of steps. -/
def tot : List Blk → ℕ
  | [] => 0
  | b :: bs => 2 * b.L + tot bs

/-- A strip of `N` steps. -/
def StripOK (t d : ℤ) (W : ℕ → MV) (N : ℕ) : Prop :=
  (∀ k, k ≤ N → Valid t d (W k)) ∧ (∀ k, k + 1 ≤ N → AdjM t d (W k) (W (k + 1))) ∧
    (∀ k, k + 2 ≤ N → AdjM t d (W k) (W (k + 2))) ∧ (∀ k, k + 3 ≤ N → W (k + 3) ≠ W k)

/-- Junction of two blocks. -/
def Junc (t d : ℤ) (b b' : Blk) : Prop :=
  b.pt t d (2 * b.L) = b'.pt t d 0 ∧ AdjM t d (b.pt t d (2 * b.L - 1)) (b'.pt t d 1) ∧
    b'.pt t d 1 ≠ b.pt t d (2 * b.L - 2) ∧ b'.pt t d 2 ≠ b.pt t d (2 * b.L - 1)

/-- A list of blocks that fit together. -/
def Chain (t d : ℤ) : List Blk → Prop
  | [] => False
  | [b] => StripOK t d (b.pt t d) (2 * b.L) ∧ 1 ≤ b.L
  | b :: b' :: bs => StripOK t d (b.pt t d) (2 * b.L) ∧ 1 ≤ b.L ∧ Junc t d b b' ∧
      Chain t d (b' :: bs)

theorem wk_head {b : Blk} {bs : List Blk} (h : Chain t d (b :: bs)) (m : ℕ) (hm : m ≤ 2 * b.L) :
    wk t d (b :: bs) m = b.pt t d m := by
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
      | nil => rfl
      | cons b'' bs =>
        simp only [wk]
        rw [if_pos (by have := hc.2.1; omega)]

theorem wk_tail (b b' : Blk) (bs : List Blk) (m : ℕ) :
    wk t d (b :: b' :: bs) (2 * b.L + m) = wk t d (b' :: bs) m := by
  simp only [wk]
  rw [if_neg (by omega)]
  congr 1; omega

theorem strip_of_chain : ∀ bs : List Blk, Chain t d bs → StripOK t d (wk t d bs) (tot bs)
  | [], h => h.elim
  | [b], h => by simpa [wk, tot] using h.1
  | b :: b' :: bs, h => by
    have ih := strip_of_chain (b' :: bs) h.2.2.2
    obtain ⟨hb, hL, ⟨hj0, hj1, hj2, hj3⟩, hc⟩ := h
    have hL' : 1 ≤ b'.L := by
      cases bs with
      | nil => exact hc.2
      | cons _ _ => exact hc.2.1
    have hW : ∀ m, m ≤ 2 * b.L → wk t d (b :: b' :: bs) m = b.pt t d m :=
      wk_head ⟨hb, hL, ⟨hj0, hj1, hj2, hj3⟩, hc⟩
    have hT : ∀ m, wk t d (b :: b' :: bs) (2 * b.L + m) = wk t d (b' :: bs) m := wk_tail b b' bs
    have hW' : ∀ m, m ≤ 2 * b'.L → wk t d (b' :: bs) m = b'.pt t d m := wk_head hc
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

/-- Evaluation of a chain at the start of its `j`-th block. -/
theorem wk_at : ∀ (bs : List Blk), Chain t d bs → ∀ (j : ℕ) (hj : j < bs.length) (m : ℕ),
    m ≤ 2 * (bs.get ⟨j, hj⟩).L → wk t d bs (tot (bs.take j) + m) = (bs.get ⟨j, hj⟩).pt t d m
  | [], h, _, _, _, _ => h.elim
  | [b], h, j, hj, m, hm => by
    have : j = 0 := by simp at hj; omega
    subst this; simp [wk, tot]
  | b :: b' :: bs, h, j, hj, m, hm => by
    rcases j with _ | j
    · simp only [List.take_zero, tot, zero_add, List.get_eq_getElem, List.getElem_cons_zero]
      exact wk_head h m (by simpa using hm)
    · have hj' : j < (b' :: bs).length := by simp at hj ⊢; omega
      have := wk_at (b' :: bs) h.2.2.2 j hj' m (by simpa using hm)
      simp only [List.take_succ_cons, tot, List.get_eq_getElem, List.getElem_cons_succ] at this ⊢
      rw [add_assoc, wk_tail]
      exact this

/-! ## Blocks -/

theorem pos_even (b : Blk) (i : ℕ) :
    b.pos (2 * i) = (b.A.1 + (i : ℤ) * b.D.1, b.A.2 + (i : ℤ) * b.D.2) := by
  simp only [Blk.pos]
  rw [show 2 * i / 2 = i by omega, show 2 * i % 2 = 0 by omega]
  simp

theorem pos_odd (b : Blk) (i : ℕ) :
    b.pos (2 * i + 1) = (b.A.1 + (i : ℤ) * b.D.1 + b.E.1, b.A.2 + (i : ℤ) * b.D.2 + b.E.2) := by
  simp only [Blk.pos]
  rw [show (2 * i + 1) / 2 = i by omega, show (2 * i + 1) % 2 = 1 by omega]
  simp

theorem pos_cases (b : Blk) (m : ℕ) : ∃ i, (m = 2 * i ∧ b.pos m = (b.A.1 + (i : ℤ) * b.D.1,
    b.A.2 + (i : ℤ) * b.D.2)) ∨ (m = 2 * i + 1 ∧ b.pos m = (b.A.1 + (i : ℤ) * b.D.1 + b.E.1,
    b.A.2 + (i : ℤ) * b.D.2 + b.E.2)) := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' m
  · exact ⟨i, Or.inl ⟨rfl, pos_even b i⟩⟩
  · exact ⟨i, Or.inr ⟨rfl, pos_odd b i⟩⟩

theorem pos_step1 (b : Blk) (m : ℕ) : b.pos (m + 1) - b.pos m = b.E ∨
    b.pos (m + 1) - b.pos m = b.D - b.E := by
  obtain ⟨i, ⟨rfl, e⟩ | ⟨rfl, e⟩⟩ := pos_cases b m
  · left; rw [e, pos_odd]; ext <;> simp
  · right; rw [e, show 2 * i + 1 + 1 = 2 * (i + 1) by ring, pos_even]; ext <;> simp <;> ring

theorem pos_step2 (b : Blk) (m : ℕ) : b.pos (m + 2) - b.pos m = b.D := by
  obtain ⟨i, ⟨rfl, e⟩ | ⟨rfl, e⟩⟩ := pos_cases b m
  · rw [e, show 2 * i + 2 = 2 * (i + 1) by ring, pos_even]; ext <;> simp <;> ring
  · rw [e, show 2 * i + 1 + 2 = 2 * (i + 1) + 1 by ring, pos_odd]; ext <;> simp <;> ring

theorem pos_step3 (b : Blk) (m : ℕ) : b.pos (m + 3) - b.pos m = b.D + b.E ∨
    b.pos (m + 3) - b.pos m = b.D + b.D - b.E := by
  obtain ⟨i, ⟨rfl, e⟩ | ⟨rfl, e⟩⟩ := pos_cases b m
  · left; rw [e, show 2 * i + 3 = 2 * (i + 1) + 1 by ring, pos_odd]; ext <;> simp <;> ring
  · right; rw [e, show 2 * i + 1 + 3 = 2 * (i + 2) by ring, pos_even]; ext <;> simp <;> ring

/-- A block in one chart with unit steps is a strip. -/
theorem blk_ok (ht : 1 ≤ t) (hd : 1 ≤ d) (b : Blk) (hc : b.c < 5)
    (hdom : ∀ i : ℕ, i ≤ b.L → Dom t d b.c (b.A.1 + (i : ℤ) * b.D.1, b.A.2 + (i : ℤ) * b.D.2))
    (hdomo : ∀ i : ℕ, i < b.L →
      Dom t d b.c (b.A.1 + (i : ℤ) * b.D.1 + b.E.1, b.A.2 + (i : ℤ) * b.D.2 + b.E.2))
    (hD : b.D ∈ unitVec) (hE : b.E ∈ unitVec) (hDE : b.D - b.E ∈ unitVec)
    (h3 : b.D + b.E ≠ 0) (h3' : b.D + b.D - b.E ≠ 0) :
    StripOK t d (b.pt t d) (2 * b.L) := by
  have hdm : ∀ m, m ≤ 2 * b.L → Dom t d b.c (b.pos m) := by
    intro m hm
    obtain ⟨i, ⟨rfl, e⟩ | ⟨rfl, e⟩⟩ := pos_cases b m
    · rw [e]; exact hdom i (by omega)
    · rw [e]; exact hdomo i (by omega)
  have adj : ∀ m m', m ≤ 2 * b.L → m' ≤ 2 * b.L → b.pos m' - b.pos m ∈ unitVec →
      AdjM t d (b.pt t d m) (b.pt t d m') := by
    intro m m' hm hm' hu
    have := adj_of_unit ht hc (hdm m hm) (by simpa using hdm m' hm') hu (v := b.pt t d m) rfl
    simpa [Blk.pt] using this
  refine ⟨fun k hk => ch_valid ht hd hc (hdm k hk), fun k hk => ?_, fun k hk => ?_,
    fun k hk => ?_⟩
  · refine adj k (k + 1) (by omega) hk ?_
    rcases pos_step1 b k with e | e <;> rw [e]
    exacts [hE, hDE]
  · exact adj k (k + 2) (by omega) hk (by rw [pos_step2]; exact hD)
  · refine ne_same ht hc (hdm (k + 3) hk) (hdm k (by omega)) (fun e => ?_)
    rcases pos_step3 b k with e' | e' <;> rw [e, sub_self] at e'
    exacts [h3 e'.symm, h3' e'.symm]

end Claude5O2
