import Formal.Claude7D12Strip

/-!
# D12 model: helper lemmas for the generated strip files

Written by a Claude worker (2026-10-22, D12 bridge session), adapting `Claude5D14StripHelp.lean`.

* `pt_0` … `pt_odd'` : points of a block;
* `odd_wk`   : no corner at an odd index of a chain, from the blocks;
* `kill_list`: the repetition kill for a chain of blocks `bs ++ [bl]` whose last block contains the
               repeated point.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

/-- Equality of explicit lattice points (linear arithmetic). -/
macro "d12peq" : tactic => `(tactic| (first | rfl | (simp only [Prod.mk.injEq, Prod.ext_iff, true_and, and_true] <;> omega)))

namespace Claude7D12

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

theorem pt_0 (b : Blk) : b.pt r s 0 = ch r s b.c (b.A.1, b.A.2) := by simp [Blk.pt, Blk.pos]

theorem pt_1 (b : Blk) : b.pt r s 1 = ch r s b.c (b.A.1 + b.E.1, b.A.2 + b.E.2) := by
  simp [Blk.pt, Blk.pos]

theorem pt_2 (b : Blk) : b.pt r s 2 = ch r s b.c (b.A.1 + b.D.1, b.A.2 + b.D.2) := by
  simp [Blk.pt, Blk.pos]

theorem pt_e (b : Blk) :
    b.pt r s (2 * b.L) = ch r s b.c (b.A.1 + (b.L : ℤ) * b.D.1, b.A.2 + (b.L : ℤ) * b.D.2) := by
  simp only [Blk.pt]; rw [pos_even]

theorem pt_e1 (b : Blk) (h : 1 ≤ b.L) : b.pt r s (2 * b.L - 1) =
    ch r s b.c (b.A.1 + ((b.L : ℤ) - 1) * b.D.1 + b.E.1, b.A.2 + ((b.L : ℤ) - 1) * b.D.2 + b.E.2) := by
  simp only [Blk.pt]
  rw [show 2 * b.L - 1 = 2 * (b.L - 1) + 1 by omega, pos_odd]
  push_cast [h]; rfl

theorem pt_e2 (b : Blk) (h : 1 ≤ b.L) : b.pt r s (2 * b.L - 2) =
    ch r s b.c (b.A.1 + ((b.L : ℤ) - 1) * b.D.1, b.A.2 + ((b.L : ℤ) - 1) * b.D.2) := by
  simp only [Blk.pt]
  rw [show 2 * b.L - 2 = 2 * (b.L - 1) by omega, pos_even]
  push_cast [h]; rfl

theorem pt_odd' (b : Blk) (i : ℕ) : b.pt r s (2 * i + 1) =
    ch r s b.c (b.A.1 + (i : ℤ) * b.D.1 + b.E.1, b.A.2 + (i : ℤ) * b.D.2 + b.E.2) := by
  simp only [Blk.pt]; rw [pos_odd]

theorem pt_even' (b : Blk) (i : ℕ) : b.pt r s (2 * i) =
    ch r s b.c (b.A.1 + (i : ℤ) * b.D.1, b.A.2 + (i : ℤ) * b.D.2) := by
  simp only [Blk.pt]; rw [pos_even]

theorem adj_ch (hr : 1 ≤ r) (hs : 1 ≤ s) {c : ℕ} (hc : c < 2) {P Q : ℤ × ℤ}
    (hP : Dom r s c P) (hQ : Dom r s c Q) (hu : Q - P ∈ unitVec) :
    AdjM r s (ch r s c P) (ch r s c Q) := by
  have := adj_of_unit hr hs hc hP (by simpa using hQ) hu (v := ch r s c P) rfl
  simpa using this

theorem one_le_of_two {n : ℕ} (h : 2 ≤ n) : (1 : ℤ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)

theorem two_le_of_two {n : ℕ} (h : 2 ≤ n) : (2 : ℤ) ≤ n := by exact_mod_cast h

theorem chain_head_L {b : Blk} {l : List Blk} (h : Chain r s (b :: l)) : 1 ≤ b.L := by
  cases l with
  | nil => exact h.2
  | cons _ _ => exact h.2.1

/-- No corner at an odd index of a chain `bs ++ [bl]`, below `tot bs + M`. -/
theorem odd_wk : ∀ (bs : List Blk) (bl : Blk), Chain r s (bs ++ [bl]) →
    (∀ b ∈ bs, ∀ i, i < b.L → ¬ IsCorner r s (b.pt r s (2 * i + 1))) → ∀ M : ℕ,
    (∀ i, 2 * i + 1 < M → ¬ IsCorner r s (bl.pt r s (2 * i + 1))) →
    ∀ k, k < tot bs + M → k % 2 = 1 → ¬ IsCorner r s (wk r s (bs ++ [bl]) k)
  | [], bl, hch, _, M, hl, k, hk, hko => by
    simp only [List.nil_append, wk]
    obtain ⟨i, rfl⟩ : ∃ i, k = 2 * i + 1 := ⟨k / 2, by omega⟩
    exact hl i (by simp [tot] at hk; omega)
  | b :: bs, bl, hch, hb, M, hl, k, hk, hko => by
    simp only [List.cons_append] at hch ⊢
    by_cases h1 : k < 2 * b.L
    · rw [wk_head hch k (by omega)]
      obtain ⟨i, rfl⟩ : ∃ i, k = 2 * i + 1 := ⟨k / 2, by omega⟩
      exact hb b (by simp) i (by omega)
    · obtain ⟨k', rfl⟩ : ∃ k', k = 2 * b.L + k' := ⟨k - 2 * b.L, by omega⟩
      obtain ⟨b', l', hl'⟩ : ∃ b' l', bs ++ [bl] = b' :: l' := by
        cases h : bs ++ [bl] with
        | nil => simp at h
        | cons b' l' => exact ⟨b', l', rfl⟩
      rw [hl', wk_tail, ← hl']
      have hch' : Chain r s (bs ++ [bl]) := by rw [hl'] at hch ⊢; exact hch.2.2.2
      exact odd_wk bs bl hch' (fun b'' hb'' => hb b'' (by simp [hb''])) M hl k'
        (by simp [tot] at hk; omega) (by omega)

/-- **Repetition kill for a chain.** -/
theorem kill_list (hr : 2 ≤ r) (hs : 2 ≤ s) (bs : List Blk) (bl : Blk)
    (hch : Chain r s (bs ++ [bl])) (i1 : ℕ) (hi1 : i1 < (bs ++ [bl]).length) (m1 m2 : ℕ)
    (hm1 : m1 ≤ 2 * ((bs ++ [bl]).get ⟨i1, hi1⟩).L) (hm2 : m2 ≤ 2 * bl.L)
    (hlt : tot ((bs ++ [bl]).take i1) + m1 < tot bs + m2)
    (hrep : ((bs ++ [bl]).get ⟨i1, hi1⟩).pt r s m1 = bl.pt r s m2)
    (hodd : ∀ b ∈ bs, ∀ i, i < b.L → ¬ IsCorner r s (b.pt r s (2 * i + 1)))
    (hoddl : ∀ i, 2 * i + 1 < m2 → ¬ IsCorner r s (bl.pt r s (2 * i + 1)))
    (b0 : Blk) (l0 : List Blk) (he : bs ++ [bl] = b0 :: l0)
    {n : ℕ} {p : ℕ → MS r s} (hp : LiteralPath (GM r s) n p) (h0 : (p 0).1 = b0.pt r s 0)
    (h1 : (p 1).1 = b0.pt r s 1) (h2 : (p 2).1 = b0.pt r s 2) : False := by
  have hS := strip_of_chain _ hch
  have hlen : bs.length < (bs ++ [bl]).length := by simp
  have hj := wk_at _ hch bs.length hlen m2 (by simpa using hm2)
  have htk : (bs ++ [bl]).take bs.length = bs := by simp
  rw [htk] at hj
  simp only [List.get_eq_getElem, List.getElem_append_right (le_refl _), Nat.sub_self,
    List.getElem_cons_zero] at hj
  have hi := wk_at _ hch i1 hi1 m1 hm1
  have hch0 : Chain r s (b0 :: l0) := he ▸ hch
  have hL0 := chain_head_L hch0
  have hw : ∀ m, m ≤ 2 → wk r s (bs ++ [bl]) m = b0.pt r s m := by
    intro m hm; rw [he]; exact wk_head hch0 m (by omega)
  have hN : tot bs + m2 ≤ tot (bs ++ [bl]) := by rw [tot_append]; simp [tot]; omega
  refine kill_rep hr hs hS hlt hN (by rw [hi, hj, hrep]) ?_ hp
    (by rw [hw 0 (by norm_num), h0]) (by rw [hw 1 (by norm_num), h1]) (by rw [hw 2 (by norm_num), h2])
  exact odd_wk bs bl hch hodd m2 hoddl

end Claude7D12
