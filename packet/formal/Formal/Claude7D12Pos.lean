import Formal.Claude7D12Laps
import Formal.Claude7D12SuffBase

/-!
# D12 model: tools for explicit literal paths (sufficiency)

Written by a Claude worker (2026-10-22, D12 bridge session).

* `cls_list`  : every index of a chain lies in one of its blocks;
* `inj_list`  : a chain is injective if any two of its blocks meet only at equal global indices;
* `inj_laps`  : the same for `laps G Q ++ tail`, with the lap-to-lap and lap-to-tail meetings
                given by lemmas about single laps;
* `lit_chain` : a chain with distinct points and the right end degrees gives a literal path.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace Claude7D12

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

/-- Every index of a chain lies in a block. -/
theorem cls_list : ∀ (bs : List Blk), Chain r s bs → ∀ k, k ≤ tot bs →
    ∃ a, ∃ ha : a < bs.length, ∃ m, m ≤ 2 * (bs.get ⟨a, ha⟩).L ∧ k = tot (bs.take a) + m ∧
      wk r s bs k = (bs.get ⟨a, ha⟩).pt r s m
  | [], h, _, _ => h.elim
  | [b], h, k, hk => ⟨0, by simp, k, by simpa [tot] using hk, by simp [tot], by simp [wk]⟩
  | b :: b' :: bs, h, k, hk => by
    by_cases h1 : k ≤ 2 * b.L
    · exact ⟨0, by simp, k, by simpa using h1, by simp [tot], wk_head h k h1⟩
    · obtain ⟨k', rfl⟩ : ∃ k', k = 2 * b.L + k' := ⟨k - 2 * b.L, by omega⟩
      obtain ⟨a, ha, m, hm, he, hw⟩ := cls_list (b' :: bs) h.2.2.2 k' (by simp [tot] at hk ⊢; omega)
      refine ⟨a + 1, by simp at ha ⊢; omega, m, by simpa using hm, ?_, ?_⟩
      · simp only [List.take_succ_cons, tot]; omega
      · rw [wk_tail, hw]; simp

/-- **Injectivity of a chain from its blocks** (on the indices `≤ N`). -/
theorem inj_list (bs : List Blk) (hch : Chain r s bs) (N : ℕ) (hN : N ≤ tot bs)
    (hpair : ∀ a b (ha : a < bs.length) (hb : b < bs.length), a ≤ b → ∀ m1 m2,
      m1 ≤ 2 * (bs.get ⟨a, ha⟩).L → m2 ≤ 2 * (bs.get ⟨b, hb⟩).L →
      tot (bs.take a) + m1 ≤ N → tot (bs.take b) + m2 ≤ N →
      (bs.get ⟨a, ha⟩).pt r s m1 = (bs.get ⟨b, hb⟩).pt r s m2 →
      tot (bs.take a) + m1 = tot (bs.take b) + m2) :
    ∀ i j, i ≤ N → j ≤ N → wk r s bs i = wk r s bs j → i = j := by
  intro i j hi hj e
  obtain ⟨a, ha, m1, hm1, rfl, e1⟩ := cls_list bs hch i (by omega)
  obtain ⟨b, hb, m2, hm2, rfl, e2⟩ := cls_list bs hch j (by omega)
  rw [e1, e2] at e
  rcases le_total a b with hab | hab
  · exact hpair a b ha hb hab m1 m2 hm1 hm2 hi hj e
  · exact (hpair b a hb ha hab m2 m1 hm2 hm1 hj hi e.symm).symm

theorem laps_add (G : ℕ → List Blk) (a : ℕ) :
    ∀ b, laps G (a + b) = laps G a ++ laps (fun j => G (a + j)) b
  | 0 => by simp [laps]
  | b + 1 => by
    rw [show a + (b + 1) = (a + b) + 1 by ring, laps, laps_add G a b, laps]; simp

theorem tot_laps_lt (G : ℕ → List Blk) (K : ℕ) (n : ℕ) (hK : ∀ j, j < n → tot (G j) = K) :
    ∀ m, m ≤ n → tot (laps G m) = m * K
  | 0, _ => by simp [laps, tot]
  | m + 1, hm => by rw [laps, tot_append, tot_laps_lt G K n hK m (by omega), hK m (by omega)]; ring

theorem chain_prefix : ∀ (l1 l2 : List Blk), l1 ≠ [] → Chain r s (l1 ++ l2) → Chain r s l1
  | [], _, h, _ => (h rfl).elim
  | [b], l2, _, h => by
    cases l2 with
    | nil => simpa using h
    | cons b' l2 => exact ⟨h.1, h.2.1⟩
  | b :: b' :: l1, l2, _, h => by
    simp only [List.cons_append] at h
    exact ⟨h.1, h.2.1, h.2.2.1, chain_prefix (b' :: l1) l2 (by simp) (by simpa using h.2.2.2)⟩

theorem wk_prefix : ∀ (l1 l2 : List Blk), Chain r s (l1 ++ l2) → l1 ≠ [] →
    ∀ m, m ≤ tot l1 → wk r s (l1 ++ l2) m = wk r s l1 m
  | [], _, _, h, _, _ => (h rfl).elim
  | [b], l2, hch, _, m, hm => by
    simp only [tot, add_zero] at hm
    cases l2 with
    | nil => rfl
    | cons b' l2 =>
      simp only [List.cons_append, List.nil_append] at hch ⊢
      rw [wk_head hch m hm]; rfl
  | b :: b' :: l1, l2, hch, _, m, hm => by
    simp only [List.cons_append] at hch ⊢
    by_cases h1 : m ≤ 2 * b.L
    · rw [wk_head hch m h1, wk_head (chain_prefix (b :: b' :: l1) l2 (by simp) (by simpa using hch)) m h1]
    · obtain ⟨m', rfl⟩ : ∃ m', m = 2 * b.L + m' := ⟨m - 2 * b.L, by omega⟩
      rw [wk_tail, wk_tail]
      exact wk_prefix (b' :: l1) l2 (by simpa using hch.2.2.2) (by simp) m' (by simp [tot] at hm ⊢; omega)

theorem chain_laps_tail (G : ℕ → List Blk) (Q : ℕ) (tail : List Blk)
    (hch : Chain r s (laps G Q ++ tail)) (hG : ∀ j, G j ≠ []) (j : ℕ) (hj : j < Q) :
    Chain r s (G j ++ (laps (fun i => G (j + 1 + i)) (Q - j - 1) ++ tail)) ∧
      laps G Q ++ tail = laps G j ++ (G j ++ (laps (fun i => G (j + 1 + i)) (Q - j - 1) ++ tail)) := by
  have e : laps G Q ++ tail = laps G j ++ (G j ++ (laps (fun i => G (j + 1 + i)) (Q - j - 1) ++ tail)) := by
    conv_lhs => rw [show Q = (j + 1) + (Q - j - 1) by omega, laps_add, laps]
    simp
  refine ⟨?_, e⟩
  rw [e] at hch
  exact chain_suffix _ _ (by simp [hG j]) hch

/-- The point at a lap position. -/
theorem wk_laps (G : ℕ → List Blk) (Q : ℕ) (tail : List Blk) (K : ℕ) (hK : ∀ j, j < Q → tot (G j) = K)
    (hch : Chain r s (laps G Q ++ tail)) (hG : ∀ j, G j ≠ []) (j : ℕ) (hj : j < Q) (m : ℕ)
    (hm : m ≤ K) : wk r s (laps G Q ++ tail) (j * K + m) = wk r s (G j) m := by
  obtain ⟨hc, e⟩ := chain_laps_tail G Q tail hch hG j hj
  rw [e, ← tot_laps_lt G K Q hK j hj.le, wk_app _ _ (by rw [← e]; exact hch) (by simp [hG j]),
    wk_prefix _ _ hc (hG j) m (by rw [hK j hj]; exact hm)]

theorem wk_tail_part (G : ℕ → List Blk) (Q : ℕ) (tail : List Blk) (K : ℕ) (hK : ∀ j, j < Q → tot (G j) = K)
    (hch : Chain r s (laps G Q ++ tail)) (htl : tail ≠ []) (m : ℕ) :
    wk r s (laps G Q ++ tail) (Q * K + m) = wk r s tail m := by
  rw [← tot_laps_lt G K Q hK Q le_rfl]; exact wk_app _ _ hch htl m

/-- **Injectivity of laps followed by a tail** (on the indices `≤ Q K + M`). -/
theorem inj_laps (G : ℕ → List Blk) (Q : ℕ) (tail : List Blk) (K : ℕ) (hK : ∀ j, j < Q → tot (G j) = K)
    (hKp : 0 < K) (M : ℕ) (hM : M ≤ tot tail) (hch : Chain r s (laps G Q ++ tail)) (hG : ∀ j, G j ≠ [])
    (hin : ∀ j, j < Q → ∀ i1 i2, i1 ≤ K → i2 ≤ K → wk r s (G j) i1 = wk r s (G j) i2 → i1 = i2)
    (hcross : ∀ j1 j2, j1 < j2 → j2 < Q → ∀ i1 i2, i1 ≤ K → i2 ≤ K →
      wk r s (G j1) i1 = wk r s (G j2) i2 → j2 = j1 + 1 ∧ i1 = K ∧ i2 = 0)
    (hlt : ∀ j, j < Q → ∀ i1 i2, i1 ≤ K → i2 ≤ M → tail ≠ [] →
      wk r s (G j) i1 = wk r s tail i2 → j + 1 = Q ∧ i1 = K ∧ i2 = 0)
    (htt : ∀ i1 i2, i1 ≤ M → i2 ≤ M → tail ≠ [] →
      wk r s tail i1 = wk r s tail i2 → i1 = i2) :
    ∀ i j, i ≤ Q * K + M → j ≤ Q * K + M →
      wk r s (laps G Q ++ tail) i = wk r s (laps G Q ++ tail) j → i = j := by
  -- every index is in a lap or in the tail
  have cls : ∀ i, i ≤ Q * K + M →
      (∃ j m, j < Q ∧ m ≤ K ∧ i = j * K + m ∧ wk r s (laps G Q ++ tail) i = wk r s (G j) m) ∨
      (tail ≠ [] ∧ ∃ m, m ≤ M ∧ i = Q * K + m ∧ wk r s (laps G Q ++ tail) i = wk r s tail m) := by
    intro i hi
    by_cases hQ : 0 < Q ∧ i ≤ Q * K
    · left
      have hK0 : K ≠ 0 := by omega
      · have hKp' : 0 < K := hKp
        by_cases hlast : i = Q * K
        · refine ⟨Q - 1, K, by omega, le_rfl, ?_, ?_⟩
          · rw [hlast, show Q * K = (Q - 1) * K + K by
              rw [show Q = (Q - 1) + 1 by omega, Nat.succ_mul]; simp]
          · rw [show i = (Q - 1) * K + K by
              rw [hlast, show Q * K = (Q - 1) * K + K by
                rw [show Q = (Q - 1) + 1 by omega, Nat.succ_mul]; simp]]
            exact wk_laps G Q tail K hK hch hG (Q - 1) (by omega) K le_rfl
        · have hlt' : i < Q * K := lt_of_le_of_ne hQ.2 hlast
          refine ⟨i / K, i % K, ?_, (Nat.mod_lt _ hKp).le, (Nat.div_add_mod' i K).symm, ?_⟩
          · by_contra hc
            have : Q * K ≤ i / K * K := Nat.mul_le_mul_right K (by omega)
            have := Nat.div_mul_le_self i K
            omega
          · conv_lhs => rw [← Nat.div_add_mod' i K]
            exact wk_laps G Q tail K hK hch hG _ (by
              by_contra hc
              have : Q * K ≤ i / K * K := Nat.mul_le_mul_right K (by omega)
              have := Nat.div_mul_le_self i K
              omega) _ (Nat.mod_lt _ hKp).le
    · right
      have htl : tail ≠ [] := by
        intro h; subst h
        simp [tot] at hM; subst hM
        simp at hi
        rcases Nat.eq_zero_or_pos Q with h0 | h0
        · subst h0; simp at hi
          -- i = 0 and Q = 0: the whole list is empty
          exact absurd hch (by simp [laps, Chain])
        · exact hQ ⟨h0, hi⟩
      refine ⟨htl, i - Q * K, by omega, by
        rcases Nat.eq_zero_or_pos Q with h0 | h0
        · subst h0; simp
        · have := not_and.1 hQ h0; omega, ?_⟩
      have : i = Q * K + (i - Q * K) := by
        rcases Nat.eq_zero_or_pos Q with h0 | h0
        · subst h0; simp
        · have := not_and.1 hQ h0; omega
      conv_lhs => rw [this]
      exact wk_tail_part G Q tail K hK hch htl _
  intro i j hi hj e
  wlog hij : i ≤ j generalizing i j
  · exact (this j i hj hi e.symm (by omega)).symm
  rcases cls i hi with ⟨j1, m1, hj1, hm1, rfl, e1⟩ | ⟨htl, m1, hm1, rfl, e1⟩ <;>
    rcases cls j hj with ⟨j2, m2, hj2, hm2, rfl, e2⟩ | ⟨htl', m2, hm2, rfl, e2⟩ <;> rw [e1, e2] at e
  · rcases Nat.lt_trichotomy j1 j2 with h | rfl | h
    · obtain ⟨rfl, rfl, rfl⟩ := hcross j1 j2 h hj2 m1 m2 hm1 hm2 e
      ring
    · rw [hin j1 hj1 m1 m2 hm1 hm2 e]
    · have : j2 * K + K ≤ j1 * K := by
        have := Nat.mul_le_mul_right K (show j2 + 1 ≤ j1 by omega); rw [Nat.succ_mul] at this; exact this
      omega
  · obtain ⟨h1, rfl, rfl⟩ := hlt j1 hj1 m1 m2 hm1 hm2 htl' e
    rw [← h1, Nat.succ_mul]; ring
  · have : j2 * K + K ≤ Q * K := by
      have := Nat.mul_le_mul_right K (show j2 + 1 ≤ Q by omega); rw [Nat.succ_mul] at this; exact this
    omega
  · rw [htt m1 m2 hm1 hm2 htl e]

/-- **A literal path from a chain.** -/
theorem lit_chain (hr : 1 ≤ r) (hs : 1 ≤ s) (bs : List Blk) (hch : Chain r s bs) (n : ℕ)
    (hn : n ≤ tot bs + 1) (h4 : 4 ≤ n) (hev : Even n)
    (hinj : ∀ i j, i ≤ n - 1 → j ≤ n - 1 → wk r s bs i = wk r s bs j → i = j)
    (d0 : ∀ v : MS r s, v.1 = wk r s bs 0 → deg (GM r s) v = 5)
    (d1 : ∀ v : MS r s, v.1 = wk r s bs (n - 1) → deg (GM r s) v = 5)
    (d2 : ∀ v : MS r s, v.1 = wk r s bs 1 → deg (GM r s) v = 6)
    (d3 : ∀ v : MS r s, v.1 = wk r s bs (n - 2) → deg (GM r s) v = 6) :
    ∃ n p, LiteralPath (GM r s) n p := by
  have hS := strip_of_chain _ hch
  refine ⟨n, fun k => ⟨wk r s bs (min k (tot bs)), hS.1 _ (min_le_right _ _)⟩, ?_⟩
  refine literal_of_strip hS (by omega) h4 hev (fun i j hi hj e => hinj i j (by omega) (by omega) e) _
    (fun k hk => by simp only [min_eq_left hk]) ?_ ?_ ?_ ?_
  · exact d0 _ (by simp only [min_eq_left (Nat.zero_le _)])
  · exact d1 _ (by simp only [min_eq_left (show n - 1 ≤ tot bs by omega)])
  · exact d2 _ (by simp only [min_eq_left (show 1 ≤ tot bs by omega)])
  · exact d3 _ (by simp only [min_eq_left (show n - 2 ≤ tot bs by omega)])

theorem ch_eq' (hr : 1 ≤ r) (hs : 1 ≤ s) {c c' : ℕ} {z z' : ℤ × ℤ} (h : ch r s c z = ch r s c' z')
    (hc : c < 2) (hc' : c' < 2) (hz : Dom r s c z) (hz' : Dom r s c' z') :
    (c = c' ∧ z = z') ∨ (c = 0 ∧ c' = 1 ∧ ¬ I0 r s z ∧ ¬ I1 r s z' ∧ a0 r s z = a1 r s z') ∨
      (c = 1 ∧ c' = 0 ∧ ¬ I1 r s z ∧ ¬ I0 r s z' ∧ a1 r s z = a0 r s z') :=
  ch_eq hr hs hc hc' hz hz' h

/-- Chains of four-block laps followed by a tail. -/
theorem chain_lapsT (g0 g1 g2 g3 : ℕ → Blk) (Q : ℕ) (hQ : 1 ≤ Q) (tail : List Blk)
    (hG : ∀ j, j < Q → Chain r s [g0 j, g1 j, g2 j, g3 j])
    (hjj : ∀ j, j + 1 < Q → Junc r s (g3 j) (g0 (j + 1)))
    (htl : tail = [] ∨ (Chain r s tail ∧ ∃ t0 rest, tail = t0 :: rest ∧ Junc r s (g3 (Q - 1)) t0)) :
    Chain r s (laps (grp g0 g1 g2 g3) Q ++ tail) := by
  have key : ∀ m, 1 ≤ m → m ≤ Q → ∃ l, laps (grp g0 g1 g2 g3) m = l ++ [g3 (m - 1)] ∧
      Chain r s (laps (grp g0 g1 g2 g3) m) := by
    intro m h1 h2
    induction m with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        refine ⟨[g0 0, g1 0, g2 0], by simp [laps, grp], ?_⟩
        simpa [laps, grp] using hG 0 (by omega)
      · obtain ⟨l, hl, hc⟩ := ih h0 (by omega)
        refine ⟨l ++ [g3 (m - 1)] ++ [g0 m, g1 m, g2 m], ?_, ?_⟩
        · rw [laps, hl]; simp [grp]
        · rw [laps, hl]
          have hj := hjj (m - 1) (by omega)
          rw [show m - 1 + 1 = m by omega] at hj
          have := chain_app l (g3 (m - 1)) [g1 m, g2 m, g3 m] (g0 m) (by rw [← hl]; exact hc) (hG m (by omega)) hj
          simpa [grp] using this
  obtain ⟨l, hl, hc⟩ := key Q hQ le_rfl
  rcases htl with rfl | ⟨htc, t0, rest, rfl, hj⟩
  · simpa using hc
  · rw [hl] at hc ⊢
    simpa using chain_app l (g3 (Q - 1)) rest t0 hc htc hj

theorem ch0_00' (hr : 1 ≤ r) (hs : 1 ≤ s) : ch r s 0 (0, 0) = (2, (0, 0)) := by
  rw [ch0_B (by simp [I0])]; simp [a0]

end Claude7D12
