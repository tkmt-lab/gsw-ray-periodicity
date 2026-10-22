import Formal.Claude7D12Help

/-!
# D12 model: strips made of laps

Written by a Claude worker (2026-10-22, D12 bridge session).

* `laps F n`  : the concatenation `F 0 ++ F 1 ++ … ++ F (n-1)` of block lists;
* `chain_app` : two chains glued at a junction form a chain;
* `chain_laps`: laps that are chains and are glued at junctions form a chain;
* `wk_app`    : the walk of `l1 ++ l2` after `tot l1` steps is the walk of `l2`;
* `kill_split`: the repetition kill when the strip is `pre ++ (mid ++ [bl])` and the repetition
                happens inside `mid ++ [bl]`.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace Claude7D12

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

/-- `n` laps. -/
def laps (F : ℕ → List Blk) : ℕ → List Blk
  | 0 => []
  | n + 1 => laps F n ++ F n

theorem tot_laps (F : ℕ → List Blk) (K : ℕ) (hK : ∀ j, tot (F j) = K) :
    ∀ n, tot (laps F n) = n * K
  | 0 => by simp [laps, tot]
  | n + 1 => by rw [laps, tot_append, tot_laps F K hK n, hK]; ring

theorem mem_laps (F : ℕ → List Blk) {b : Blk} : ∀ n, b ∈ laps F n → ∃ j, j < n ∧ b ∈ F j
  | 0, h => by simp [laps] at h
  | n + 1, h => by
    rw [laps, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨j, hj, hb⟩ := mem_laps F n h; exact ⟨j, by omega, hb⟩
    · exact ⟨n, by omega, h⟩

theorem chain_cons_iff {b b' : Blk} {l : List Blk} :
    Chain r s (b :: b' :: l) ↔ StripOK r s (b.pt r s) (2 * b.L) ∧ 1 ≤ b.L ∧ Junc r s b b' ∧
      Chain r s (b' :: l) := Iff.rfl

/-- Two chains glued at a junction. -/
theorem chain_app : ∀ (l1 : List Blk) (b : Blk) (l2 : List Blk) (b' : Blk),
    Chain r s (l1 ++ [b]) → Chain r s (b' :: l2) → Junc r s b b' →
    Chain r s (l1 ++ [b] ++ b' :: l2)
  | [], b, l2, b', h1, h2, hj => by
    simp only [List.nil_append, List.cons_append] at h1 ⊢
    exact ⟨h1.1, h1.2, hj, h2⟩
  | [a], b, l2, b', h1, h2, hj => by
    simp only [List.cons_append, List.nil_append] at h1 ⊢
    exact ⟨h1.1, h1.2.1, h1.2.2.1, chain_app [] b l2 b' h1.2.2.2 h2 hj⟩
  | a :: a' :: l1, b, l2, b', h1, h2, hj => by
    simp only [List.cons_append] at h1 ⊢
    refine ⟨h1.1, h1.2.1, h1.2.2.1, ?_⟩
    have := chain_app (a' :: l1) b l2 b' (by simpa using h1.2.2.2) h2 hj
    simpa using this

theorem chain_head {b : Blk} {l : List Blk} (h : Chain r s (b :: l)) :
    StripOK r s (b.pt r s) (2 * b.L) ∧ 1 ≤ b.L := by
  cases l with
  | nil => exact h
  | cons _ _ => exact ⟨h.1, h.2.1⟩

/-- Gluing a chain `l1 ++ [b]` to a chain `b' :: l2` (list form). -/
theorem chain_glue (l1 l2 : List Blk) (b b' : Blk) (e1 : l1 ≠ []) (hl : l1.getLast e1 = b)
    (e2 : l2 ≠ []) (hh : l2.head e2 = b') (h1 : Chain r s l1) (h2 : Chain r s l2)
    (hj : Junc r s b b') : Chain r s (l1 ++ l2) := by
  obtain ⟨l1', hl1⟩ : ∃ l1', l1 = l1' ++ [b] := ⟨l1.dropLast, by rw [← hl]; exact (List.dropLast_append_getLast e1).symm⟩
  obtain ⟨l2', hl2⟩ : ∃ l2', l2 = b' :: l2' := by
    cases l2 with
    | nil => exact (e2 rfl).elim
    | cons x l2' => exact ⟨l2', by simp at hh; rw [hh]⟩
  subst hl1; subst hl2
  exact chain_app l1' b l2' b' h1 h2 hj

/-- The walk of `l1 ++ l2` after the steps of `l1`. -/
theorem wk_app : ∀ (l1 l2 : List Blk), Chain r s (l1 ++ l2) → l2 ≠ [] →
    ∀ m, wk r s (l1 ++ l2) (tot l1 + m) = wk r s l2 m
  | [], l2, _, _, m => by simp [tot]
  | a :: l1, l2, h, hne, m => by
    obtain ⟨x, l', hx⟩ : ∃ x l', l1 ++ l2 = x :: l' := by
      cases h' : l1 ++ l2 with
      | nil => simp at h'; exact (hne h'.2).elim
      | cons x l' => exact ⟨x, l', rfl⟩
    have h' : Chain r s (l1 ++ l2) := by
      simp only [List.cons_append] at h; rw [hx] at h ⊢; exact h.2.2.2
    simp only [List.cons_append, tot]
    rw [hx, show 2 * a.L + tot l1 + m = 2 * a.L + (tot l1 + m) by ring, wk_tail, ← hx]
    exact wk_app l1 l2 h' hne m

/-- A suffix of a chain is a chain. -/
theorem chain_suffix : ∀ (pre l : List Blk), l ≠ [] → Chain r s (pre ++ l) → Chain r s l
  | [], l, _, h => by simpa using h
  | a :: pre, l, hne, h => by
    apply chain_suffix pre l hne
    obtain ⟨x, l', hx⟩ : ∃ x l', pre ++ l = x :: l' := by
      cases h' : pre ++ l with
      | nil => simp at h'; exact (hne h'.2).elim
      | cons x l' => exact ⟨x, l', rfl⟩
    simp only [List.cons_append] at h
    rw [hx] at h ⊢; exact h.2.2.2

/-- Four-block groups. -/
def grp (g0 g1 g2 g3 : ℕ → Blk) (j : ℕ) : List Blk := [g0 j, g1 j, g2 j, g3 j]

theorem laps_ex (g0 g1 g2 g3 : ℕ → Blk) (st : List Blk) (p : Blk) :
    ∀ n, ∃ l, st ++ [p] ++ laps (grp g0 g1 g2 g3) n = l ++ [if n = 0 then p else g3 (n - 1)]
  | 0 => ⟨st, by simp [laps]⟩
  | n + 1 => by
    obtain ⟨l, hl⟩ := laps_ex g0 g1 g2 g3 st p n
    refine ⟨st ++ [p] ++ laps (grp g0 g1 g2 g3) n ++ [g0 n, g1 n, g2 n], ?_⟩
    simp [laps, grp]

/-- **Chains of four-block groups.** -/
theorem chain_gen (g0 g1 g2 g3 : ℕ → Blk) (st : List Blk) (p : Blk) (n : ℕ) (fin : List Blk)
    (f0 : Blk) (hfin : fin ≠ []) (hf0 : fin.head hfin = f0)
    (hst : Chain r s (st ++ [p])) (hG : ∀ j, j < n → Chain r s [g0 j, g1 j, g2 j, g3 j])
    (hj0 : 0 < n → Junc r s p (g0 0)) (hjj : ∀ j, j + 1 < n → Junc r s (g3 j) (g0 (j + 1)))
    (hF : Chain r s fin) (hjf : Junc r s (if n = 0 then p else g3 (n - 1)) f0) :
    Chain r s (st ++ [p] ++ laps (grp g0 g1 g2 g3) n ++ fin) := by
  have key : ∀ m, m ≤ n → Chain r s (st ++ [p] ++ laps (grp g0 g1 g2 g3) m) := by
    intro m hm
    induction m with
    | zero => simpa [laps] using hst
    | succ m ih =>
      obtain ⟨l, hl⟩ := laps_ex g0 g1 g2 g3 st p m
      have h1 := ih (by omega)
      rw [hl] at h1
      have hG' := hG m (by omega)
      have hj : Junc r s (if m = 0 then p else g3 (m - 1)) (g0 m) := by
        split_ifs with h
        · subst h; exact hj0 (by omega)
        · have := hjj (m - 1) (by omega); rwa [show m - 1 + 1 = m by omega] at this
      have := chain_app l _ [g1 m, g2 m, g3 m] (g0 m) h1 hG' hj
      have e : st ++ [p] ++ laps (grp g0 g1 g2 g3) (m + 1) =
          l ++ [if m = 0 then p else g3 (m - 1)] ++ g0 m :: [g1 m, g2 m, g3 m] := by
        rw [laps, ← hl]; simp [grp]
      rw [e]; exact this
  obtain ⟨l, hl⟩ := laps_ex g0 g1 g2 g3 st p n
  have h1 := key n le_rfl
  rw [hl] at h1 ⊢
  obtain ⟨fl, hfl⟩ : ∃ fl, fin = f0 :: fl := by
    cases fin with
    | nil => exact (hfin rfl).elim
    | cons x fl => exact ⟨fl, by simp at hf0; rw [hf0]⟩
  subst hfl
  exact chain_app l _ fl f0 h1 hF hjf

theorem mem_laps_grp {g0 g1 g2 g3 : ℕ → Blk} {b : Blk} {n : ℕ}
    (h : b ∈ laps (grp g0 g1 g2 g3) n) :
    ∃ j, j < n ∧ (b = g0 j ∨ b = g1 j ∨ b = g2 j ∨ b = g3 j) := by
  obtain ⟨j, hj, hb⟩ := mem_laps _ n h
  simp only [grp, List.mem_cons, List.not_mem_nil, or_false] at hb
  exact ⟨j, hj, hb⟩

theorem forall_laps_grp {P : Blk → Prop} {g0 g1 g2 g3 : ℕ → Blk} {n : ℕ}
    (h : ∀ j, j < n → P (g0 j) ∧ P (g1 j) ∧ P (g2 j) ∧ P (g3 j)) :
    ∀ b ∈ laps (grp g0 g1 g2 g3) n, P b := by
  intro b hb
  obtain ⟨j, hj, hb⟩ := mem_laps_grp hb
  obtain ⟨a0, a1, a2, a3⟩ := h j hj
  rcases hb with rfl | rfl | rfl | rfl <;> assumption

/-- **Repetition kill, split form.** -/
theorem kill_split (hr : 2 ≤ r) (hs : 2 ≤ s) (pre mid : List Blk) (bl : Blk)
    (hch : Chain r s (pre ++ (mid ++ [bl]))) (i1 : ℕ) (hi1 : i1 < (mid ++ [bl]).length)
    (m1 m2 : ℕ) (hm1 : m1 ≤ 2 * ((mid ++ [bl]).get ⟨i1, hi1⟩).L) (hm2 : m2 ≤ 2 * bl.L)
    (hlt : tot ((mid ++ [bl]).take i1) + m1 < tot mid + m2)
    (hrep : ((mid ++ [bl]).get ⟨i1, hi1⟩).pt r s m1 = bl.pt r s m2)
    (hodd : ∀ b ∈ pre ++ mid, ∀ i, i < b.L → ¬ IsCorner r s (b.pt r s (2 * i + 1)))
    (hoddl : ∀ i, 2 * i + 1 < m2 → ¬ IsCorner r s (bl.pt r s (2 * i + 1)))
    (b0 : Blk) (l0 : List Blk) (he : pre ++ (mid ++ [bl]) = b0 :: l0)
    {n : ℕ} {p : ℕ → MS r s} (hp : LiteralPath (GM r s) n p) (h0 : (p 0).1 = b0.pt r s 0)
    (h1 : (p 1).1 = b0.pt r s 1) (h2 : (p 2).1 = b0.pt r s 2) : False := by
  have hS := strip_of_chain _ hch
  have hch2 : Chain r s (mid ++ [bl]) := chain_suffix pre (mid ++ [bl]) (by simp) hch
  have hne : mid ++ [bl] ≠ [] := by simp
  have happ := wk_app pre (mid ++ [bl]) hch hne
  have hlen : mid.length < (mid ++ [bl]).length := by simp
  have hj := wk_at _ hch2 mid.length hlen m2 (by simpa using hm2)
  have htk : (mid ++ [bl]).take mid.length = mid := by simp
  rw [htk] at hj
  simp only [List.get_eq_getElem, List.getElem_append_right (le_refl _), Nat.sub_self,
    List.getElem_cons_zero] at hj
  have hi := wk_at _ hch2 i1 hi1 m1 hm1
  have hch0 : Chain r s (b0 :: l0) := he ▸ hch
  have hL0 := chain_head_L hch0
  have hw : ∀ m, m ≤ 2 → wk r s (pre ++ (mid ++ [bl])) m = b0.pt r s m := by
    intro m hm; rw [he]; exact wk_head hch0 m (by omega)
  have hN : tot pre + (tot mid + m2) ≤ tot (pre ++ (mid ++ [bl])) := by
    rw [tot_append, tot_append]; simp [tot]; omega
  have hlt' : tot pre + (tot ((mid ++ [bl]).take i1) + m1) < tot pre + (tot mid + m2) := by omega
  refine kill_rep hr hs hS hlt' hN (by rw [happ, happ, hi, hj, hrep]) ?_ hp
    (by rw [hw 0 (by norm_num), h0]) (by rw [hw 1 (by norm_num), h1]) (by rw [hw 2 (by norm_num), h2])
  intro k hk hko
  have := odd_wk (pre ++ mid) bl (by simpa using hch) hodd m2 hoddl k
    (by rw [tot_append]; omega) hko
  simpa using this

end Claude7D12
