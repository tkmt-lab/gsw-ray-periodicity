import Formal.Claude5O2Strip

/-!
# O2 model: closed strips kill literal paths (`t, d ≥ 2`)

Written by a Claude worker (2026-10-20, O2 bridge session).

* `IsCornerPos`, `corner_pos` : a corner seen in a chart sits at a corner of the chart;
* `IsCStrip W N` : a closed strip of period `N`, corners only at even indices;
* `cstrip_of_chain` : a chain of blocks closed up by repeating its first block;
* `kill_fwd`, `kill_bwd` : no literal path starts along a closed strip at an even index.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

variable {t d : ℤ}

/-- The nine corner positions of a hexagon chart, the four corners of a rhombus chart. -/
def IsCornerPos (t d : ℤ) : ℕ → ℤ × ℤ → Prop
  | 0, p => (p.1 = 0 ∧ p.2 = 0) ∨ (p.1 = t ∧ p.2 = 0) ∨ (p.1 = 2 * t ∧ p.2 = 0) ∨
      (p.1 = 2 * t ∧ p.2 = d) ∨ (p.1 = t ∧ p.2 = t + d) ∨ (p.1 = 0 ∧ p.2 = 2 * t + d) ∨
      (p.1 = -d ∧ p.2 = 2 * t + d) ∨ (p.1 = -d ∧ p.2 = t + d) ∨ (p.1 = -d ∧ p.2 = d)
  | 1, p => (p.1 = 0 ∧ p.2 = 0) ∨ (p.1 = t ∧ p.2 = 0) ∨ (p.1 = 2 * t ∧ p.2 = 0) ∨
      (p.1 = 2 * t ∧ p.2 = d) ∨ (p.1 = t ∧ p.2 = t + d) ∨ (p.1 = 0 ∧ p.2 = 2 * t + d) ∨
      (p.1 = -d ∧ p.2 = 2 * t + d) ∨ (p.1 = -d ∧ p.2 = t + d) ∨ (p.1 = -d ∧ p.2 = d)
  | _ + 2, p => (p.1 = 0 ∨ p.1 = t) ∧ (p.2 = 0 ∨ p.2 = t)

theorem corner_cases {v : MV} (h : IsCorner t d v) : ∃ k : ℤ, ∃ j : ℕ, ∃ l : ℤ, j < 3 ∧
    (k = 0 ∨ k = 1) ∧ (l = 0 ∨ l = t ∨ l = 2 * t) ∧ v = (k, sp t d j l) := by
  simp only [IsCorner, corners, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
  exacts [⟨0, 0, 0, by norm_num⟩, ⟨0, 0, t, by norm_num⟩, ⟨0, 0, 2 * t, by norm_num⟩,
    ⟨1, 0, t, by norm_num⟩, ⟨0, 1, 0, by norm_num⟩, ⟨0, 1, t, by norm_num⟩,
    ⟨0, 1, 2 * t, by norm_num⟩, ⟨1, 1, t, by norm_num⟩, ⟨0, 2, 0, by norm_num⟩,
    ⟨0, 2, t, by norm_num⟩, ⟨0, 2, 2 * t, by norm_num⟩, ⟨1, 2, t, by norm_num⟩]

theorem corner_pos (ht : 1 ≤ t) (hd : 1 ≤ d) {c : ℕ} (hc : c < 5) {p : ℤ × ℤ}
    (hp : Dom t d c p) (h : IsCorner t d (ch t d c p)) : IsCornerPos t d c p := by
  obtain ⟨k, j, l, hj, hk, hl, e⟩ := corner_cases h
  rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩
  · rw [ch0] at e
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    simp only [IsCornerPos]
    interval_cases j <;> rcases hl with h | h | h <;> subst h <;> simp [sp] <;> omega
  · have e2 : p = sp t d j l := congrArg Prod.snd e
    subst e2
    simp only [IsCornerPos]
    interval_cases j <;> rcases hl with h | h | h <;> subst h <;> simp [sp] <;> omega
  · simp only [Dom] at hp
    by_cases hI : RhI t p
    · rw [chR_int i hI] at e
      have := congrArg Prod.fst e
      simp at this; omega
    · rw [chR_bd i hI] at e
      simp only [Prod.mk.injEq] at e
      have hr := rl_range hp hI
      have hij := sides_disj ht hd (by omega) hj hr.1 hr.2 (by omega) (by omega) e.2
      subst hij
      have hll := sp_inj hj e.2
      simp only [IsCornerPos]
      simp only [Rh, RhI] at hp hI
      unfold rl at hll
      split_ifs at hll <;> omega

/-! ## Closed strips -/

/-- A closed strip of period `N` whose corners have even indices. -/
def IsCStrip (t d : ℤ) (W : ℕ → MV) (N : ℕ) : Prop :=
  4 ≤ N ∧ Even N ∧ (∀ k, W (k + N) = W k) ∧ (∀ k, Valid t d (W k)) ∧
    (∀ k, AdjM t d (W k) (W (k + 1))) ∧ (∀ k, AdjM t d (W k) (W (k + 2))) ∧
    (∀ k, W (k + 3) ≠ W k) ∧ (∀ k, IsCorner t d (W k) → Even k)

theorem cs_mul {W : ℕ → MV} {N : ℕ} (h : IsCStrip t d W N) (k q : ℕ) : W (k + N * q) = W k := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← add_assoc, h.2.2.1, ih]

theorem forced_fwd (ht : 2 ≤ t) (hd : 2 ≤ d) {W : ℕ → MV} {N : ℕ} (hW : IsCStrip t d W N)
    {s : ℕ} {n : ℕ} {p : ℕ → MS t d} (hp : LiteralPath (GM t d) n p) (h0 : (p 0).1 = W s)
    (h1 : (p 1).1 = W (s + 1)) (h2 : (p 2).1 = W (s + 2)) : ∀ k, k < n → (p k).1 = W (s + k) := by
  obtain ⟨-, -, -, -, hS1, hS2, hS3, -⟩ := hW
  obtain ⟨h4, -, hinj, hp1, hp2, -⟩ := hp
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    match k, ih with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | j + 3, ih =>
      have e0 := ih j (by omega) (by omega)
      have e1 := ih (j + 1) (by omega) (by omega)
      have e2 := ih (j + 2) (by omega) (by omega)
      by_contra hne
      have a12 : AdjM t d (p (j + 1)).1 (p (j + 2)).1 := hp1 (j + 1) (by omega)
      have a01 : AdjM t d (p (j + 1)).1 (p j).1 := adjM_symm (hp1 j (by omega))
      have a02 : AdjM t d (p (j + 2)).1 (p j).1 := adjM_symm (hp2 j (by omega))
      have a13 : AdjM t d (p (j + 1)).1 (p (j + 3)).1 := hp2 (j + 1) (by omega)
      have a23 : AdjM t d (p (j + 2)).1 (p (j + 3)).1 := hp1 (j + 2) (by omega)
      have w13 : AdjM t d (p (j + 1)).1 (W (s + (j + 3))) := by
        rw [e1, show s + (j + 3) = s + (j + 1) + 2 by omega]; exact hS2 _
      have w23 : AdjM t d (p (j + 2)).1 (W (s + (j + 3))) := by
        rw [e2, show s + (j + 3) = s + (j + 2) + 1 by omega]; exact hS1 _
      have n1 : (p j).1 ≠ W (s + (j + 3)) := by
        rw [e0, show s + (j + 3) = s + j + 3 by omega]; exact (hS3 _).symm
      have n2 : (p j).1 ≠ (p (j + 3)).1 := fun e => by
        have := hinj j (j + 3) (by omega) (by omega) (Subtype.ext e); omega
      exact no_three ht hd a12 a01 a02 w13 w23 a13 a23 n1 n2 (fun e => hne e.symm)

theorem forced_bwd (ht : 2 ≤ t) (hd : 2 ≤ d) {W : ℕ → MV} {N : ℕ} (hW : IsCStrip t d W N)
    {s : ℕ} {n : ℕ} {p : ℕ → MS t d} (hp : LiteralPath (GM t d) n p) (hs : n + 2 ≤ s)
    (h0 : (p 0).1 = W s) (h1 : (p 1).1 = W (s - 1)) (h2 : (p 2).1 = W (s - 2)) :
    ∀ k, k < n → (p k).1 = W (s - k) := by
  obtain ⟨-, -, -, -, hS1, hS2, hS3, -⟩ := hW
  obtain ⟨h4, -, hinj, hp1, hp2, -⟩ := hp
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    match k, ih with
    | 0, _ => simpa using h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | j + 3, ih =>
      have e0 := ih j (by omega) (by omega)
      have e1 := ih (j + 1) (by omega) (by omega)
      have e2 := ih (j + 2) (by omega) (by omega)
      by_contra hne
      have a12 : AdjM t d (p (j + 1)).1 (p (j + 2)).1 := hp1 (j + 1) (by omega)
      have a01 : AdjM t d (p (j + 1)).1 (p j).1 := adjM_symm (hp1 j (by omega))
      have a02 : AdjM t d (p (j + 2)).1 (p j).1 := adjM_symm (hp2 j (by omega))
      have a13 : AdjM t d (p (j + 1)).1 (p (j + 3)).1 := hp2 (j + 1) (by omega)
      have a23 : AdjM t d (p (j + 2)).1 (p (j + 3)).1 := hp1 (j + 2) (by omega)
      have w13 : AdjM t d (p (j + 1)).1 (W (s - (j + 3))) := by
        rw [e1, show s - (j + 1) = s - (j + 3) + 2 by omega]; exact adjM_symm (hS2 _)
      have w23 : AdjM t d (p (j + 2)).1 (W (s - (j + 3))) := by
        rw [e2, show s - (j + 2) = s - (j + 3) + 1 by omega]; exact adjM_symm (hS1 _)
      have n1 : (p j).1 ≠ W (s - (j + 3)) := by
        rw [e0, show s - j = s - (j + 3) + 3 by omega]; exact hS3 _
      have n2 : (p j).1 ≠ (p (j + 3)).1 := fun e => by
        have := hinj j (j + 3) (by omega) (by omega) (Subtype.ext e); omega
      exact no_three ht hd a12 a01 a02 w13 w23 a13 a23 n1 n2 (fun e => hne e.symm)

theorem end_corner (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS t d}
    (hp : LiteralPath (GM t d) n p) : IsCorner t d (p (n - 1)).1 ∧ 4 ≤ n ∧ Even n :=
  ⟨deg_five ht hd _ hp.2.2.2.2.2.2.1, hp.1, hp.2.1⟩

/-- **Forward kill.** -/
theorem kill_fwd (ht : 2 ≤ t) (hd : 2 ≤ d) {W : ℕ → MV} {N : ℕ} (hW : IsCStrip t d W N)
    {s : ℕ} (hs : Even s) {n : ℕ} {p : ℕ → MS t d} (hp : LiteralPath (GM t d) n p)
    (h0 : (p 0).1 = W s) (h1 : (p 1).1 = W (s + 1)) (h2 : (p 2).1 = W (s + 2)) : False := by
  have hf := forced_fwd ht hd hW hp h0 h1 h2
  obtain ⟨hc, h4, hn⟩ := end_corner ht hd hp
  rw [hf (n - 1) (by omega)] at hc
  have := hW.2.2.2.2.2.2.2 _ hc
  obtain ⟨a, ha⟩ := hs; obtain ⟨b, hb⟩ := hn; obtain ⟨c, hc'⟩ := this
  omega

/-- **Backward kill.** -/
theorem kill_bwd (ht : 2 ≤ t) (hd : 2 ≤ d) {W : ℕ → MV} {N : ℕ} (hW : IsCStrip t d W N)
    {s : ℕ} (hs : Even s) {n : ℕ} {p : ℕ → MS t d} (hp : LiteralPath (GM t d) n p)
    (h0 : (p 0).1 = W s) (h1 : (p 1).1 = W (s + N - 1)) (h2 : (p 2).1 = W (s + N - 2)) :
    False := by
  have hN := hW.1
  set S := s + N * (n + 2) with hS
  have hSn : n + 2 ≤ S := by
    have : n + 2 ≤ N * (n + 2) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have g0 : (p 0).1 = W S := by rw [h0, hS, cs_mul hW]
  have g1 : (p 1).1 = W (S - 1) := by
    rw [h1, show S - 1 = s + N - 1 + N * (n + 1) by rw [hS, Nat.mul_succ]; omega, cs_mul hW]
  have g2 : (p 2).1 = W (S - 2) := by
    rw [h2, show S - 2 = s + N - 2 + N * (n + 1) by rw [hS, Nat.mul_succ]; omega, cs_mul hW]
  have hf := forced_bwd ht hd hW hp hSn g0 g1 g2
  obtain ⟨hc, h4, hn⟩ := end_corner ht hd hp
  rw [hf (n - 1) (by omega)] at hc
  have := hW.2.2.2.2.2.2.2 _ hc
  obtain ⟨a, ha⟩ := hs; obtain ⟨b, hb⟩ := hn; obtain ⟨c, hc'⟩ := this
  obtain ⟨e, he⟩ := hW.2.1
  have : S = s + N * (n + 2) := hS
  rw [he] at this
  have h2 : S - (n - 1) = c + c := hc'
  have : (e + e) * (n + 2) = 2 * (e * (n + 2)) := by ring
  omega

/-! ## Closing a chain -/

theorem tot_append (l l' : List Blk) : tot (l ++ l') = tot l + tot l' := by
  induction l with
  | nil => simp [tot]
  | cons b l ih => simp [tot, ih]; ring

theorem tot_even (l : List Blk) : Even (tot l) := by
  induction l with
  | nil => exact ⟨0, rfl⟩
  | cons b l ih => obtain ⟨k, hk⟩ := ih; exact ⟨b.L + k, by simp [tot, hk]; ring⟩

theorem chain_tail {b : Blk} {l : List Blk} (h : Chain t d (b :: l)) (hl : l ≠ []) :
    Chain t d l := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons b' l => exact h.2.2.2

theorem odd_chain : ∀ (bs tail : List Blk), Chain t d (bs ++ tail) → tail ≠ [] →
    (∀ b ∈ bs, ∀ i, i < b.L → ¬ IsCorner t d (b.pt t d (2 * i + 1))) →
    ∀ r, r < tot bs → IsCorner t d (wk t d (bs ++ tail) r) → Even r
  | [], _, _, _, _, r, hr, _ => by simp [tot] at hr
  | b :: bs, tail, hch, htl, hodd, r, hr, hc => by
    simp only [List.cons_append] at hch hc
    by_cases h1 : r < 2 * b.L
    · rw [wk_head hch r (by omega)] at hc
      obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' r
      · exact ⟨i, by ring⟩
      · exact ((hodd b (by simp) i (by omega)) hc).elim
    · have hne : bs ++ tail ≠ [] := by simp [htl]
      obtain ⟨r', rfl⟩ : ∃ r', r = 2 * b.L + r' := ⟨r - 2 * b.L, by omega⟩
      obtain ⟨b', l', hl'⟩ : ∃ b' l', bs ++ tail = b' :: l' := by
        cases h : bs ++ tail with
        | nil => exact (hne h).elim
        | cons b' l' => exact ⟨b', l', rfl⟩
      rw [hl', wk_tail, ← hl'] at hc
      have ih := odd_chain bs tail (chain_tail hch hne) htl
        (fun b'' hb'' => hodd b'' (by simp [hb''])) r' (by simp [tot] at hr; omega) hc
      obtain ⟨k, hk⟩ := ih
      exact ⟨b.L + k, by omega⟩

theorem mod_lt' {N k : ℕ} (hN : 0 < N) : k % N < N := Nat.mod_lt _ hN

theorem mod_add_small {N k j : ℕ} (hN : 0 < N) (hj : j ≤ N) :
    (k + j) % N = k % N + j ∨ ((k + j) % N + N = k % N + j) := by
  have h1 := Nat.mod_add_div k N
  have h2 := Nat.mod_lt k hN
  by_cases h : k % N + j < N
  · left
    rw [show k + j = (k % N + j) + N * (k / N) by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt h]
  · right
    rw [show k + j = (k % N + j - N) + N * (k / N + 1) by rw [Nat.mul_succ]; omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega

/-- **A closed strip from a chain closed up by its first block.** -/
theorem cstrip_of_chain (ht : 1 ≤ t) (bs : List Blk) (b0 : Blk) (rest : List Blk)
    (hbs : bs = b0 :: rest) (hch : Chain t d (bs ++ [b0])) (hN : 4 ≤ tot bs)
    (hodd : ∀ b ∈ bs, ∀ i, i < b.L → ¬ IsCorner t d (b.pt t d (2 * i + 1))) :
    IsCStrip t d (fun k => wk t d (bs ++ [b0]) (k % tot bs)) (tot bs) := by
  set N := tot bs with hNdef
  set V := wk t d (bs ++ [b0]) with hVdef
  have hS := strip_of_chain (bs ++ [b0]) hch
  rw [tot_append] at hS
  have htot1 : tot [b0] = 2 * b0.L := by simp [tot]
  rw [htot1] at hS
  have hL0 : 1 ≤ b0.L := by
    rw [hbs] at hch
    cases rest with
    | nil => exact hch.2.1
    | cons _ _ => exact hch.2.1
  have hlast : ∀ m, m ≤ 2 * b0.L → V (N + m) = V m := by
    intro m hm
    have h1 := wk_at (bs ++ [b0]) hch bs.length (by simp) m (by simpa using hm)
    have h2 : (bs ++ [b0]).take bs.length = bs := by simp
    rw [h2] at h1
    simp only [List.get_eq_getElem, List.getElem_append_right (le_refl _), Nat.sub_self,
      List.getElem_cons_zero] at h1
    rw [hVdef, h1]
    have h3 := wk_head (b := b0) (bs := rest ++ [b0]) (by rw [hbs] at hch; simpa using hch) m hm
    rw [hbs, List.cons_append, h3]
  have hNpos : 0 < N := by omega
  have shift : ∀ k j, j ≤ 3 → V ((k + j) % N) = V (k % N + j) := by
    intro k j hj
    rcases mod_add_small (k := k) hNpos (show j ≤ N by omega) with h | h
    · rw [h]
    · have h2 := Nat.mod_lt k hNpos
      have h3 := Nat.mod_lt (k + j) hNpos
      rw [show k % N + j = N + (k + j) % N by omega, hlast _ (by omega)]
  have hr : ∀ k, k % N + 3 ≤ N + 2 * b0.L := fun k => by
    have := Nat.mod_lt k hNpos; omega
  obtain ⟨e, he⟩ := tot_even bs
  refine ⟨hN, tot_even bs, fun k => by simp, fun k => hS.1 _ (by have := hr k; omega),
    fun k => ?_, fun k => ?_, fun k => ?_, fun k hk => ?_⟩
  · show AdjM t d (V (k % N)) (V ((k + 1) % N))
    rw [shift k 1 (by norm_num)]; exact hS.2.1 _ (by have := hr k; omega)
  · show AdjM t d (V (k % N)) (V ((k + 2) % N))
    rw [shift k 2 (by norm_num)]; exact hS.2.2.1 _ (by have := hr k; omega)
  · show V ((k + 3) % N) ≠ V (k % N)
    rw [shift k 3 (by norm_num)]; exact hS.2.2.2 _ (hr k)
  · have := odd_chain bs [b0] hch (by simp) hodd (k % N) (Nat.mod_lt _ hNpos) hk
    obtain ⟨c, hc⟩ := this
    have h1 := Nat.mod_add_div k N
    refine ⟨c + e * (k / N), ?_⟩
    generalize k / N = q at h1 ⊢
    have he' : N = e + e := by rw [hNdef]; exact he
    rw [hc, he'] at h1
    linarith

end Claude5O2
