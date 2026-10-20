import Formal.Claude5D14Strip

/-!
# D14 model: closed strips kill literal paths (`r, s ≥ 2`)

Written by a Claude worker (2026-10-20, D14 bridge session), adapting `Claude5O2Kill.lean`.

* `IsCornerPos`, `corner_pos` : a corner seen in a chart sits at a corner of the cell polygon;
* `IsCStrip W N` : a closed strip of period `N`, corners only at even indices;
* `cstrip_of_chain` : a chain of blocks closed up by repeating its first block;
* `kill_fwd`, `kill_bwd` : no literal path starts along a closed strip at an even index.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5D14

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

/-- The twelve corner positions of each cell polygon (label order). -/
def IsCornerPos (r s : ℤ) : ℕ → ℤ × ℤ → Prop
  | 0, p => (p.1 = (0) ∧ p.2 = (0)) ∨
      (p.1 = (s) ∧ p.2 = (0)) ∨
      (p.1 = (s) ∧ p.2 = (r)) ∨
      (p.1 = (s) ∧ p.2 = (r + s)) ∨
      (p.1 = (s) ∧ p.2 = (2 * r + s)) ∨
      (p.1 = (0) ∧ p.2 = (2 * r + 2 * s)) ∨
      (p.1 = (-r) ∧ p.2 = (2 * r + 2 * s)) ∨
      (p.1 = (-r - s) ∧ p.2 = (2 * r + 2 * s)) ∨
      (p.1 = (-2 * r - s) ∧ p.2 = (2 * r + 2 * s)) ∨
      (p.1 = (-2 * r - s) ∧ p.2 = (2 * r + s)) ∨
      (p.1 = (-r - s) ∧ p.2 = (r + s)) ∨
      (p.1 = (-r) ∧ p.2 = (r))
  | _, p => (p.1 = (0) ∧ p.2 = (0)) ∨
      (p.1 = (-s) ∧ p.2 = (0)) ∨
      (p.1 = (-r - s) ∧ p.2 = (0)) ∨
      (p.1 = (-r - 2 * s) ∧ p.2 = (s)) ∨
      (p.1 = (-r - 2 * s) ∧ p.2 = (r + s)) ∨
      (p.1 = (-r - 2 * s) ∧ p.2 = (r + 2 * s)) ∨
      (p.1 = (-r - 2 * s) ∧ p.2 = (2 * r + 2 * s)) ∨
      (p.1 = (-r - s) ∧ p.2 = (2 * r + 2 * s)) ∨
      (p.1 = (-s) ∧ p.2 = (r + 2 * s)) ∨
      (p.1 = (0) ∧ p.2 = (r + s)) ∨
      (p.1 = (r) ∧ p.2 = (s)) ∨
      (p.1 = (r) ∧ p.2 = (0))

theorem P0_lab0 (hr : 1 ≤ r) (hs : 1 ≤ s) : P0 r s (0) = ((0), (0)) := by
  unfold P0; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P1_lab0 (hr : 1 ≤ r) (hs : 1 ≤ s) : P1 r s (0) = ((0), (0)) := by
  unfold P1; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P0_lab1 (hr : 1 ≤ r) (hs : 1 ≤ s) : P0 r s (s) = ((s), (0)) := by
  unfold P0; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P1_lab1 (hr : 1 ≤ r) (hs : 1 ≤ s) : P1 r s (s) = ((-s), (0)) := by
  unfold P1; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P0_lab2 (hr : 1 ≤ r) (hs : 1 ≤ s) : P0 r s (r + s) = ((s), (r)) := by
  unfold P0; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P1_lab2 (hr : 1 ≤ r) (hs : 1 ≤ s) : P1 r s (r + s) = ((-r - s), (0)) := by
  unfold P1; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P0_lab3 (hr : 1 ≤ r) (hs : 1 ≤ s) : P0 r s (r + 2 * s) = ((s), (r + s)) := by
  unfold P0; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P1_lab3 (hr : 1 ≤ r) (hs : 1 ≤ s) : P1 r s (r + 2 * s) = ((-r - 2 * s), (s)) := by
  unfold P1; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P0_lab4 (hr : 1 ≤ r) (hs : 1 ≤ s) : P0 r s (2 * r + 2 * s) = ((s), (2 * r + s)) := by
  unfold P0; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P1_lab4 (hr : 1 ≤ r) (hs : 1 ≤ s) : P1 r s (2 * r + 2 * s) = ((-r - 2 * s), (r + s)) := by
  unfold P1; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P0_lab5 (hr : 1 ≤ r) (hs : 1 ≤ s) : P0 r s (2 * r + 3 * s) = ((0), (2 * r + 2 * s)) := by
  unfold P0; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P1_lab5 (hr : 1 ≤ r) (hs : 1 ≤ s) : P1 r s (2 * r + 3 * s) = ((-r - 2 * s), (r + 2 * s)) := by
  unfold P1; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P0_lab6 (hr : 1 ≤ r) (hs : 1 ≤ s) : P0 r s (3 * r + 3 * s) = ((-r), (2 * r + 2 * s)) := by
  unfold P0; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P1_lab6 (hr : 1 ≤ r) (hs : 1 ≤ s) : P1 r s (3 * r + 3 * s) = ((-r - 2 * s), (2 * r + 2 * s)) := by
  unfold P1; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P0_lab7 (hr : 1 ≤ r) (hs : 1 ≤ s) : P0 r s (3 * r + 4 * s) = ((-r - s), (2 * r + 2 * s)) := by
  unfold P0; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P1_lab7 (hr : 1 ≤ r) (hs : 1 ≤ s) : P1 r s (3 * r + 4 * s) = ((-r - s), (2 * r + 2 * s)) := by
  unfold P1; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P0_lab8 (hr : 1 ≤ r) (hs : 1 ≤ s) : P0 r s (4 * r + 4 * s) = ((-2 * r - s), (2 * r + 2 * s)) := by
  unfold P0; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P1_lab8 (hr : 1 ≤ r) (hs : 1 ≤ s) : P1 r s (4 * r + 4 * s) = ((-s), (r + 2 * s)) := by
  unfold P1; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P0_lab9 (hr : 1 ≤ r) (hs : 1 ≤ s) : P0 r s (4 * r + 5 * s) = ((-2 * r - s), (2 * r + s)) := by
  unfold P0; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P1_lab9 (hr : 1 ≤ r) (hs : 1 ≤ s) : P1 r s (4 * r + 5 * s) = ((0), (r + s)) := by
  unfold P1; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P0_lab10 (hr : 1 ≤ r) (hs : 1 ≤ s) : P0 r s (5 * r + 5 * s) = ((-r - s), (r + s)) := by
  unfold P0; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P1_lab10 (hr : 1 ≤ r) (hs : 1 ≤ s) : P1 r s (5 * r + 5 * s) = ((r), (s)) := by
  unfold P1; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P0_lab11 (hr : 1 ≤ r) (hs : 1 ≤ s) : P0 r s (5 * r + 6 * s) = ((-r), (r)) := by
  unfold P0; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)
theorem P1_lab11 (hr : 1 ≤ r) (hs : 1 ≤ s) : P1 r s (5 * r + 6 * s) = ((r), (0)) := by
  unfold P1; split_ifs <;> first | (exfalso; omega) | (ext <;> simp only <;> omega)

theorem corner_pos (hr : 1 ≤ r) (hs : 1 ≤ s) {c : ℕ} (hc : c < 2) {p : ℤ × ℤ}
    (hp : Dom r s c p) (h : IsCorner r s (ch r s c p)) : IsCornerPos r s c p := by
  rcases c_cases hc with rfl | rfl
  · by_cases hI : I0 r s p
    · rw [ch0_I hI] at h; simp [IsCorner, corners] at h
    · rw [ch0_B hI] at h
      have e := eq_P0 hr hs hp hI
      simp only [IsCorner, corners, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
        true_and, and_true] at h
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at e <;> rw [e]
      · rw [P0_lab0 hr hs]; simp [IsCornerPos]
      · rw [P0_lab1 hr hs]; simp [IsCornerPos]
      · rw [P0_lab2 hr hs]; simp [IsCornerPos]
      · rw [P0_lab3 hr hs]; simp [IsCornerPos]
      · rw [P0_lab4 hr hs]; simp [IsCornerPos]
      · rw [P0_lab5 hr hs]; simp [IsCornerPos]
      · rw [P0_lab6 hr hs]; simp [IsCornerPos]
      · rw [P0_lab7 hr hs]; simp [IsCornerPos]
      · rw [P0_lab8 hr hs]; simp [IsCornerPos]
      · rw [P0_lab9 hr hs]; simp [IsCornerPos]
      · rw [P0_lab10 hr hs]; simp [IsCornerPos]
      · rw [P0_lab11 hr hs]; simp [IsCornerPos]
  · by_cases hI : I1 r s p
    · rw [ch1_I hI] at h; simp [IsCorner, corners] at h
    · rw [ch1_B hI] at h
      have e := eq_P1 hr hs hp hI
      simp only [IsCorner, corners, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq,
        true_and, and_true] at h
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at e <;> rw [e]
      · rw [P1_lab0 hr hs]; simp [IsCornerPos]
      · rw [P1_lab1 hr hs]; simp [IsCornerPos]
      · rw [P1_lab2 hr hs]; simp [IsCornerPos]
      · rw [P1_lab3 hr hs]; simp [IsCornerPos]
      · rw [P1_lab4 hr hs]; simp [IsCornerPos]
      · rw [P1_lab5 hr hs]; simp [IsCornerPos]
      · rw [P1_lab6 hr hs]; simp [IsCornerPos]
      · rw [P1_lab7 hr hs]; simp [IsCornerPos]
      · rw [P1_lab8 hr hs]; simp [IsCornerPos]
      · rw [P1_lab9 hr hs]; simp [IsCornerPos]
      · rw [P1_lab10 hr hs]; simp [IsCornerPos]
      · rw [P1_lab11 hr hs]; simp [IsCornerPos]

/-! ## Closed strips -/

/-- A closed strip of period `N` whose corners have even indices. -/
def IsCStrip (r s : ℤ) (W : ℕ → MV) (N : ℕ) : Prop :=
  4 ≤ N ∧ Even N ∧ (∀ k, W (k + N) = W k) ∧ (∀ k, Valid r s (W k)) ∧
    (∀ k, AdjM r s (W k) (W (k + 1))) ∧ (∀ k, AdjM r s (W k) (W (k + 2))) ∧
    (∀ k, W (k + 3) ≠ W k) ∧ (∀ k, IsCorner r s (W k) → Even k)

theorem cs_mul {W : ℕ → MV} {N : ℕ} (h : IsCStrip r s W N) (k q : ℕ) : W (k + N * q) = W k := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← add_assoc, h.2.2.1, ih]

theorem forced_fwd (hr : 2 ≤ r) (hs : 2 ≤ s) {W : ℕ → MV} {N : ℕ} (hW : IsCStrip r s W N)
    {s0 : ℕ} {n : ℕ} {p : ℕ → MS r s} (hp : LiteralPath (GM r s) n p) (h0 : (p 0).1 = W s0)
    (h1 : (p 1).1 = W (s0 + 1)) (h2 : (p 2).1 = W (s0 + 2)) : ∀ k, k < n → (p k).1 = W (s0 + k) := by
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
      have a12 : AdjM r s (p (j + 1)).1 (p (j + 2)).1 := hp1 (j + 1) (by omega)
      have a01 : AdjM r s (p (j + 1)).1 (p j).1 := adjM_symm (hp1 j (by omega))
      have a02 : AdjM r s (p (j + 2)).1 (p j).1 := adjM_symm (hp2 j (by omega))
      have a13 : AdjM r s (p (j + 1)).1 (p (j + 3)).1 := hp2 (j + 1) (by omega)
      have a23 : AdjM r s (p (j + 2)).1 (p (j + 3)).1 := hp1 (j + 2) (by omega)
      have w13 : AdjM r s (p (j + 1)).1 (W (s0 + (j + 3))) := by
        rw [e1, show s0 + (j + 3) = s0 + (j + 1) + 2 by omega]; exact hS2 _
      have w23 : AdjM r s (p (j + 2)).1 (W (s0 + (j + 3))) := by
        rw [e2, show s0 + (j + 3) = s0 + (j + 2) + 1 by omega]; exact hS1 _
      have n1 : (p j).1 ≠ W (s0 + (j + 3)) := by
        rw [e0, show s0 + (j + 3) = s0 + j + 3 by omega]; exact (hS3 _).symm
      have n2 : (p j).1 ≠ (p (j + 3)).1 := fun e => by
        have := hinj j (j + 3) (by omega) (by omega) (Subtype.ext e); omega
      exact no_three (by omega) (by omega) a12 a01 a02 w13 w23 a13 a23 n1 n2 (fun e => hne e.symm)

theorem forced_bwd (hr : 2 ≤ r) (hs : 2 ≤ s) {W : ℕ → MV} {N : ℕ} (hW : IsCStrip r s W N)
    {s0 : ℕ} {n : ℕ} {p : ℕ → MS r s} (hp : LiteralPath (GM r s) n p) (hs0 : n + 2 ≤ s0)
    (h0 : (p 0).1 = W s0) (h1 : (p 1).1 = W (s0 - 1)) (h2 : (p 2).1 = W (s0 - 2)) :
    ∀ k, k < n → (p k).1 = W (s0 - k) := by
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
      have a12 : AdjM r s (p (j + 1)).1 (p (j + 2)).1 := hp1 (j + 1) (by omega)
      have a01 : AdjM r s (p (j + 1)).1 (p j).1 := adjM_symm (hp1 j (by omega))
      have a02 : AdjM r s (p (j + 2)).1 (p j).1 := adjM_symm (hp2 j (by omega))
      have a13 : AdjM r s (p (j + 1)).1 (p (j + 3)).1 := hp2 (j + 1) (by omega)
      have a23 : AdjM r s (p (j + 2)).1 (p (j + 3)).1 := hp1 (j + 2) (by omega)
      have w13 : AdjM r s (p (j + 1)).1 (W (s0 - (j + 3))) := by
        rw [e1, show s0 - (j + 1) = s0 - (j + 3) + 2 by omega]; exact adjM_symm (hS2 _)
      have w23 : AdjM r s (p (j + 2)).1 (W (s0 - (j + 3))) := by
        rw [e2, show s0 - (j + 2) = s0 - (j + 3) + 1 by omega]; exact adjM_symm (hS1 _)
      have n1 : (p j).1 ≠ W (s0 - (j + 3)) := by
        rw [e0, show s0 - j = s0 - (j + 3) + 3 by omega]; exact hS3 _
      have n2 : (p j).1 ≠ (p (j + 3)).1 := fun e => by
        have := hinj j (j + 3) (by omega) (by omega) (Subtype.ext e); omega
      exact no_three (by omega) (by omega) a12 a01 a02 w13 w23 a13 a23 n1 n2 (fun e => hne e.symm)

theorem end_corner (hr : 2 ≤ r) (hs : 2 ≤ s) {n : ℕ} {p : ℕ → MS r s}
    (hp : LiteralPath (GM r s) n p) : IsCorner r s (p (n - 1)).1 ∧ 4 ≤ n ∧ Even n :=
  ⟨deg_five hr hs _ hp.2.2.2.2.2.2.1, hp.1, hp.2.1⟩

/-- **Forward kill.** -/
theorem kill_fwd (hr : 2 ≤ r) (hs : 2 ≤ s) {W : ℕ → MV} {N : ℕ} (hW : IsCStrip r s W N)
    {s0 : ℕ} (hs0 : Even s0) {n : ℕ} {p : ℕ → MS r s} (hp : LiteralPath (GM r s) n p)
    (h0 : (p 0).1 = W s0) (h1 : (p 1).1 = W (s0 + 1)) (h2 : (p 2).1 = W (s0 + 2)) : False := by
  have hf := forced_fwd hr hs hW hp h0 h1 h2
  obtain ⟨hc, h4, hn⟩ := end_corner hr hs hp
  rw [hf (n - 1) (by omega)] at hc
  have := hW.2.2.2.2.2.2.2 _ hc
  obtain ⟨a, ha⟩ := hs0; obtain ⟨b, hb⟩ := hn; obtain ⟨c, hc'⟩ := this
  omega

/-- **Backward kill.** -/
theorem kill_bwd (hr : 2 ≤ r) (hs : 2 ≤ s) {W : ℕ → MV} {N : ℕ} (hW : IsCStrip r s W N)
    {s0 : ℕ} (hs0 : Even s0) {n : ℕ} {p : ℕ → MS r s} (hp : LiteralPath (GM r s) n p)
    (h0 : (p 0).1 = W s0) (h1 : (p 1).1 = W (s0 + N - 1)) (h2 : (p 2).1 = W (s0 + N - 2)) :
    False := by
  have hN := hW.1
  set S := s0 + N * (n + 2) with hS
  have hSn : n + 2 ≤ S := by
    have : n + 2 ≤ N * (n + 2) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have g0 : (p 0).1 = W S := by rw [h0, hS, cs_mul hW]
  have g1 : (p 1).1 = W (S - 1) := by
    rw [h1, show S - 1 = s0 + N - 1 + N * (n + 1) by rw [hS, Nat.mul_succ]; omega, cs_mul hW]
  have g2 : (p 2).1 = W (S - 2) := by
    rw [h2, show S - 2 = s0 + N - 2 + N * (n + 1) by rw [hS, Nat.mul_succ]; omega, cs_mul hW]
  have hf := forced_bwd hr hs hW hp hSn g0 g1 g2
  obtain ⟨hc, h4, hn⟩ := end_corner hr hs hp
  rw [hf (n - 1) (by omega)] at hc
  have := hW.2.2.2.2.2.2.2 _ hc
  obtain ⟨a, ha⟩ := hs0; obtain ⟨b, hb⟩ := hn; obtain ⟨c, hc'⟩ := this
  obtain ⟨e, he⟩ := hW.2.1
  have : S = s0 + N * (n + 2) := hS
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

theorem chain_tail {b : Blk} {l : List Blk} (h : Chain r s (b :: l)) (hl : l ≠ []) :
    Chain r s l := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons b' l => exact h.2.2.2

theorem odd_chain : ∀ (bs tail : List Blk), Chain r s (bs ++ tail) → tail ≠ [] →
    (∀ b ∈ bs, ∀ i, i < b.L → ¬ IsCorner r s (b.pt r s (2 * i + 1))) →
    ∀ q, q < tot bs → IsCorner r s (wk r s (bs ++ tail) q) → Even q
  | [], _, _, _, _, q, hq, _ => by simp [tot] at hq
  | b :: bs, tail, hch, htl, hodd, q, hq, hc => by
    simp only [List.cons_append] at hch hc
    by_cases h1 : q < 2 * b.L
    · rw [wk_head hch q (by omega)] at hc
      obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' q
      · exact ⟨i, by ring⟩
      · exact ((hodd b (by simp) i (by omega)) hc).elim
    · have hne : bs ++ tail ≠ [] := by simp [htl]
      obtain ⟨q', rfl⟩ : ∃ q', q = 2 * b.L + q' := ⟨q - 2 * b.L, by omega⟩
      obtain ⟨b', l', hl'⟩ : ∃ b' l', bs ++ tail = b' :: l' := by
        cases h : bs ++ tail with
        | nil => exact (hne h).elim
        | cons b' l' => exact ⟨b', l', rfl⟩
      rw [hl', wk_tail, ← hl'] at hc
      have ih := odd_chain bs tail (chain_tail hch hne) htl
        (fun b'' hb'' => hodd b'' (by simp [hb''])) q' (by simp [tot] at hq; omega) hc
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
theorem cstrip_of_chain (hr : 1 ≤ r) (bs : List Blk) (b0 : Blk) (rest : List Blk)
    (hbs : bs = b0 :: rest) (hch : Chain r s (bs ++ [b0])) (hN : 4 ≤ tot bs)
    (hodd : ∀ b ∈ bs, ∀ i, i < b.L → ¬ IsCorner r s (b.pt r s (2 * i + 1))) :
    IsCStrip r s (fun k => wk r s (bs ++ [b0]) (k % tot bs)) (tot bs) := by
  set N := tot bs with hNdef
  set V := wk r s (bs ++ [b0]) with hVdef
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
  have hq : ∀ k, k % N + 3 ≤ N + 2 * b0.L := fun k => by
    have := Nat.mod_lt k hNpos; omega
  obtain ⟨e, he⟩ := tot_even bs
  refine ⟨hN, tot_even bs, fun k => by simp, fun k => hS.1 _ (by have := hq k; omega),
    fun k => ?_, fun k => ?_, fun k => ?_, fun k hk => ?_⟩
  · show AdjM r s (V (k % N)) (V ((k + 1) % N))
    rw [shift k 1 (by norm_num)]; exact hS.2.1 _ (by have := hq k; omega)
  · show AdjM r s (V (k % N)) (V ((k + 2) % N))
    rw [shift k 2 (by norm_num)]; exact hS.2.2.1 _ (by have := hq k; omega)
  · show V ((k + 3) % N) ≠ V (k % N)
    rw [shift k 3 (by norm_num)]; exact hS.2.2.2 _ (hq k)
  · have := odd_chain bs [b0] hch (by simp) hodd (k % N) (Nat.mod_lt _ hNpos) hk
    obtain ⟨c, hc⟩ := this
    have h1 := Nat.mod_add_div k N
    refine ⟨c + e * (k / N), ?_⟩
    generalize k / N = q at h1 ⊢
    have he' : N = e + e := by rw [hNdef]; exact he
    rw [hc, he'] at h1
    linarith

end Claude5D14
