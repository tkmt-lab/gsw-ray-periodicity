import Formal.Claude3SentDeg

/-!
# Theorem 1a, G6: the root passage atoms `PR q`

Written by a Claude worker (2026-10-20, Theorem 1a, parts G6/A).

For a root state the start index is pinned by the root corner (`PinOK`), and the exit index is
`hi` (its parity is fixed by the exit branch) or pinned by the terminal corner. So every root
passage atom is a formula in the height of the state alone.

* `QPar`, `q_par_iff` : for `q ≠ qT` the passage property depends on the indices only through
  their parities (and, for `qL`, on `i + 1 ≤ e`);
* `forall_exit_iff` : the exit index by cases;
* `prT`, `sat_prT`, `def1_pr` (for `q ≠ qT`), `def1_pr_all` (all `q`).
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo
open R002.Claude3Fold (HF St)

variable {S : Sig} {t : ℕ}

/-- The passage property at index parities `ηi`, `ηe` (the state's type only). -/
def QPar (q : QIdx) (τ : PType S) (ηi ηe : ℤ) : Prop := q.Q 0 ((τ, 0) : PState S) ηi ηe

theorem even_par_iff {i e ηi ηe a b : ℤ} (hi : i = 2 * a + ηi) (he : e = 2 * b + ηe) :
    Even (e - i + 1) ↔ Even (ηe - ηi + 1) := by
  rw [Int.even_iff, Int.even_iff]; omega

theorem q_par_iff (q : QIdx) (hq : q ≠ .qT) (hqL : q ≠ .qL) (y : PState S) {i e ηi ηe a b : ℤ}
    (hi : i = 2 * a + ηi) (he : e = 2 * b + ηe) : q.Q t y i e ↔ QPar q y.1 ηi ηe := by
  cases q with
  | q0 => simp [QIdx.Q, QPar]
  | qT => exact absurd rfl hq
  | qP c => simp only [QIdx.Q, QPar, even_par_iff hi he]
  | qE => simp only [QIdx.Q, QPar, even_par_iff hi he]
  | qL => exact absurd rfl hqL

theorem q_none_iff (q : QIdx) (hq : q ≠ .qT) (y : PState S) (ht : y.1.term = none)
    {i e ηi ηe a b : ℤ} (hi : i = 2 * a + ηi) (he : e = 2 * b + ηe) :
    q.Q t y i e ↔ QPar q y.1 ηi ηe := by
  by_cases hqL : q = .qL
  · subst hqL; simp [QIdx.Q, QPar, ht]
  · exact q_par_iff q hq hqL y hi he

/-- The exit index by cases. -/
theorem forall_exit_iff (hE : Embedded S t) (y : PState S) (P : ℤ → Prop) :
    (∀ e, ExitAt t y e → P e) ↔ (y.1.term = none → P (hiS t y)) ∧
      ∀ m', y.1.term = some m' → ∀ w' ηt, (ηt = 0 ∨ ηt = 1) → PinOK t y m' w' ηt →
        P (2 * (cornerY S y.1.k m' w').1.eval t + ηt - 2) := by
  constructor
  · intro H
    refine ⟨fun ht => H _ ⟨fun _ => rfl, fun m hm => by simp [ht] at hm⟩, ?_⟩
    intro m' ht w' ηt hηt hp
    refine H _ ((exitAt_some_iff ht _).2 ((atCorner_iff_pin hE y _ m').2 ⟨w', ηt, hηt, hp, ?_⟩))
    ring
  · rintro ⟨H₁, H₂⟩ e he
    cases ht : y.1.term with
    | none => rw [he.1 ht]; exact H₁ ht
    | some m' =>
      obtain ⟨w', ηt, hηt, hp, hj⟩ := (atCorner_iff_pin hE y _ m').1 ((exitAt_some_iff ht e).1 he)
      have := H₂ m' ht w' ηt hηt hp
      rwa [show 2 * (cornerY S y.1.k m' w').1.eval t + ηt - 2 = e by omega] at this

theorem hi_par (y : PState S) {b : Bool} (hg : ExitGuard y.1 b t y.2) :
    hiS t y = 2 * ((exitBnd y.1 b 0).1.σ * y.2 + (exitBnd y.1 b 0).1.c.eval t) +
      (exitBnd y.1 b 0).2 := by
  simpa using hiS_branch y b hg 0 (by norm_num)

/-- The property at a pinned terminal exit. -/
noncomputable def someHF (q : QIdx) (τ : PType S) (Xr : ClaudeChallenge2.Aff) (ηr : ℤ)
    (Xt : ClaudeChallenge2.Aff) (ηt : ℤ) : HF (PType S) 1 0 :=
  match q with
  | .qL => HF.tNonneg ⟨2 * Xt.a - 2 * Xr.a, 2 * Xt.b + ηt - 2 - 2 * Xr.b - ηr - 1⟩
  | q => ifHF (QPar q τ ηr ηt)

theorem sat_someHF (q : QIdx) (hq : q ≠ .qT) (y : PState S) (hr : y.1.root ≠ none)
    (ht : y.1.term ≠ none) (Xr Xt : ClaudeChallenge2.Aff) (ηr ηt : ℤ) :
    HF.Sat stLo stHi t (someHF q y.1 Xr ηr Xt ηt) ![y] Fin.elim0 ↔
      q.Q t y (2 * Xr.eval t + ηr) (2 * Xt.eval t + ηt - 2) := by
  have hi : 2 * Xr.eval t + ηr = 2 * Xr.eval t + ηr := rfl
  have he : 2 * Xt.eval t + ηt - 2 = 2 * (Xt.eval t - 1) + ηt := by ring
  cases q with
  | qL =>
    simp only [someHF, HF.Sat, R002.Claude3Fold.Aff.eval, QIdx.Q, ClaudeChallenge2.Aff.eval]
    constructor
    · intro h _ _; linarith
    · intro h; have := h hr ht; linarith
  | qT => exact absurd rfl hq
  | q0 => simp only [someHF, sat_ifHF]; exact (q_par_iff _ (by simp) (by simp) y hi he).symm
  | qP c => simp only [someHF, sat_ifHF]; exact (q_par_iff _ (by simp) (by simp) y hi he).symm
  | qE => simp only [someHF, sat_ifHF]; exact (q_par_iff _ (by simp) (by simp) y hi he).symm

/-- The exit part of a root passage formula. -/
noncomputable def exitF (q : QIdx) (τ : PType S) (Xr : ClaudeChallenge2.Aff) (ηr : ℤ) :
    HF (PType S) 1 0 :=
  match τ.term with
  | none => bigAnd ([false, true].map fun b =>
      HF.imp (guardHF τ b 0) (HF.imp (loLeHF τ ηr Xr 0) (HF.imp (leHiHF τ ηr Xr 0)
        (ifHF (QPar q τ ηr (exitBnd τ b 0).2)))))
  | some m' => bigAnd ((wordsLT S S.C).flatMap fun w' => ([0, 1] : List ℤ).map fun ηt =>
      HF.imp (pinHF τ m' w' ηt 0) (HF.imp (loLeHF τ ηr Xr 0)
        (HF.imp (HF.tNonneg ⟨2 * (cornerY S τ.k m' w').1.a - 2 * Xr.a,
            2 * (cornerY S τ.k m' w').1.b + ηt - 2 - 2 * Xr.b - ηr⟩)
          (HF.imp (leHiHF τ ηt (affAdd (cornerY S τ.k m' w').1 (-1)) 0)
            (someHF q τ Xr ηr (cornerY S τ.k m' w').1 ηt)))))

theorem sat_exitF (hE : Embedded S t) (q : QIdx) (hq : q ≠ .qT) (y : PState S)
    (hr : y.1.root ≠ none) (Xr : ClaudeChallenge2.Aff) {ηr : ℤ} (hηr : ηr = 0 ∨ ηr = 1) :
    HF.Sat stLo stHi t (exitF q y.1 Xr ηr) ![y] Fin.elim0 ↔
      ∀ e, ExitAt t y e → loS t y ≤ 2 * Xr.eval t + ηr → 2 * Xr.eval t + ηr ≤ e →
        e ≤ hiS t y → q.Q t y (2 * Xr.eval t + ηr) e := by
  rw [forall_exit_iff hE]
  unfold exitF
  cases ht : y.1.term with
  | none =>
    simp only [List.map_cons, List.map_nil, sat_bigAnd, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, HF.sat_imp, sat_guardHF,
      sat_loLeHF y hηr Xr 0 ![y] Fin.elim0 rfl, sat_leHiHF y hηr Xr 0 ![y] Fin.elim0 rfl,
      sat_ifHF, Matrix.cons_val_zero, reduceCtorEq, forall_const, and_true, le_refl,
      IsEmpty.forall_iff, implies_true]
    have key : ∀ b, ExitGuard y.1 b t y.2 →
        (QPar q y.1 ηr (exitBnd y.1 b 0).2 ↔ q.Q t y (2 * Xr.eval t + ηr) (hiS t y)) := fun b hg =>
      (q_none_iff q hq y ht rfl (hi_par y hg)).symm
    constructor
    · rintro ⟨H₁, H₂⟩ h₁ h₂
      obtain ⟨b, hg⟩ := exitGuard_exists y.1 t y.2
      rcases b with _ | _
      · exact (key false hg).1 (H₁ hg h₁ h₂)
      · exact (key true hg).1 (H₂ hg h₁ h₂)
    · intro H
      exact ⟨fun hg h₁ h₂ => (key false hg).2 (H h₁ h₂),
        fun hg h₁ h₂ => (key true hg).2 (H h₁ h₂)⟩
  | some m' =>
    simp only [sat_bigAnd, List.mem_flatMap, List.mem_map, mem_wordsLT, forall_exists_index,
      and_imp, reduceCtorEq, false_imp_iff, true_and, Option.some.injEq, forall_eq']
    constructor
    · intro H w' ηt hηt hp h₁ h₂ h₃
      have := H _ w' hp.1 ηt (by rcases hηt with rfl | rfl <;> simp) rfl
      rw [HF.sat_imp, HF.sat_imp, HF.sat_imp, HF.sat_imp,
        sat_pinHF y m' w' ηt 0 ![y] Fin.elim0 rfl hp.1,
        sat_loLeHF y hηr Xr 0 ![y] Fin.elim0 rfl, sat_leHiHF y hηt _ 0 ![y] Fin.elim0 rfl,
        sat_someHF q hq y hr (by simp [ht])] at this
      refine this hp h₁ ?_ ?_
      · simp only [HF.Sat, R002.Claude3Fold.Aff.eval, ClaudeChallenge2.Aff.eval] at h₂ ⊢
        linarith
      · simp only [affAdd_eval]; linarith
    · rintro H φ w' hw' ηt hηt rfl
      have hηt' : ηt = 0 ∨ ηt = 1 := by simpa using hηt
      rw [HF.sat_imp, HF.sat_imp, HF.sat_imp, HF.sat_imp,
        sat_pinHF y m' w' ηt 0 ![y] Fin.elim0 rfl hw',
        sat_loLeHF y hηr Xr 0 ![y] Fin.elim0 rfl, sat_leHiHF y hηt' _ 0 ![y] Fin.elim0 rfl,
        sat_someHF q hq y hr (by simp [ht])]
      intro hp h₁ h₂ h₃
      refine H w' ηt hηt' hp h₁ ?_ ?_
      · simp only [HF.Sat, R002.Claude3Fold.Aff.eval, ClaudeChallenge2.Aff.eval] at h₂ ⊢
        linarith
      · simp only [affAdd_eval] at h₃; linarith

/-- The root passage formula for a type. -/
noncomputable def prT (q : QIdx) (τ : PType S) : HF (PType S) 1 0 :=
  match τ.root with
  | none => hfTrue
  | some m => bigAnd ((wordsLT S S.C).flatMap fun w => ([0, 1] : List ℤ).map fun ηr =>
      HF.imp (pinHF τ m w ηr 0) (exitF q τ (cornerY S τ.k m w).1 ηr))

theorem sat_prT (hE : Embedded S t) (q : QIdx) (hq : q ≠ .qT) (y : PState S)
    (hy : RowsIn t y) : HF.Sat stLo stHi t (prT q y.1) ![y] Fin.elim0 ↔ PR q t y := by
  have hPR : PR q t y ↔ ∀ i e, RootAt t y i → ExitAt t y e → loS t y ≤ i → i ≤ e →
      e ≤ hiS t y → q.Q t y i e := by
    constructor
    · intro H i e hr he h₁ h₂ h₃; exact H i e hr ⟨hy, h₁, h₂, h₃, he⟩
    · intro H i e hr hp; exact H i e hr hp.2.2.2.2 hp.2.1 hp.2.2.1 hp.2.2.2.1
  rw [hPR]
  simp only [rootAt_iff_pin hE]
  unfold prT
  cases hr : y.1.root with
  | none => simp
  | some m =>
    simp only [sat_bigAnd, List.mem_flatMap, List.mem_map, mem_wordsLT, forall_exists_index,
      and_imp, Option.some.injEq]
    constructor
    · rintro H i e m' rfl w ηr hηr hp rfl he h₁ h₂ h₃
      have := H _ w hp.1 ηr (by rcases hηr with rfl | rfl <;> simp) rfl
      rw [HF.sat_imp, sat_pinHF y _ w ηr 0 ![y] Fin.elim0 rfl hp.1,
        sat_exitF hE q hq y (by simp [hr]) _ hηr] at this
      exact this hp e he h₁ h₂ h₃
    · rintro H φ w hw ηr hηr rfl
      have hηr' : ηr = 0 ∨ ηr = 1 := by simpa using hηr
      rw [HF.sat_imp, sat_pinHF y m w ηr 0 ![y] Fin.elim0 rfl hw,
        sat_exitF hE q hq y (by simp [hr]) _ hηr']
      intro hp e he h₁ h₂ h₃
      exact H _ e m rfl w ηr hηr' hp rfl he h₁ h₂ h₃

theorem def1_pr (q : QIdx) (hq : q ≠ .qT) : Def1 S (PR q) :=
  ⟨typeSplit1 (prT q), 0, fun t _ hV _ x hx => by
    rw [sat_typeSplit1, sat_prT (valid_embedded hV) q hq x ((mem_St_iff t x).1 hx)]⟩

/-- **All root passage atoms are definable.** -/
theorem def1_pr_all (q : QIdx) : Def1 S (PR q) := by
  by_cases hq : q = .qT
  · subst hq; exact def1_pr_qT (def1_pr .q0 (by simp))
  · exact def1_pr q hq

end ClaudeChallenge2.State
