import Formal.Claude3SentRoot

/-!
# Theorem 1a, G6: the parity atoms `PT (qP b)`, `PT qE`

Written by a Claude worker (2026-10-20, Theorem 1a, parts G6/A).

The parity clauses along a transition depend on the entry index only through its parity, which
is the parity `η` of the decoupled transition (`TransCharE`). So `PT q x y` is
`∀ η, (transition with entry parity η) → G q η y` with a one-state `G`.

* `transAtE_iff` : `(∃ i X, TransAt t x y i ∧ i = 2 X + η) ↔ TransCharE t x y η`;
* `transEHF`, `sat_transEHF`; `gT`, `sat_gT`;
* `def2_pt_par` : `Def2 S (PT q)` for `q = qP b` and `q = qE`.
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo
open R002.Claude3Fold (HF St)

variable {S : Sig} {t : ℕ}

/-- The decoupled transition with entry parity `η`. -/
def TransCharE (t : ℕ) (x y : PState S) (η : ℤ) : Prop :=
  x.1.term = none ∧ y.1.root = none ∧ ∃ b, ExitGuard x.1 b t x.2 ∧
    ∃ w : List (Letter S), w.length < S.C ∧ WordOK S w x.1.f y.1.f ∧
      Meet S t (entRow x.1 y.1 b w (rotN y.1.k (dS η 1))) x.2 (exitRow x.1 b 2) x.2 ∧
      ¬ Meet S t (entRow x.1 y.1 b w (rotN y.1.k (dS η 2))) x.2 (exitRow x.1 b 0) x.2 ∧
      YPart t y η (entRow x.1 y.1 b w 0) x.2

theorem transAtE_iff (hE : Embedded S t) {x y : PState S} (hy : RowsIn t y) {η : ℤ}
    (hη : η = 0 ∨ η = 1) :
    (∃ i X, TransAt t x y i ∧ i = 2 * X + η) ↔ TransCharE t x y η := by
  constructor
  · rintro ⟨i, X, ⟨hxt, hyr, ⟨e, hP⟩, ⟨v₁, ⟨hz₁y, rfl⟩, ⟨hz₁x, hq₁⟩⟩,
      ⟨v₂, ⟨hz₂y, rfl⟩, ⟨hz₂x, hq₂⟩⟩, hN⟩, rfl⟩
    obtain ⟨b, hg⟩ := exitGuard_exists x.1 t x.2
    obtain ⟨w, hw, hok, hch, hwe⟩ := (ident_iff_word hE x.1.f y.1.f _ _).1 ⟨hz₁x, hz₁y, hq₁⟩
    refine ⟨hxt, hyr, b, hg, w, hw, hok, ?_, ?_, ?_⟩
    · refine ⟨_, _, (entRow_at x y.1 b hg w _ _).2 ⟨hch, ?_⟩, (exitRow_at2 x b hg _).2 rfl,
        hz₂y, hz₂x, hq₂.symm⟩
      rw [rp_shift y X η 1 hη, hwe]
    · rintro ⟨z₁, z₂, h₁, h₂, hz₁, hz₂, he⟩
      rw [entRow_at x y.1 b hg] at h₁
      rw [exitRow_at0 x b hg] at h₂
      obtain ⟨-, h₁⟩ := h₁
      rw [← hwe, ← rp_shift y X η 2 hη] at h₁
      subst h₁ h₂
      exact hN _ _ ⟨hz₁, rfl⟩ ⟨hz₂, rfl⟩ he
    · obtain ⟨-, hlo, hie, hehi, hex⟩ := hP
      cases ht : y.1.term with
      | none =>
        refine Or.inl ⟨ht, _, _, (rowPtRow_at _ _ hη _ _ _ _).2 ⟨X, ⟨(lo_le_iff y hη X).1 hlo,
          (le_hi_iff y hη X).1 ?_⟩, rfl⟩, (entRow_at x y.1 b hg w 0 _).2 ⟨hch, ?_⟩, hz₁y, hz₁y,
          rfl⟩
        · rw [← hex.1 ht]; exact hie
        · rw [add_zero]; exact hwe
      | some m =>
        obtain ⟨w', hw', hok', hch', hce⟩ := (atCorner_iff_word hE y (e + 2) m).1 (hex.2 m ht)
        obtain ⟨ηc, hηc, hj, hh⟩ := (rp_eq_corner_iff y m w' (e + 2)).1 hce
        refine Or.inr ⟨m, ht, w', hw', hok', hch', ηc, hηc, hh, by omega, _, _,
          (rowPtRow_at _ _ hη _ _ _ _).2 ⟨X, ⟨(lo_le_iff y hη X).1 hlo, ?_⟩, rfl⟩,
          (entRow_at x y.1 b hg w 0 _).2 ⟨hch, ?_⟩, hz₁y, hz₁y, rfl⟩
        · simp only [List.mem_singleton, forall_eq, zero_mul, zero_add, affAdd_eval]
          omega
        · rw [add_zero]; exact hwe
  · rintro ⟨hxt, hyr, b, hg, w, hw, hok, hM₂, hN₃, hYP⟩
    -- the entry position and the passage
    obtain ⟨X, e, hrp, hch, hzy, hP⟩ : ∃ X e : ℤ,
        rp y (2 * X + η) = (wordAff S w).apply t (rp x (hiS t x + 1)) ∧
        (∀ ch ∈ wordCharts S w x.1.f, ch.Mem t (rp x (hiS t x + 1))) ∧
        (S.chart y.1.f).Mem t (rp y (2 * X + η)) ∧ PassOK t y (2 * X + η) e := by
      rcases hYP with ⟨ht, hM⟩ | ⟨m, ht, w', hw', hok', hch', ηc, hηc, hh, hehi, hM⟩
      · obtain ⟨X, ⟨hlo, hup⟩, hrp, hch, hzy⟩ := meet_entry hE hg hη hM
        exact ⟨X, hiS t y, hrp, hch, hzy, hy, (lo_le_iff y hη X).2 hlo,
          (le_hi_iff y hη X).2 hup, le_refl _, ⟨fun _ => rfl, fun m hm => by simp [ht] at hm⟩⟩
      · obtain ⟨X, ⟨hlo, hup⟩, hrp, hch, hzy⟩ := meet_entry hE hg hη hM
        simp only [List.mem_singleton, forall_eq, zero_mul, zero_add, affAdd_eval] at hup
        refine ⟨X, 2 * (cornerY S y.1.k m w').1.eval t + ηc - 2, hrp, hch, hzy, hy,
          (lo_le_iff y hη X).2 hlo, by omega, hehi, ⟨fun h => by simp [ht] at h, ?_⟩⟩
        intro m' hm'
        rw [ht, Option.some.injEq] at hm'
        subst hm'
        refine (atCorner_iff_word hE y _ m).2 ⟨w', hw', hok', hch', ?_⟩
        exact (rp_eq_corner_iff y m w' _).2 ⟨ηc, hηc, by ring, hh⟩
    obtain ⟨hzq, hzy', hq⟩ := (ident_iff_word hE x.1.f y.1.f _ _).2 ⟨w, hw, hok, hch, hrp⟩
    refine ⟨2 * X + η, X, ⟨hxt, hyr, ⟨e, hP⟩, ⟨_, ⟨hzy', rfl⟩, ⟨hzq, hq⟩⟩, ?_, ?_⟩, rfl⟩
    · obtain ⟨z₁, z₂, h₁, h₂, hz₁, hz₂, he⟩ := hM₂
      rw [entRow_at x y.1 b hg] at h₁
      rw [exitRow_at2 x b hg] at h₂
      obtain ⟨-, h₁⟩ := h₁
      rw [← hrp, ← rp_shift y X η 1 hη] at h₁
      subst h₁ h₂
      exact ⟨_, ⟨hz₁, rfl⟩, ⟨hz₂, he.symm⟩⟩
    · rintro v v' ⟨hz₁, rfl⟩ ⟨hz₂, rfl⟩ he
      refine hN₃ ⟨_, _, (entRow_at x y.1 b hg w _ _).2 ⟨hch, ?_⟩, (exitRow_at0 x b hg _).2 rfl,
        hz₁, hz₂, he⟩
      rw [rp_shift y X η 2 hη, hrp]

/-- The transition formula with entry parity `η`, for fixed types. -/
noncomputable def transTE (η : ℤ) (τx τy : PType S) : HF (PType S) 2 0 :=
  if τx.term = none ∧ τy.root = none then
    bigOr ([false, true].flatMap fun b => (wordsLT S S.C).flatMap fun w => [()].map fun _ =>
      if WordOK S w τx.f τy.f then
        bigAnd [guardHF τx b 0,
          meetHF (entRow τx τy b w (rotN τy.k (dS η 1))) (exitRow τx b 2) 0 0,
          HF.neg (meetHF (entRow τx τy b w (rotN τy.k (dS η 2))) (exitRow τx b 0) 0 0),
          ypartHF τy η (entRow τx τy b w 0)]
      else hfFalse)
  else hfFalse

theorem sat_transTE (hE : Embedded S t) (x y : PState S) {η : ℤ} (V : Fin 0 → Set (PState S)) :
    HF.Sat stLo stHi t (typeSplit2 (transTE η)) ![x, y] V ↔ TransCharE t x y η := by
  rw [sat_typeSplit2]
  unfold transTE TransCharE
  by_cases hc : x.1.term = none ∧ y.1.root = none
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), sat_bigOr3]
    simp only [List.mem_cons, List.not_mem_nil, or_false, mem_wordsLT, sat_ite_false,
      sat_bigAnd, forall_eq_or_imp, forall_eq, sat_guardHF, HF.Sat,
      sat_meetHF hE (entRow_wf _ _ _ _ _) (exitRow_wf _ _ _),
      sat_ypartHF hE x y _ (entRow_wf _ _ _ _ _),
      Matrix.cons_val_zero, hc, true_and]
    constructor
    · rintro ⟨b, -, w, hw, -, hok, hg, hM, hN, hY⟩
      exact ⟨b, hg, w, hw, hok, hM, hN, hY⟩
    · rintro ⟨b, hg, w, hw, hok, hM, hN, hY⟩
      exact ⟨b, by cases b <;> simp, w, hw, (), hok, hg, hM, hN, hY⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    simp only [sat_hfFalse, false_iff]
    rintro ⟨h1, h2, -⟩
    exact hc ⟨h1, h2⟩

/-- The exit clause with entry parity `η`. -/
def GP (q : QIdx) (η : ℤ) (t : ℕ) (y : PState S) : Prop := ∀ e, ExitAt t y e → q.Q t y η e

/-- Its formula for a type. -/
noncomputable def gT (q : QIdx) (η : ℤ) (τ : PType S) : HF (PType S) 1 0 :=
  match τ.term with
  | none => bigAnd ([false, true].map fun b =>
      HF.imp (guardHF τ b 0) (ifHF (QPar q τ η (exitBnd τ b 0).2)))
  | some m => bigAnd ((wordsLT S S.C).flatMap fun w => ([0, 1] : List ℤ).map fun ηt =>
      HF.imp (pinHF τ m w ηt 0) (ifHF (QPar q τ η ηt)))

theorem sat_gT (hE : Embedded S t) (q : QIdx) (hq : q ≠ .qT) (hqL : q ≠ .qL) {η : ℤ}
    (y : PState S) : HF.Sat stLo stHi t (gT q η y.1) ![y] Fin.elim0 ↔ GP q η t y := by
  unfold GP
  rw [forall_exit_iff hE]
  unfold gT
  have hi0 : η = 2 * 0 + η := by ring
  cases ht : y.1.term with
  | none =>
    simp only [List.map_cons, List.map_nil, sat_bigAnd, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, HF.sat_imp, sat_guardHF, sat_ifHF,
      Matrix.cons_val_zero, reduceCtorEq, IsEmpty.forall_iff, implies_true, and_true,
      forall_const]
    have key : ∀ b, ExitGuard y.1 b t y.2 →
        (QPar q y.1 η (exitBnd y.1 b 0).2 ↔ q.Q t y η (hiS t y)) := fun b hg =>
      (q_par_iff q hq hqL y hi0 (hi_par y hg)).symm
    constructor
    · rintro ⟨H₁, H₂⟩
      obtain ⟨b, hg⟩ := exitGuard_exists y.1 t y.2
      rcases b with _ | _
      · exact (key false hg).1 (H₁ hg)
      · exact (key true hg).1 (H₂ hg)
    · intro H
      exact ⟨fun hg => (key false hg).2 H, fun hg => (key true hg).2 H⟩
  | some m' =>
    simp only [sat_bigAnd, List.mem_flatMap, List.mem_map, mem_wordsLT, forall_exists_index,
      and_imp, reduceCtorEq, IsEmpty.forall_iff, true_and, Option.some.injEq, forall_eq']
    have he : ∀ (w' : List (Letter S)) (ηt : ℤ), 2 * (cornerY S y.1.k m' w').1.eval t + ηt - 2 =
        2 * ((cornerY S y.1.k m' w').1.eval t - 1) + ηt := fun _ _ => by ring
    constructor
    · intro H w' ηt hηt hp
      have := H _ w' hp.1 ηt (by rcases hηt with rfl | rfl <;> simp) rfl
      rw [HF.sat_imp, sat_pinHF y m' w' ηt 0 ![y] Fin.elim0 rfl hp.1, sat_ifHF] at this
      exact (q_par_iff q hq hqL y hi0 (he w' ηt)).2 (this hp)
    · rintro H φ w' hw' ηt hηt rfl
      have hηt' : ηt = 0 ∨ ηt = 1 := by simpa using hηt
      rw [HF.sat_imp, sat_pinHF y m' w' ηt 0 ![y] Fin.elim0 rfl hw', sat_ifHF]
      intro hp
      exact (q_par_iff q hq hqL y hi0 (he w' ηt)).1 (H w' ηt hηt' hp)

theorem pt_par_iff (hV : Valid S t) (q : QIdx) (hq : q ≠ .qT) (hqL : q ≠ .qL)
    (x y : PState S) :
    PT q t x y ↔ ∀ η : ℤ, (η = 0 ∨ η = 1) → (∃ i X, TransAt t x y i ∧ i = 2 * X + η) →
      GP q η t y := by
  have par : ∀ {i η e : ℤ} (X : ℤ), i = 2 * X + η → (q.Q t y i e ↔ q.Q t y η e) := by
    intro i η e X hi
    have he : e = 2 * (e / 2) + e % 2 := by omega
    rw [q_par_iff q hq hqL y hi he, q_par_iff q hq hqL y (show η = 2 * 0 + η by ring) he]
  constructor
  · rintro H η - ⟨i, X, hT, hi⟩ e he
    obtain ⟨e', hp⟩ := hT.2.2.1
    rw [ExitAt.unique hV he hp.2.2.2.2]
    exact (par X hi).1 (H i e' hT hp)
  · intro H i e hT hp
    exact (par (i / 2) (by omega)).2
      (H (i % 2) (by omega) ⟨i, i / 2, hT, by omega⟩ e hp.2.2.2.2)

/-- **The parity atoms along transitions are definable.** -/
theorem def2_pt_par (q : QIdx) (hq : q ≠ .qT) (hqL : q ≠ .qL) : Def2 S (PT q) := by
  refine ⟨bigAnd (([0, 1] : List ℤ).map fun η =>
    HF.imp (typeSplit2 (transTE η)) (at1 (typeSplit1 (gT q η)) 1)), 0,
    fun t _ hV _ x _ y hy => ?_⟩
  have hE := valid_embedded hV
  have hy' := (mem_St_iff t y).1 hy
  rw [pt_par_iff hV q hq hqL, sat_bigAnd, List.forall_mem_map]
  have hmem : ∀ η : ℤ, η ∈ ([0, 1] : List ℤ) ↔ (η = 0 ∨ η = 1) := by simp
  constructor
  · intro H η hη hT
    have := H η ((hmem η).2 hη)
    rw [HF.sat_imp, sat_transTE hE, sat_at1] at this
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
    rw [sat_typeSplit1, sat_gT hE q hq hqL] at this
    exact this ((transAtE_iff hE hy' hη).1 hT)
  · intro H η hη
    have hη' := (hmem η).1 hη
    rw [HF.sat_imp, sat_transTE hE, sat_at1]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [sat_typeSplit1, sat_gT hE q hq hqL]
    intro hT
    exact H η hη' ((transAtE_iff hE hy' hη').2 hT)

end ClaudeChallenge2.State
