import Formal.Claude3SentTrans

/-!
# Theorem 1a, G6: the transition as a formula (the atom `PT .q0`)

Written by a Claude worker (2026-10-20, Theorem 1a, parts G6/A).

* `typeSplit2`, `sat_typeSplit2` : a two-state formula by cases on the two types.
* `memConstHF`, `chainHF` : membership of a point with affine coordinates in charts (sentences).
* `transHF`, `sat_transHF` : under `Embedded` and `RowsIn t y`,
  `Sat transHF ![x, y] ↔ TransChar t x y` (so `↔ Trans t x y` by `trans_iff_char`).
* `def2_pt_q0 : Def2 S (PT .q0)`.
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo
open R002.Claude3Fold (HF)

variable {S : Sig} {t : ℕ}

/-! ## Generic pieces -/

/-- `A - B` as an affine function of the folding layer. -/
def fsub (A B : ClaudeChallenge2.Aff) : R002.Claude3Fold.Aff := ⟨A.a - B.a, A.b - B.b⟩

@[simp] theorem fsub_eval (A B : ClaudeChallenge2.Aff) (t : ℕ) :
    (fsub A B).eval t = A.eval t - B.eval t := by
  simp only [fsub, R002.Claude3Fold.Aff.eval, ClaudeChallenge2.Aff.eval]; ring

/-- Cases on the types of the two state variables. -/
noncomputable def typeSplit2 {k : ℕ} (F : PType S → PType S → HF (PType S) 2 k) :
    HF (PType S) 2 k :=
  bigOr ((allTypes S).flatMap fun τx => (allTypes S).map fun τy =>
    HF.and (HF.typ 0 τx) (HF.and (HF.typ 1 τy) (F τx τy)))

theorem sat_typeSplit2 {lo hi : PType S → R002.Claude3Fold.Aff} {k : ℕ}
    (F : PType S → PType S → HF (PType S) 2 k) (x y : PState S) (V : Fin k → Set (PState S)) :
    HF.Sat lo hi t (typeSplit2 F) ![x, y] V ↔ HF.Sat lo hi t (F x.1 y.1) ![x, y] V := by
  simp only [typeSplit2, sat_bigOr, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨φ, ⟨τx, -, τy, -, rfl⟩, h⟩
    simp only [HF.Sat, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    obtain ⟨rfl, rfl, h⟩ := h
    exact h
  · intro h
    exact ⟨_, ⟨x.1, mem_allTypes _, y.1, mem_allTypes _, rfl⟩, by simpa using h⟩

theorem sat_bigOr3 {α β γ : Type} {lo hi : PType S → R002.Claude3Fold.Aff} {m k : ℕ}
    (L₁ : List α) (L₂ : List β) (L₃ : List γ) (F : α → β → γ → HF (PType S) m k)
    (ν : Fin m → PState S) (V : Fin k → Set (PState S)) :
    HF.Sat lo hi t (bigOr (L₁.flatMap fun a => L₂.flatMap fun b => L₃.map fun c => F a b c)) ν V
      ↔ ∃ a ∈ L₁, ∃ b ∈ L₂, ∃ c ∈ L₃, HF.Sat lo hi t (F a b c) ν V := by
  simp only [sat_bigOr, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨φ, ⟨a, ha, b, hb, c, hc, rfl⟩, h⟩
    exact ⟨a, ha, b, hb, c, hc, h⟩
  · rintro ⟨a, ha, b, hb, c, hc, h⟩
    exact ⟨_, ⟨a, ha, b, hb, c, hc, rfl⟩, h⟩

theorem sat_ite_false {lo hi : PType S → R002.Claude3Fold.Aff} {m k : ℕ} (p : Prop) [Decidable p]
    (φ : HF (PType S) m k) (ν : Fin m → PState S) (V : Fin k → Set (PState S)) :
    HF.Sat lo hi t (if p then φ else hfFalse) ν V ↔ p ∧ HF.Sat lo hi t φ ν V := by
  by_cases hp : p
  · simp [hp]
  · simp only [hp, ↓reduceIte, false_and, iff_false]; exact sat_hfFalse

/-- A point with affine coordinates lies in a chart (a sentence). -/
def memConstHF {m k : ℕ} (c : Chart) (P : ClaudeChallenge2.Aff × ClaudeChallenge2.Aff) :
    HF (PType S) m k :=
  bigAnd [HF.tNonneg (fsub P.1 c.lx), HF.tNonneg (fsub c.ux P.1), HF.tNonneg (fsub P.2 c.ly),
    HF.tNonneg (fsub c.uy P.2), HF.tNonneg (fsub (addAff P.1 P.2) c.ls),
    HF.tNonneg (fsub c.us (addAff P.1 P.2))]

theorem sat_memConstHF {lo hi : PType S → R002.Claude3Fold.Aff} {m k : ℕ} (c : Chart)
    (P : ClaudeChallenge2.Aff × ClaudeChallenge2.Aff) (ν : Fin m → PState S)
    (V : Fin k → Set (PState S)) :
    HF.Sat lo hi t (memConstHF c P) ν V ↔ c.Mem t (P.1.eval t, P.2.eval t) := by
  simp only [memConstHF, sat_bigAnd, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, HF.Sat, fsub_eval, addAff_eval, Chart.Mem]
  constructor <;> intro h <;> omega

/-- All charts of a list contain the point. -/
def chainHF {m k : ℕ} (L : List Chart) (P : ClaudeChallenge2.Aff × ClaudeChallenge2.Aff) :
    HF (PType S) m k :=
  bigAnd (L.map fun c => memConstHF c P)

theorem sat_chainHF {lo hi : PType S → R002.Claude3Fold.Aff} {m k : ℕ} (L : List Chart)
    (P : ClaudeChallenge2.Aff × ClaudeChallenge2.Aff) (ν : Fin m → PState S)
    (V : Fin k → Set (PState S)) :
    HF.Sat lo hi t (chainHF L P) ν V ↔ ∀ c ∈ L, c.Mem t (P.1.eval t, P.2.eval t) := by
  simp only [chainHF, sat_bigAnd, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, sat_memConstHF]

/-! ## The transition -/

/-- The exit branch guard on variable `v`. -/
def guardHF {m k : ℕ} (τ : PType S) (b : Bool) (v : Fin m) : HF (PType S) m k :=
  if b then HF.nle v (fsub (rc τ).ux (rc τ).us)
  else HF.le v ⟨(rc τ).us.a - (rc τ).ux.a, (rc τ).us.b - (rc τ).ux.b - 1⟩

theorem sat_guardHF {lo hi : PType S → R002.Claude3Fold.Aff} {m k : ℕ} (τ : PType S) (b : Bool)
    (v : Fin m) (ν : Fin m → PState S) (V : Fin k → Set (PState S)) :
    HF.Sat lo hi t (guardHF τ b v) ν V ↔ ExitGuard τ b t (ν v).2 := by
  rcases b with _ | _ <;>
    simp only [guardHF, ExitGuard, Bool.false_eq_true, ↓reduceIte, HF.Sat, fsub,
      R002.Claude3Fold.Aff.eval, ClaudeChallenge2.Aff.eval] <;>
    constructor <;> intro h <;> linarith

/-- The terminal part (variable `1` is `y`, variable `0` is `x`). -/
noncomputable def termHF (τy : PType S) (m : Fin S.M) (η : ℤ) (R : RowSet S) :
    HF (PType S) 2 0 :=
  bigOr ((wordsLT S S.C).flatMap fun w' => [()].flatMap fun _ => ([0, 1] : List ℤ).map fun ηc =>
    if WordOK S w' (S.mchart m) τy.f then
      bigAnd [chainHF (wordCharts S w' (S.mchart m)) (S.mx m, S.my m),
        HF.le 1 ⟨(cornerY S τy.k m w').2.a, (cornerY S τy.k m w').2.b - ηc⟩,
        HF.nle 1 ⟨-(cornerY S τy.k m w').2.a, -(cornerY S τy.k m w').2.b + ηc⟩,
        HF.tNonneg (fsub (rc τy).ux (cornerY S τy.k m w').1),
        HF.le 1 ⟨(rc τy).us.a - (cornerY S τy.k m w').1.a,
          (rc τy).us.b - ηc - (cornerY S τy.k m w').1.b⟩,
        meetHF (yRow τy η [⟨0, affAdd (cornerY S τy.k m w').1 ((ηc - η - 2) / 2)⟩]) R 1 0]
    else hfFalse)

/-- The part on the row of `y`. -/
noncomputable def ypartHF (τy : PType S) (η : ℤ) (R : RowSet S) : HF (PType S) 2 0 :=
  match τy.term with
  | none => meetHF (yRow τy η (upsY τy η)) R 1 0
  | some m => termHF τy m η R

/-- The transition formula for fixed types. -/
noncomputable def transT (τx τy : PType S) : HF (PType S) 2 0 :=
  if τx.term = none ∧ τy.root = none then
    bigOr ([false, true].flatMap fun b => (wordsLT S S.C).flatMap fun w =>
      ([0, 1] : List ℤ).map fun η =>
      if WordOK S w τx.f τy.f then
        bigAnd [guardHF τx b 0,
          meetHF (entRow τx τy b w (rotN τy.k (dS η 1))) (exitRow τx b 2) 0 0,
          HF.neg (meetHF (entRow τx τy b w (rotN τy.k (dS η 2))) (exitRow τx b 0) 0 0),
          ypartHF τy η (entRow τx τy b w 0)]
      else hfFalse)
  else hfFalse

/-- **The transition formula.** -/
noncomputable def transHF : HF (PType S) 2 0 := typeSplit2 transT

/-! ## Semantics -/

theorem yRow_wf (τ : PType S) (η : ℤ) {ups : List Bnd} (hu : ∀ b ∈ ups, b.WF) :
    (yRow τ η ups).WF :=
  rowPtRow_wf _ _ _ (lowsY_wf τ η) hu

theorem entRow_wf (τx τy : PType S) (b : Bool) (w : List (Letter S)) (d : ℤ × ℤ) :
    (entRow τx τy b w d).WF :=
  nbrRow_wf (exitRow_wf τx b 1) _ _ _

theorem hi_corner_iff (y : PState S) {ηc : ℤ} (hηc : ηc = 0 ∨ ηc = 1) (Xc : ℤ) :
    2 * Xc + ηc - 2 ≤ hiS t y ↔
      0 ≤ (rc y.1).ux.eval t - Xc ∧ y.2 ≤ (rc y.1).us.eval t - ηc - Xc := by
  have := le_hi_iff (t := t) y hηc (Xc - 1)
  simp only [upsY, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    zero_mul, zero_add, affAdd_eval, neg_mul, one_mul] at this
  rw [show 2 * Xc + ηc - 2 = 2 * (Xc - 1) + ηc by ring, this]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem sat_meetHF_y0 (hE : Embedded S t) {R : RowSet S} (hR : R.WF) (τ : PType S) (η : ℤ)
    (c : ClaudeChallenge2.Aff) {m k : ℕ} (a b : Fin m) {lo hi : PType S → R002.Claude3Fold.Aff}
    (ν : Fin m → PState S) (V : Fin k → Set (PState S)) :
    HF.Sat lo hi t (meetHF (yRow τ η [⟨0, c⟩]) R a b) ν V ↔
      Meet S t (yRow τ η [⟨0, c⟩]) (ν a).2 R (ν b).2 :=
  sat_meetHF hE (yRow_wf _ _ (by simp [Bnd.WF])) hR a b ν V

theorem sat_termHF (hE : Embedded S t) (x y : PState S) (m : Fin S.M) {η : ℤ}
    {R : RowSet S} (hR : R.WF) (V : Fin 0 → Set (PState S)) :
    HF.Sat stLo stHi t (termHF y.1 m η R) ![x, y] V ↔ TermPart t y m η R x.2 := by
  rw [termHF, sat_bigOr3]
  simp only [mem_wordsLT, List.mem_cons, List.not_mem_nil, or_false, sat_ite_false, sat_bigAnd,
    forall_eq_or_imp, forall_eq, sat_chainHF, HF.Sat, Matrix.cons_val_one, Matrix.cons_val_zero,
    sat_meetHF_y0 hE hR, R002.Claude3Fold.Aff.eval]
  unfold TermPart
  constructor
  · rintro ⟨w', hw', -, -, ηc, hηc, hok, hch, h1, h2, h3, h4, hM⟩
    refine ⟨w', hw', hok, hch, ηc, hηc, ?_, (hi_corner_iff y hηc _).2 ⟨?_, ?_⟩, hM⟩ <;>
      simp only [fsub, ClaudeChallenge2.Aff.eval] at h1 h2 h3 h4 ⊢ <;> linarith
  · rintro ⟨w', hw', hok, hch, ηc, hηc, hh, hhi, hM⟩
    obtain ⟨h3, h4⟩ := (hi_corner_iff y hηc _).1 hhi
    refine ⟨w', hw', (), trivial, ηc, hηc, hok, hch, ?_, ?_, ?_, ?_, hM⟩ <;>
      simp only [fsub, ClaudeChallenge2.Aff.eval] at hh h3 h4 ⊢ <;> linarith

theorem sat_ypartHF (hE : Embedded S t) (x y : PState S) (η : ℤ) {R : RowSet S} (hR : R.WF)
    (V : Fin 0 → Set (PState S)) :
    HF.Sat stLo stHi t (ypartHF y.1 η R) ![x, y] V ↔ YPart t y η R x.2 := by
  unfold ypartHF YPart
  cases h : y.1.term with
  | none =>
    simp only [sat_meetHF hE (yRow_wf _ _ (upsY_wf _ _)) hR, Matrix.cons_val_one,
      Matrix.cons_val_zero, true_and, reduceCtorEq, false_and, exists_false, or_false]
  | some m =>
    simp only [sat_termHF hE x y m hR, reduceCtorEq, false_and, Option.some.injEq, false_or,
      exists_eq_left']

theorem sat_transT (hE : Embedded S t) (x y : PState S) (V : Fin 0 → Set (PState S)) :
    HF.Sat stLo stHi t (transT x.1 y.1) ![x, y] V ↔ TransChar t x y := by
  unfold transT TransChar
  by_cases hc : x.1.term = none ∧ y.1.root = none
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), sat_bigOr3]
    simp only [List.mem_cons, List.not_mem_nil, or_false, mem_wordsLT, sat_ite_false,
      sat_bigAnd, forall_eq_or_imp, forall_eq, sat_guardHF, HF.Sat,
      sat_meetHF hE (entRow_wf _ _ _ _ _) (exitRow_wf _ _ _),
      sat_ypartHF hE x y _ (entRow_wf _ _ _ _ _),
      Matrix.cons_val_zero, hc, true_and]
    constructor
    · rintro ⟨b, -, w, hw, η, hη, hok, hg, hM, hN, hY⟩
      exact ⟨b, hg, w, hw, hok, η, hη, hM, hN, hY⟩
    · rintro ⟨b, hg, w, hw, hok, η, hη, hM, hN, hY⟩
      exact ⟨b, by cases b <;> simp, w, hw, η, hη, hok, hg, hM, hN, hY⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    simp only [sat_hfFalse, false_iff]
    rintro ⟨h1, h2, -⟩
    exact hc ⟨h1, h2⟩

theorem sat_transHF (hE : Embedded S t) (x y : PState S) (V : Fin 0 → Set (PState S)) :
    HF.Sat stLo stHi t transHF ![x, y] V ↔ TransChar t x y := by
  rw [transHF, sat_typeSplit2, sat_transT hE]

/-- **The atom `PT .q0` (no transition) is definable.** -/
theorem def2_pt_q0 : Def2 S (PT .q0) := by
  refine ⟨HF.neg transHF, 0, fun t _ hV _ x _ y hy => ?_⟩
  have hE := valid_embedded hV
  rw [HF.Sat, sat_transHF hE, ← trans_iff_char hE ((mem_St_iff t y).1 hy), trans_iff, not_not]

end ClaudeChallenge2.State
