import Formal.Claude3SentDbP

/-!
# Theorem 1a, G6: condition 3 (b) as a formula (the atom `DbR`)

Written by a Claude worker (2026-10-20, Theorem 1a, parts G6/A).

For every witness `(b, w, η)` of a transition and every choice of data, the formula says that
the output of `y` (as a row in the non-parallel case, through an auxiliary state in the parallel
case) does not meet the full tail of `x`. `def2_DbR : Def2 S DbR`.
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo
open R002.Claude3Fold (HF St)

variable {S : Sig} {t : ℕ}

/-- `a h_u + c h_v ≤ F(t)` (coefficients in `{-1, 0, 1}`). -/
def linHF {n : ℕ} (a : ℤ) (u : Fin n) (c : ℤ) (v : Fin n) (F : ClaudeChallenge2.Aff) :
    HF (PType S) n 0 := PA.toHF u v ⟨a, c, F⟩

theorem sat_linHF {n : ℕ} {a c : ℤ} (ha : Sgn a) (hc : Sgn c) (u v : Fin n)
    (F : ClaudeChallenge2.Aff) (ν : Fin n → PState S) :
    HF.Sat stLo stHi t (linHF a u c v F) ν Fin.elim0 ↔ a * (ν u).2 + c * (ν v).2 ≤ F.eval t :=
  PA.sat_toHF (c := ⟨a, c, F⟩) ⟨ha, hc⟩ u v ν Fin.elim0

theorem sgn_of_wf {b : Bnd} (hb : b.WF) : Sgn (-b.σ) := by
  rcases hb with h | h <;> rw [h] <;> simp [Sgn]

/-- The affine function `A + c` with integer `c` and sign `s` (`s A + c`). -/
def lc (s : ℤ) (A : ClaudeChallenge2.Aff) (c : ℤ) : ClaudeChallenge2.Aff := ⟨s * A.a, s * A.b + c⟩

@[simp] theorem lc_eval (s : ℤ) (A : ClaudeChallenge2.Aff) (c : ℤ) (t : ℕ) :
    (lc s A c).eval t = s * A.eval t + c := by
  simp only [lc, ClaudeChallenge2.Aff.eval]; ring

/-- `A - B + c`. -/
def subA (A B : ClaudeChallenge2.Aff) (c : ℤ) : ClaudeChallenge2.Aff :=
  ⟨A.a - B.a, A.b - B.b + c⟩

@[simp] theorem subA_eval (A B : ClaudeChallenge2.Aff) (c : ℤ) (t : ℕ) :
    (subA A B c).eval t = A.eval t - B.eval t + c := by
  simp only [subA, ClaudeChallenge2.Aff.eval]; ring

@[simp] theorem cons3_one {α : Type} (s x y : α) : (Fin.cons s ![x, y] : Fin 3 → α) 1 = x := rfl
@[simp] theorem cons3_two {α : Type} (s x y : α) : (Fin.cons s ![x, y] : Fin 3 → α) 2 = y := rfl

theorem entV_sgn (τx τy : PType S) (b : Bool) (w : List (Letter S)) :
    Sgn (entV τx τy b w).1 ∧ Sgn (entV τx τy b w).2 := by
  have hm := entV_mem τx τy b w
  generalize entV τx τy b w = v at *
  rw [mem_unitVec_iff] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Sgn]

theorem entV_par (τx τy : PType S) (b : Bool) (w : List (Letter S))
    (h : (entV τx τy b w).2 = 0) : (entV τx τy b w).1 = 1 ∨ (entV τx τy b w).1 = -1 := by
  have hm := entV_mem τx τy b w
  generalize entV τx τy b w = v at *
  rw [mem_unitVec_iff] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-! ## The witness and the height link -/

/-- The transition witness as a formula. -/
noncomputable def twHF (τx τy : PType S) (b : Bool) (w : List (Letter S)) (η : ℤ) :
    HF (PType S) 2 0 :=
  if τx.term = none ∧ τy.root = none ∧ WordOK S w τx.f τy.f then
    bigAnd [guardHF τx b 0,
      meetHF (entRow τx τy b w (rotN τy.k (dS η 1))) (exitRow τx b 2) 0 0,
      HF.neg (meetHF (entRow τx τy b w (rotN τy.k (dS η 2))) (exitRow τx b 0) 0 0),
      ypartHF τy η (entRow τx τy b w 0)]
  else hfFalse

theorem sat_twHF (hE : Embedded S t) (x y : PState S) (b : Bool) {w : List (Letter S)}
    (hw : w.length < S.C) (η : ℤ) :
    HF.Sat stLo stHi t (twHF x.1 y.1 b w η) ![x, y] Fin.elim0 ↔ TW t x y b w η := by
  unfold twHF TW
  by_cases hc : x.1.term = none ∧ y.1.root = none ∧ WordOK S w x.1.f y.1.f
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    simp only [sat_bigAnd, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, sat_guardHF, HF.Sat, sat_meetHF hE (entRow_wf _ _ _ _ _) (exitRow_wf _ _ _),
      sat_ypartHF hE x y _ (entRow_wf _ _ _ _ _), Matrix.cons_val_zero, hc, hw, true_and]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    simp only [sat_hfFalse, false_iff]
    rintro ⟨h1, h2, -, -, h3, -⟩
    exact hc ⟨h1, h2, h3⟩

/-- `h_y + η = entV.2 h_x + entG.2(t)`. -/
def hhHF (τx τy : PType S) (b : Bool) (w : List (Letter S)) (η : ℤ) : HF (PType S) 2 0 :=
  HF.and (linHF 1 1 (-(entV τx τy b w).2) 0 (affAdd (entG τx τy b w).2 (-η)))
    (linHF (-1) 1 (entV τx τy b w).2 0 (lc (-1) (entG τx τy b w).2 η))

theorem sat_hhHF (x y : PState S) (b : Bool) (w : List (Letter S)) (η : ℤ) :
    HF.Sat stLo stHi t (hhHF x.1 y.1 b w η) ![x, y] Fin.elim0 ↔
      y.2 + η = (entV x.1 y.1 b w).2 * x.2 + (entG x.1 y.1 b w).2.eval t := by
  have hs := (entV_sgn x.1 y.1 b w).2
  have hs' : Sgn (-(entV x.1 y.1 b w).2) := by rcases hs with h | h | h <;> simp [Sgn, h]
  rw [hhHF, HF.Sat, sat_linHF (by simp [Sgn]) hs', sat_linHF (by simp [Sgn]) hs]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, affAdd_eval, lc_eval]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; constructor <;> linarith

/-! ## The parallel case -/

/-- `PCond` at the position `h_z + δ - H` (variables `z = 0`, `x = 1`, `y = 2`). -/
def pcondHF (τx τy : PType S) (b : Bool) (w : List (Letter S)) (η η' : ℤ) (ed' : ED S)
    (δ : ℤ) : HF (PType S) 3 0 :=
  bigAnd (linHF (entV τx τy b w).1 1 (-1) 0
      (lc (-1) (addAff (pH τx τy b w η η') (entG τx τy b w).1) (δ - (η - η' + 3) / 2)) ::
    (edUps τy η' ed').map fun b' =>
      linHF 1 0 (-b'.σ) 2 (lc 1 (addAff b'.c (pH τx τy b w η η')) (-δ)))

theorem edUps_wf (τ : PType S) (η : ℤ) (ed : ED S) : ∀ b ∈ edUps τ η ed, b.WF := by
  cases ed with
  | hi => simpa [edUps, Bnd.WF] using upsY_wf τ η
  | pin => simp [edUps, Bnd.WF]

theorem sat_pcondHF (x y s : PState S) (b : Bool) (w : List (Letter S)) (η η' : ℤ) (ed' : ED S)
    (δ : ℤ) :
    HF.Sat stLo stHi t (pcondHF x.1 y.1 b w η η' ed' δ) (Fin.cons s ![x, y]) Fin.elim0 ↔
      PCond t x y b w η η' ed' (s.2 + δ - (pH x.1 y.1 b w η η').eval t) := by
  rw [pcondHF, sat_bigAnd, List.forall_mem_cons, List.forall_mem_map,
    sat_linHF (entV_sgn x.1 y.1 b w).1 (by simp [Sgn])]
  simp only [Fin.cons_zero, cons3_one, lc_eval, addAff_eval, PCond]
  refine and_congr (by constructor <;> intro h <;> linarith) (forall₂_congr fun b' hb' => ?_)
  rw [sat_linHF (by simp [Sgn]) (sgn_of_wf (edUps_wf _ _ _ b' hb'))]
  simp only [Fin.cons_zero, cons3_two, lc_eval, addAff_eval]
  constructor <;> intro h <;> linarith

/-- `PCond` at the position `L - H` (variables `x = 0`, `y = 1`). -/
def pcondCHF (τx τy : PType S) (b : Bool) (w : List (Letter S)) (η η' : ℤ) (ed' : ED S) :
    HF (PType S) 2 0 :=
  bigAnd (linHF (entV τx τy b w).1 0 0 0
      (subA (rc (τz τy)).ly (addAff (pH τx τy b w η η') (entG τx τy b w).1)
        (-((η - η' + 3) / 2))) ::
    (edUps τy η' ed').map fun b' =>
      linHF (-b'.σ) 1 0 1 (subA (addAff b'.c (pH τx τy b w η η')) (rc (τz τy)).ly 0))

theorem sat_pcondCHF (x y : PState S) (b : Bool) (w : List (Letter S)) (η η' : ℤ)
    (ed' : ED S) :
    HF.Sat stLo stHi t (pcondCHF x.1 y.1 b w η η' ed') ![x, y] Fin.elim0 ↔
      PCond t x y b w η η' ed' ((rc (τz y.1)).ly.eval t - (pH x.1 y.1 b w η η').eval t) := by
  rw [pcondCHF, sat_bigAnd, List.forall_mem_cons, List.forall_mem_map,
    sat_linHF (entV_sgn x.1 y.1 b w).1 (by simp [Sgn])]
  simp only [Matrix.cons_val_zero, subA_eval, addAff_eval, PCond]
  refine and_congr (by constructor <;> intro h <;> linarith) (forall₂_congr fun b' hb' => ?_)
  rw [sat_linHF (sgn_of_wf (edUps_wf _ _ _ b' hb')) (by simp [Sgn])]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, subA_eval, addAff_eval]
  constructor <;> intro h <;> linarith

/-- The parallel-case meeting formula. -/
noncomputable def pHF (τx τy : PType S) (b : Bool) (w : List (Letter S)) (η η' : ℤ) (ed' : ED S)
    (R : RowSet S) : HF (PType S) 2 0 :=
  HF.or (HF.exF (bigAnd [HF.typ 0 (τz τy), pcondHF τx τy b w η η' ed' 0,
      meetHF (affA τx τy b w η η') R 0 1]))
    (HF.or (HF.exF (bigAnd [HF.typ 0 (τz τy), pcondHF τx τy b w η η' ed' 1,
      meetHF (affB τx τy b w η η') R 0 1]))
      (bigAnd [pcondCHF τx τy b w η η' ed', meetHFo (cstC τx τy b w η η') R none (some 0)]))

theorem affA_wf (τx τy : PType S) (b : Bool) (w : List (Letter S)) (η η' : ℤ) :
    (affA τx τy b w η η').WF := affineRow_wf _ _ _ _ (by simp [Bnd.WF])

theorem affB_wf (τx τy : PType S) (b : Bool) (w : List (Letter S)) (η η' : ℤ) :
    (affB τx τy b w η η').WF := affineRow_wf _ _ _ _ (by simp [Bnd.WF])

theorem cstC_wf (τx τy : PType S) (b : Bool) (w : List (Letter S)) (η η' : ℤ) :
    (cstC τx τy b w η η').WF := constRow_wf _ _ _

theorem sat_pHF (hE : Embedded S t) (x y : PState S) (b : Bool) (w : List (Letter S))
    (η η' : ℤ) (ed' : ED S) {R : RowSet S} (hR : R.WF) :
    HF.Sat stLo stHi t (pHF x.1 y.1 b w η η' ed' R) ![x, y] Fin.elim0 ↔
      (∃ hz, RowsIn t ((τz y.1), hz) ∧ PCond t x y b w η η' ed'
          (hz - (pH x.1 y.1 b w η η').eval t) ∧ Meet S t (affA x.1 y.1 b w η η') hz R x.2) ∨
      (∃ hz, RowsIn t ((τz y.1), hz) ∧ PCond t x y b w η η' ed'
          (hz + 1 - (pH x.1 y.1 b w η η').eval t) ∧ Meet S t (affB x.1 y.1 b w η η') hz R x.2) ∨
      (PCond t x y b w η η' ed' ((rc (τz y.1)).ly.eval t - (pH x.1 y.1 b w η η').eval t) ∧
        Meet S t (cstC x.1 y.1 b w η η') 0 R x.2) := by
  rw [pHF, HF.sat_or, HF.sat_or]
  simp only [HF.Sat, sat_bigAnd, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, sat_pcondHF, sat_pcondCHF, sat_meetHF hE (affA_wf _ _ _ _ _ _) hR,
    sat_meetHF hE (affB_wf _ _ _ _ _ _) hR,
    Fin.cons_zero, cons3_one]
  refine or_congr ?_ (or_congr ?_ ?_)
  · constructor
    · rintro ⟨s, hs, hτ, hc, hM⟩
      obtain ⟨τ, hz⟩ := s
      simp only at hτ
      subst hτ
      exact ⟨hz, (mem_St_iff t _).1 hs, by simpa using hc, hM⟩
    · rintro ⟨hz, hr, hc, hM⟩
      exact ⟨(τz y.1, hz), (mem_St_iff t _).2 hr, rfl, by simpa using hc, hM⟩
  · constructor
    · rintro ⟨s, hs, hτ, hc, hM⟩
      obtain ⟨τ, hz⟩ := s
      simp only at hτ
      subst hτ
      exact ⟨hz, (mem_St_iff t _).1 hs, hc, hM⟩
    · rintro ⟨hz, hr, hc, hM⟩
      exact ⟨(τz y.1, hz), (mem_St_iff t _).2 hr, rfl, hc, hM⟩
  · rw [sat_meetHFo hE (cstC_wf _ _ _ _ _ _) hR]
    rfl

/-! ## The atom -/

/-- The meeting of the output with a row, by cases. -/
noncomputable def meetYHF (τx τy : PType S) (b : Bool) (w : List (Letter S)) (η : ℤ)
    (ed' : ED S) (η' : ℤ) (R : RowSet S) : HF (PType S) 2 0 :=
  if (entV τx τy b w).2 = 0 then pHF τx τy b w η η' ed' R
  else meetHF (npRow τx τy b w η η' ed') R 1 0

theorem sat_meetYHF (hE : Embedded S t) (x y : PState S) (b : Bool) (w : List (Letter S))
    {η : ℤ} (hη : η = 0 ∨ η = 1)
    (hh : y.2 + η = (entV x.1 y.1 b w).2 * x.2 + (entG x.1 y.1 b w).2.eval t)
    (ed' : ED S) {η' : ℤ} (hη' : η' = 0 ∨ η' = 1) {R : RowSet S} (hR : R.WF) :
    HF.Sat stLo stHi t (meetYHF x.1 y.1 b w η ed' η' R) ![x, y] Fin.elim0 ↔
      MeetY t y (entI t x y b w η) ed' η' R x.2 := by
  unfold meetYHF
  by_cases hv : (entV x.1 y.1 b w).2 = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hv), sat_pHF hE x y b w η η' ed' hR]
    rw [hv, zero_mul, zero_add] at hh
    exact (meetY_p hh ed' hη' R x.2).symm
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hv), sat_meetHF hE (npRow_wf _ _ _ _ _ _ _ hv) hR]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    exact (meetY_np hη hv hh ed' hη' R x.2).symm

/-- The body: the output avoids every full tail of `x`. -/
noncomputable def bodyHF (τx τy : PType S) (b : Bool) (w : List (Letter S)) (η : ℤ) :
    HF (PType S) 2 0 :=
  bigAnd ((dataList τx).map fun p => bigAnd ((edList τy).map fun ed' =>
    bigAnd (([0, 1] : List ℤ).map fun η' => bigAnd (([0, 1] : List ℤ).map fun η'' =>
      HF.imp (sdGuard τx 0 p.1) (HF.imp (edGuard τx 0 p.2) (HF.imp (edGuard τy 1 ed')
        (HF.neg (meetYHF τx τy b w η ed' η' (tailRow τx η'' p.1 p.2)))))))))

theorem sat_bodyHF (hE : Embedded S t) (x y : PState S) (b : Bool) (w : List (Letter S))
    {η : ℤ} (hη : η = 0 ∨ η = 1)
    (hh : y.2 + η = (entV x.1 y.1 b w).2 * x.2 + (entG x.1 y.1 b w).2.eval t) :
    HF.Sat stLo stHi t (bodyHF x.1 y.1 b w η) ![x, y] Fin.elim0 ↔ PB t x y (entI t x y b w η) := by
  rw [pb_iff_meetY hE, bodyHF]
  simp only [sat_bigAnd_map]
  constructor
  · intro H p hp hs he ed' hed' he' η' hη' η'' hη''
    have := H p hp ed' hed' η' hη' η'' hη''
    rw [mem_dataList] at hp
    rw [HF.sat_imp, HF.sat_imp, HF.sat_imp, sat_sdGuard x 0 _ rfl hp.1, sat_edGuard x 0 _ rfl hp.2,
      sat_edGuard y 1 _ rfl hed', HF.Sat,
      sat_meetYHF hE x y b w hη hh ed' ((par_mem_iff η').1 hη') (tailRow_wf _ _ _ _)] at this
    exact this hs he he'
  · intro H p hp ed' hed' η' hη' η'' hη''
    have hp' := mem_dataList.1 hp
    rw [HF.sat_imp, HF.sat_imp, HF.sat_imp, sat_sdGuard x 0 _ rfl hp'.1,
      sat_edGuard x 0 _ rfl hp'.2, sat_edGuard y 1 _ rfl hed', HF.Sat,
      sat_meetYHF hE x y b w hη hh ed' ((par_mem_iff η').1 hη') (tailRow_wf _ _ _ _)]
    exact fun hs he he' => H p hp hs he ed' hed' he' η' hη' η'' hη''

/-- The formula of condition 3 (b) for fixed types. -/
noncomputable def dbT (τx τy : PType S) : HF (PType S) 2 0 :=
  bigAnd ([false, true].flatMap fun b => (wordsLT S S.C).flatMap fun w =>
    ([0, 1] : List ℤ).map fun η =>
      HF.imp (twHF τx τy b w η) (HF.imp (hhHF τx τy b w η) (bodyHF τx τy b w η)))

theorem sat_dbT (hE : Embedded S t) (x y : PState S) (hy : RowsIn t y) :
    HF.Sat stLo stHi t (dbT x.1 y.1) ![x, y] Fin.elim0 ↔ DbR t x y := by
  rw [dbR_iff_witness hE x y hy, dbT, sat_bigAnd]
  simp only [List.mem_flatMap, List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro H b w η hη hW hh
    have := H _ b (by cases b <;> simp) w ((mem_wordsLT _ _).2 hW.2.2.2.1) η
      ((par_mem_iff η).2 hη) rfl
    rw [HF.sat_imp, HF.sat_imp, sat_twHF hE x y b hW.2.2.2.1, sat_hhHF,
      sat_bodyHF hE x y b w hη hh] at this
    exact this hW hh
  · rintro H φ b - w hw η hη rfl
    have hη' := (par_mem_iff η).1 hη
    rw [HF.sat_imp, HF.sat_imp, sat_twHF hE x y b ((mem_wordsLT _ _).1 hw), sat_hhHF]
    intro hW hh
    rw [sat_bodyHF hE x y b w hη' hh]
    exact H b w η hη' hW hh

/-- **Condition 3 (b) is definable.** -/
theorem def2_DbR : Def2 S DbR :=
  ⟨typeSplit2 dbT, 0, fun t _ hV _ x _ y hy => by
    rw [sat_typeSplit2, sat_dbT (valid_embedded hV) x y ((mem_St_iff t y).1 hy)]⟩

end ClaudeChallenge2.State
