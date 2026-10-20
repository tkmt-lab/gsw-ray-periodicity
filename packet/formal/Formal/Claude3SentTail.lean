import Formal.Claude3SentPar

/-!
# Theorem 1a, G6: full tails as rows (the atoms `DaR`, `DcR`)

Written by a Claude worker (2026-10-20, Theorem 1a, parts G6/A).

The full tail `OutV t y s e` (`OwnStart t y s`, `ExitAt t y e`) of a state is, for each parity
`η` of the index, a row of `y` with own-height bounds: the start is `lo` or pinned by the root
corner (`SD`), the exit is `hi` or pinned by the terminal corner (`ED`).

* `SD`, `ED`, `SDOK`, `EDOK`, `ownStart_iff`, `exitAt_iff_ed`;
* `tailRow`, `tail_bounds_iff`, `disj_iff_meet` : two full tails are disjoint iff the tail rows
  do not meet (for all parities);
* `def2_DaR`, `def2_DcR`.
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo
open R002.Claude3Fold (HF St)

variable {S : Sig} {t : ℕ}

/-- Start data of a full tail. -/
inductive SD (S : Sig)
  | lo
  | pin (m : Fin S.M) (w : List (Letter S)) (η : ℤ)

/-- Exit data of a full tail. -/
inductive ED (S : Sig)
  | hi
  | pin (m : Fin S.M) (w : List (Letter S)) (η : ℤ)

/-- The start data is that of `y`, with start index `s`. -/
def SDOK (t : ℕ) (y : PState S) : SD S → ℤ → Prop
  | .lo, s => y.1.root = none ∧ s = loS t y
  | .pin m w η, s => y.1.root = some m ∧ (η = 0 ∨ η = 1) ∧ PinOK t y m w η ∧
      s = 2 * (cornerY S y.1.k m w).1.eval t + η

/-- The exit data is that of `y`, with exit index `e`. -/
def EDOK (t : ℕ) (y : PState S) : ED S → ℤ → Prop
  | .hi, e => y.1.term = none ∧ e = hiS t y
  | .pin m w η, e => y.1.term = some m ∧ (η = 0 ∨ η = 1) ∧ PinOK t y m w η ∧
      e + 2 = 2 * (cornerY S y.1.k m w).1.eval t + η

/-- All start data of a type. -/
def sdList (τ : PType S) : List (SD S) :=
  match τ.root with
  | none => [.lo]
  | some m => (wordsLT S S.C).flatMap fun w => ([0, 1] : List ℤ).map fun η => .pin m w η

/-- All exit data of a type. -/
def edList (τ : PType S) : List (ED S) :=
  match τ.term with
  | none => [.hi]
  | some m => (wordsLT S S.C).flatMap fun w => ([0, 1] : List ℤ).map fun η => .pin m w η

theorem ownStart_iff (hE : Embedded S t) (y : PState S) (s : ℤ) :
    OwnStart t y s ↔ ∃ sd ∈ sdList y.1, SDOK t y sd s := by
  unfold OwnStart sdList
  rw [rootAt_iff_pin hE]
  cases h : y.1.root with
  | none => simp [SDOK, h]
  | some m =>
    simp only [reduceCtorEq, false_and, false_or, Option.some.injEq, List.mem_flatMap,
      List.mem_map, mem_wordsLT]
    constructor
    · rintro ⟨m', rfl, w, η, hη, hp, rfl⟩
      exact ⟨_, ⟨w, hp.1, η, by rcases hη with rfl | rfl <;> simp, rfl⟩, h, hη, hp, rfl⟩
    · rintro ⟨sd, ⟨w, -, η, -, rfl⟩, h', hη, hp, rfl⟩
      rw [h, Option.some.injEq] at h'
      exact ⟨m, h', w, η, hη, hp, rfl⟩

theorem exitAt_iff_ed (hE : Embedded S t) (y : PState S) (e : ℤ) :
    ExitAt t y e ↔ ∃ ed ∈ edList y.1, EDOK t y ed e := by
  unfold edList
  cases h : y.1.term with
  | none =>
    simp only [List.mem_singleton, exists_eq_left, EDOK, h, true_and]
    exact ⟨fun H => H.1 h, fun H => ⟨fun _ => H, fun m hm => by simp [h] at hm⟩⟩
  | some m =>
    rw [exitAt_some_iff h, atCorner_iff_pin hE]
    simp only [List.mem_flatMap, List.mem_map, mem_wordsLT]
    constructor
    · rintro ⟨w, η, hη, hp, he⟩
      exact ⟨_, ⟨w, hp.1, η, by rcases hη with rfl | rfl <;> simp, rfl⟩, h, hη, hp, he⟩
    · rintro ⟨ed, ⟨w, -, η, -, rfl⟩, -, hη, hp, he⟩
      exact ⟨w, η, hη, hp, he⟩

/-- Lower position bounds of the tail row of parity `η`. -/
def sdLows (τ : PType S) (η : ℤ) : SD S → List Bnd
  | .lo => (lowsY τ η).map fun b => ⟨b.σ, affAdd b.c 1⟩
  | .pin m w ηr => [⟨0, affAdd (cornerY S τ.k m w).1 ((ηr - η + 3) / 2)⟩]

/-- Upper position bounds of the tail row of parity `η`. -/
def edUps (τ : PType S) (η : ℤ) : ED S → List Bnd
  | .hi => (upsY τ η).map fun b => ⟨b.σ, affAdd b.c 1⟩
  | .pin m w ηt => [⟨0, affAdd (cornerY S τ.k m w).1 ((ηt - η) / 2)⟩]

/-- The tail row. -/
def tailRow (τ : PType S) (η : ℤ) (sd : SD S) (ed : ED S) : RowSet S :=
  rowPtRow τ.f τ.k η (sdLows τ η sd) (edUps τ η ed)

theorem tailRow_wf (τ : PType S) (η : ℤ) (sd : SD S) (ed : ED S) : (tailRow τ η sd ed).WF := by
  refine rowPtRow_wf _ _ _ ?_ ?_
  · cases sd with
    | lo => simpa [sdLows, Bnd.WF] using lowsY_wf τ η
    | pin => simp [sdLows, Bnd.WF]
  · cases ed with
    | hi => simpa [edUps, Bnd.WF] using upsY_wf τ η
    | pin => simp [edUps, Bnd.WF]

theorem sd_bounds_iff (y : PState S) {sd : SD S} {s : ℤ} (hs : SDOK t y sd s) {η : ℤ}
    (hη : η = 0 ∨ η = 1) (X : ℤ) :
    s + 2 ≤ 2 * X + η ↔ ∀ b ∈ sdLows y.1 η sd, b.σ * y.2 + b.c.eval t ≤ X := by
  cases sd with
  | lo =>
    obtain ⟨-, rfl⟩ := hs
    rw [show loS t y + 2 ≤ 2 * X + η ↔ loS t y ≤ 2 * (X - 1) + η by constructor <;> intro <;>
      omega, lo_le_iff y hη]
    simp only [sdLows, List.forall_mem_map, affAdd_eval]
    exact forall₂_congr fun b _ => by constructor <;> intro <;> omega
  | pin m w ηr =>
    obtain ⟨-, hηr, -, rfl⟩ := hs
    simp only [sdLows, List.mem_singleton, forall_eq, zero_mul, zero_add, affAdd_eval]
    omega

theorem ed_bounds_iff (y : PState S) {ed : ED S} {e : ℤ} (he : EDOK t y ed e) {η : ℤ}
    (hη : η = 0 ∨ η = 1) (X : ℤ) :
    2 * X + η ≤ e + 2 ↔ ∀ b ∈ edUps y.1 η ed, X ≤ b.σ * y.2 + b.c.eval t := by
  cases ed with
  | hi =>
    obtain ⟨-, rfl⟩ := he
    rw [show 2 * X + η ≤ hiS t y + 2 ↔ 2 * (X - 1) + η ≤ hiS t y by constructor <;> intro <;>
      omega, le_hi_iff y hη]
    simp only [edUps, List.forall_mem_map, affAdd_eval]
    exact forall₂_congr fun b _ => by constructor <;> intro <;> omega
  | pin m w ηt =>
    obtain ⟨-, hηt, -, he⟩ := he
    simp only [edUps, List.mem_singleton, forall_eq, zero_mul, zero_add, affAdd_eval]
    omega

/-- A full tail vertex is a point of a tail row. -/
theorem outV_iff (y : PState S) {sd : SD S} {ed : ED S} {s e : ℤ} (hs : SDOK t y sd s)
    (he : EDOK t y ed e) (v : Vertex S t) :
    OutV t y s e v ↔ ∃ η : ℤ, (η = 0 ∨ η = 1) ∧ ∃ z, (tailRow y.1 η sd ed).At t y.2 z ∧
      ∃ hz : (S.chart y.1.f).Mem t z, pt S t y.1.f z hz = v := by
  constructor
  · rintro ⟨j, h₁, h₂, hz, rfl⟩
    obtain ⟨X, η, hη, rfl⟩ : ∃ X η : ℤ, (η = 0 ∨ η = 1) ∧ j = 2 * X + η :=
      ⟨j / 2, j % 2, by omega, by omega⟩
    exact ⟨η, hη, _, (rowPtRow_at _ _ hη _ _ _ _).2 ⟨X, ⟨(sd_bounds_iff y hs hη X).1 h₁,
      (ed_bounds_iff y he hη X).1 h₂⟩, rfl⟩, hz, rfl⟩
  · rintro ⟨η, hη, z, hA, hz, rfl⟩
    rw [tailRow, rowPtRow_at _ _ hη] at hA
    obtain ⟨X, ⟨h₁, h₂⟩, rfl⟩ := hA
    exact ⟨2 * X + η, (sd_bounds_iff y hs hη X).2 h₁, (ed_bounds_iff y he hη X).2 h₂, hz, rfl⟩

/-- Disjointness of a set of vertices given by rows from a full tail. -/
theorem disj_tail_iff (y : PState S) {sd : SD S} {ed : ED S} {s e : ℤ} (hs : SDOK t y sd s)
    (he : EDOK t y ed e) (R : RowSet S) (h : ℤ) :
    (∀ v, (∃ z, R.At t h z ∧ ∃ hz : (S.chart R.f).Mem t z, pt S t R.f z hz = v) →
        ¬ OutV t y s e v) ↔
      ∀ η : ℤ, (η = 0 ∨ η = 1) → ¬ Meet S t R h (tailRow y.1 η sd ed) y.2 := by
  simp only [outV_iff y hs he]
  constructor
  · rintro H η hη ⟨z₁, z₂, h₁, h₂, hz₁, hz₂, hq⟩
    exact H _ ⟨z₁, h₁, hz₁, rfl⟩ ⟨η, hη, z₂, h₂, hz₂, hq.symm⟩
  · rintro H v ⟨z₁, h₁, hz₁, rfl⟩ ⟨η, hη, z₂, h₂, hz₂, hq⟩
    exact H η hη ⟨z₁, z₂, h₁, h₂, hz₁, hz₂, hq.symm⟩

/-! ## Guards of the data -/

/-- The start data holds (for data of the list of the type). -/
noncomputable def sdGuard {n : ℕ} (τ : PType S) (v : Fin n) : SD S → HF (PType S) n 0
  | .lo => hfTrue
  | .pin m w η => pinHF τ m w η v

/-- The exit data holds (for data of the list of the type). -/
noncomputable def edGuard {n : ℕ} (τ : PType S) (v : Fin n) : ED S → HF (PType S) n 0
  | .hi => hfTrue
  | .pin m w η => pinHF τ m w η v

theorem sat_sdGuard {n : ℕ} (y : PState S) (v : Fin n) (ν : Fin n → PState S) (hv : ν v = y)
    {sd : SD S} (hsd : sd ∈ sdList y.1) :
    HF.Sat stLo stHi t (sdGuard y.1 v sd) ν Fin.elim0 ↔ ∃ s, SDOK t y sd s := by
  unfold sdList at hsd
  cases h : y.1.root with
  | none =>
    simp only [h, List.mem_singleton] at hsd
    subst hsd
    simp [sdGuard, SDOK, h]
  | some m =>
    simp only [h, List.mem_flatMap, List.mem_map, mem_wordsLT] at hsd
    obtain ⟨w, hw, η, hη, rfl⟩ := hsd
    have hη' : η = 0 ∨ η = 1 := by simpa using hη
    rw [sdGuard, sat_pinHF y m w η v ν _ hv hw]
    simp only [SDOK, h, hη', true_and, exists_eq_right]

theorem sat_edGuard {n : ℕ} (y : PState S) (v : Fin n) (ν : Fin n → PState S) (hv : ν v = y)
    {ed : ED S} (hed : ed ∈ edList y.1) :
    HF.Sat stLo stHi t (edGuard y.1 v ed) ν Fin.elim0 ↔ ∃ e, EDOK t y ed e := by
  unfold edList at hed
  cases h : y.1.term with
  | none =>
    simp only [h, List.mem_singleton] at hed
    subst hed
    simp [edGuard, EDOK, h]
  | some m =>
    simp only [h, List.mem_flatMap, List.mem_map, mem_wordsLT] at hed
    obtain ⟨w, hw, η, hη, rfl⟩ := hed
    have hη' : η = 0 ∨ η = 1 := by simpa using hη
    rw [edGuard, sat_pinHF y m w η v ν _ hv hw]
    simp only [EDOK, h, hη', true_and]
    exact ⟨fun H => ⟨2 * (cornerY S y.1.k m w).1.eval t + η - 2, H, by ring⟩,
      fun ⟨_, H, _⟩ => H⟩

theorem sat_bigAnd_map {α : Type} {n k : ℕ} {lo hi : PType S → R002.Claude3Fold.Aff}
    (L : List α) (F : α → HF (PType S) n k) (ν : Fin n → PState S) (V : Fin k → Set (PState S)) :
    HF.Sat lo hi t (bigAnd (L.map F)) ν V ↔ ∀ a ∈ L, HF.Sat lo hi t (F a) ν V := by
  rw [sat_bigAnd, List.forall_mem_map]

/-! ## Condition 3 (a) -/

/-- Data pairs of a type. -/
def dataList (τ : PType S) : List (SD S × ED S) :=
  (sdList τ).flatMap fun sd => (edList τ).map fun ed => (sd, ed)

theorem mem_dataList {τ : PType S} {p : SD S × ED S} :
    p ∈ dataList τ ↔ p.1 ∈ sdList τ ∧ p.2 ∈ edList τ := by
  obtain ⟨sd, ed⟩ := p
  simp [dataList]

theorem par_mem_iff (η : ℤ) : η ∈ ([0, 1] : List ℤ) ↔ (η = 0 ∨ η = 1) := by simp

/-- Condition 3 (a) by data. -/
theorem daR_iff (hE : Embedded S t) (y y' : PState S) :
    DaR t y y' ↔ ∀ p ∈ dataList y.1, ∀ p' ∈ dataList y'.1, (∃ s, SDOK t y p.1 s) →
      (∃ e, EDOK t y p.2 e) → (∃ s, SDOK t y' p'.1 s) → (∃ e, EDOK t y' p'.2 e) →
        ∀ η ∈ ([0, 1] : List ℤ), ∀ η' ∈ ([0, 1] : List ℤ),
          ¬ Meet S t (tailRow y.1 η p.1 p.2) y.2 (tailRow y'.1 η' p'.1 p'.2) y'.2 := by
  constructor
  · rintro H p hp p' hp' ⟨s, hs⟩ ⟨e, he⟩ ⟨s', hs'⟩ ⟨e', he'⟩ η hη η' hη'
      ⟨z₁, z₂, h₁, h₂, hz₁, hz₂, hq⟩
    rw [mem_dataList] at hp hp'
    exact H s e s' e' ((ownStart_iff hE y s).2 ⟨_, hp.1, hs⟩)
      ((exitAt_iff_ed hE y e).2 ⟨_, hp.2, he⟩)
      ((ownStart_iff hE y' s').2 ⟨_, hp'.1, hs'⟩) ((exitAt_iff_ed hE y' e').2 ⟨_, hp'.2, he'⟩) _
      ((outV_iff y hs he _).2 ⟨η, (par_mem_iff η).1 hη, z₁, h₁, hz₁, rfl⟩)
      ((outV_iff y' hs' he' _).2 ⟨η', (par_mem_iff η').1 hη', z₂, h₂, hz₂, hq.symm⟩)
  · intro H s e s' e' hs he hs' he' v hv hv'
    obtain ⟨sd, hsd, hs₁⟩ := (ownStart_iff hE y s).1 hs
    obtain ⟨ed, hed, he₁⟩ := (exitAt_iff_ed hE y e).1 he
    obtain ⟨sd', hsd', hs₁'⟩ := (ownStart_iff hE y' s').1 hs'
    obtain ⟨ed', hed', he₁'⟩ := (exitAt_iff_ed hE y' e').1 he'
    obtain ⟨η, hη, z₁, h₁, hz₁, rfl⟩ := (outV_iff y hs₁ he₁ _).1 hv
    obtain ⟨η', hη', z₂, h₂, hz₂, hq⟩ := (outV_iff y' hs₁' he₁' _).1 hv'
    exact H (sd, ed) (mem_dataList.2 ⟨hsd, hed⟩) (sd', ed') (mem_dataList.2 ⟨hsd', hed'⟩)
      ⟨s, hs₁⟩ ⟨e, he₁⟩ ⟨s', hs₁'⟩ ⟨e', he₁'⟩ η ((par_mem_iff η).2 hη) η' ((par_mem_iff η').2 hη')
      ⟨z₁, z₂, h₁, h₂, hz₁, hz₂, hq.symm⟩

/-- The formula of condition 3 (a) for fixed types. -/
noncomputable def daT (τ τ' : PType S) : HF (PType S) 2 0 :=
  bigAnd ((dataList τ).map fun p => bigAnd ((dataList τ').map fun p' =>
    HF.imp (sdGuard τ 0 p.1) (HF.imp (edGuard τ 0 p.2) (HF.imp (sdGuard τ' 1 p'.1)
      (HF.imp (edGuard τ' 1 p'.2) (bigAnd (([0, 1] : List ℤ).map fun η =>
        bigAnd (([0, 1] : List ℤ).map fun η' =>
          HF.neg (meetHF (tailRow τ η p.1 p.2) (tailRow τ' η' p'.1 p'.2) 0 1)))))))))

theorem sat_daT (hE : Embedded S t) (x y : PState S) :
    HF.Sat stLo stHi t (daT x.1 y.1) ![x, y] Fin.elim0 ↔ DaR t x y := by
  rw [daR_iff hE, daT, sat_bigAnd_map]
  refine forall₂_congr fun p hp => ?_
  rw [sat_bigAnd_map]
  refine forall₂_congr fun p' hp' => ?_
  rw [mem_dataList] at hp hp'
  rw [HF.sat_imp, HF.sat_imp, HF.sat_imp, HF.sat_imp, sat_sdGuard x 0 _ rfl hp.1,
    sat_edGuard x 0 _ rfl hp.2, sat_sdGuard y 1 _ rfl hp'.1, sat_edGuard y 1 _ rfl hp'.2]
  simp only [sat_bigAnd_map, HF.Sat, sat_meetHF hE (tailRow_wf _ _ _ _) (tailRow_wf _ _ _ _),
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Condition 3 (a) is definable.** -/
theorem def2_DaR : Def2 S DaR :=
  ⟨typeSplit2 daT, 0, fun t _ hV _ x _ y _ => by
    rw [sat_typeSplit2, sat_daT (valid_embedded hV)]⟩

/-! ## Condition 3 (c) -/

theorem cornerNbr_at {x : PState S} {m : Fin S.M} {w : List (Letter S)} {ηc : ℤ}
    (hηc : ηc = 0 ∨ ηc = 1) (hp : PinOK t x m w ηc) (n : ℤ) (P : ℤ × ℤ) :
    (cornerNbr x.1 m w ηc n).At t 0 P ↔
      P = rp x (2 * (cornerY S x.1.k m w).1.eval t + ηc + n) := by
  have hrp : rp x (2 * (cornerY S x.1.k m w).1.eval t + ηc) =
      (wordAff S w).apply t ((S.mx m).eval t, (S.my m).eval t) :=
    (rp_eq_corner_iff x m w _).2 ⟨ηc, hηc, rfl, hp.2.2.2⟩
  rw [cornerNbr, nbrRow_at', rp_shift x _ _ _ hηc, hrp]
  constructor
  · rintro ⟨p, hp', -, rfl⟩
    rw [cornerRow_at] at hp'
    rw [hp']
  · rintro rfl
    exact ⟨_, (cornerRow_at m _).2 rfl, hp.2.2.1, rfl⟩

theorem dcR_iff (hE : Embedded S t) (x y : PState S) :
    DcR t x y ↔ ∀ m, x.1.root = some m → ∀ w ∈ wordsLT S S.C, ∀ ηr ∈ ([0, 1] : List ℤ),
      PinOK t x m w ηr → ∀ p ∈ dataList y.1, (∃ s, SDOK t y p.1 s) → (∃ e, EDOK t y p.2 e) →
        ∀ n ∈ ([0, 1] : List ℤ), ∀ η ∈ ([0, 1] : List ℤ),
          ¬ Meet S t (cornerNbr x.1 m w ηr n) 0 (tailRow y.1 η p.1 p.2) y.2 := by
  constructor
  · rintro H m hm w - ηr hηr hp p hpd ⟨s, hs⟩ ⟨e, he⟩ n hn η hη ⟨z₁, z₂, h₁, h₂, hz₁, hz₂, hq⟩
    rw [mem_dataList] at hpd
    have hηr' := (par_mem_iff ηr).1 hηr
    rw [cornerNbr_at hηr' hp] at h₁
    subst h₁
    refine H _ s e ((rootAt_iff_pin hE x _).2 ⟨m, hm, w, ηr, hηr', hp, rfl⟩)
      ((ownStart_iff hE y s).2 ⟨_, hpd.1, hs⟩) ((exitAt_iff_ed hE y e).2 ⟨_, hpd.2, he⟩) _ ?_
      ((outV_iff y hs he _).2 ⟨η, (par_mem_iff η).1 hη, z₂, h₂, hz₂, hq.symm⟩)
    have hv : RV t x (2 * (cornerY S x.1.k m w).1.eval t + ηr + n)
        (pt S t (cornerNbr x.1 m w ηr n).f _ hz₁) := ⟨hz₁, rfl⟩
    rcases (par_mem_iff n).1 hn with rfl | rfl
    · left; simpa using hv
    · right; exact hv
  · intro H i₀ s e hr hs he v hv hout
    obtain ⟨m, hm, w, ηr, hηr, hp, rfl⟩ := (rootAt_iff_pin hE x _).1 hr
    obtain ⟨sd, hsd, hs₁⟩ := (ownStart_iff hE y s).1 hs
    obtain ⟨ed, hed, he₁⟩ := (exitAt_iff_ed hE y e).1 he
    obtain ⟨η, hη, z₂, h₂, hz₂, hq⟩ := (outV_iff y hs₁ he₁ _).1 hout
    obtain ⟨n, hn, hz₁, rfl⟩ : ∃ n ∈ ([0, 1] : List ℤ), ∃ hz : (S.chart x.1.f).Mem t
        (rp x (2 * (cornerY S x.1.k m w).1.eval t + ηr + n)), pt S t x.1.f _ hz = v := by
      rcases hv with ⟨hz, rfl⟩ | ⟨hz, rfl⟩
      · exact ⟨0, by simp, by simpa using hz, by simp⟩
      · exact ⟨1, by simp, hz, rfl⟩
    exact H m hm w ((mem_wordsLT _ _).2 hp.1) ηr ((par_mem_iff ηr).2 hηr) hp (sd, ed)
      (mem_dataList.2 ⟨hsd, hed⟩) ⟨s, hs₁⟩ ⟨e, he₁⟩ n hn η ((par_mem_iff η).2 hη)
      ⟨_, z₂, (cornerNbr_at hηr hp n _).2 rfl, h₂, hz₁, hz₂, hq.symm⟩

/-- The formula of condition 3 (c) for fixed types. -/
noncomputable def dcT (τx τy : PType S) : HF (PType S) 2 0 :=
  match τx.root with
  | none => hfTrue
  | some m => bigAnd ((wordsLT S S.C).map fun w => bigAnd (([0, 1] : List ℤ).map fun ηr =>
      HF.imp (pinHF τx m w ηr 0) (bigAnd ((dataList τy).map fun p =>
        HF.imp (sdGuard τy 1 p.1) (HF.imp (edGuard τy 1 p.2)
          (bigAnd (([0, 1] : List ℤ).map fun n => bigAnd (([0, 1] : List ℤ).map fun η =>
            HF.neg (meetHFo (cornerNbr τx m w ηr n) (tailRow τy η p.1 p.2) none (some 1))))))))))

theorem sat_dcT (hE : Embedded S t) (x y : PState S) :
    HF.Sat stLo stHi t (dcT x.1 y.1) ![x, y] Fin.elim0 ↔ DcR t x y := by
  rw [dcR_iff hE]
  unfold dcT
  cases h : x.1.root with
  | none => simp
  | some m =>
    simp only [Option.some.injEq, forall_eq']
    rw [sat_bigAnd_map]
    refine forall₂_congr fun w hw => ?_
    rw [sat_bigAnd_map]
    refine forall₂_congr fun ηr hηr => ?_
    rw [HF.sat_imp, sat_pinHF x m w ηr 0 _ _ rfl ((mem_wordsLT _ _).1 hw), sat_bigAnd_map]
    refine imp_congr_right fun _ => forall₂_congr fun p hp => ?_
    rw [mem_dataList] at hp
    rw [HF.sat_imp, HF.sat_imp, sat_sdGuard y 1 _ rfl hp.1, sat_edGuard y 1 _ rfl hp.2]
    simp only [sat_bigAnd_map, HF.Sat,
      sat_meetHFo hE (cornerNbr_wf _ _ _ _ _) (tailRow_wf _ _ _ _)]
    rfl

/-- **Condition 3 (c) is definable.** -/
theorem def2_DcR : Def2 S DcR :=
  ⟨typeSplit2 dcT, 0, fun t _ hV _ x _ y _ => by
    rw [sat_typeSplit2, sat_dcT (valid_embedded hV)]⟩

end ClaudeChallenge2.State
