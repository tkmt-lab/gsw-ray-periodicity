import Formal.Claude3SentPin

/-!
# Theorem 1a, G6: the degree atoms

Written by a Claude worker (2026-10-20, Theorem 1a, parts G6/A).

* closure of `Def1`/`Def2` under `∨`, transfer along equivalence (`def1_congr`, `def2_congr`);
* `typeSplit1`;
* `pinned_deg_iff` : the degree at a point of the row at a fixed offset from a pinned corner is
  a sentence (`degAllHFo` of a neighbour row of the corner, height `0`);
* `def1_E1P` (root degrees), `def1_T1` (terminal degrees, `T1`),
  `def1_pr_qT`, `def2_pt_qT` (via `T1` and the uniqueness of the exit index).
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo
open R002.Claude3Fold (HF St)

variable {S : Sig} {t : ℕ}

/-! ## Closure -/

theorem def1_congr {P Q : ℕ → PState S → Prop} (hP : Def1 S P) (t₀ : ℕ)
    (h : ∀ t, t₀ ≤ t → Valid S t → ClaudeChallenge2.TrianglesInCharts S t →
      ∀ x ∈ St (stLo (S := S)) stHi t, (P t x ↔ Q t x)) : Def1 S Q := by
  obtain ⟨φ, t₂, hφ⟩ := hP
  exact ⟨φ, t₂ + t₀, fun t ht hV hT x hx => (hφ t (by omega) hV hT x hx).trans
    (h t (by omega) hV hT x hx)⟩

theorem def2_congr {P Q : ℕ → PState S → PState S → Prop} (hP : Def2 S P) (t₀ : ℕ)
    (h : ∀ t, t₀ ≤ t → Valid S t → ClaudeChallenge2.TrianglesInCharts S t →
      ∀ x ∈ St (stLo (S := S)) stHi t, ∀ y ∈ St (stLo (S := S)) stHi t,
        (P t x y ↔ Q t x y)) : Def2 S Q := by
  obtain ⟨φ, t₂, hφ⟩ := hP
  exact ⟨φ, t₂ + t₀, fun t ht hV hT x hx y hy => (hφ t (by omega) hV hT x hx y hy).trans
    (h t (by omega) hV hT x hx y hy)⟩

theorem def1_or {P Q : ℕ → PState S → Prop} (hP : Def1 S P) (hQ : Def1 S Q) :
    Def1 S (fun t x => P t x ∨ Q t x) := by
  obtain ⟨φ, t₁, hφ⟩ := hP
  obtain ⟨ψ, t₂, hψ⟩ := hQ
  refine ⟨HF.or φ ψ, t₁ + t₂, fun t ht hV hT x hx => ?_⟩
  rw [HF.sat_or, hφ t (by omega) hV hT x hx, hψ t (by omega) hV hT x hx]

theorem def2_or_snd {R : ℕ → PState S → PState S → Prop} {Q : ℕ → PState S → Prop}
    (hR : Def2 S R) (hQ : Def1 S Q) : Def2 S (fun t x y => R t x y ∨ Q t y) := by
  obtain ⟨φ, t₁, hφ⟩ := hR
  obtain ⟨ψ, t₂, hψ⟩ := hQ
  refine ⟨HF.or φ (at1 ψ 1), t₁ + t₂, fun t ht hV hT x hx y hy => ?_⟩
  rw [HF.sat_or, hφ t (by omega) hV hT x hx y hy, sat_at1]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [hψ t (by omega) hV hT y hy]

/-- Cases on the type of the state variable. -/
noncomputable def typeSplit1 {k : ℕ} (F : PType S → HF (PType S) 1 k) : HF (PType S) 1 k :=
  bigOr ((allTypes S).map fun τ => HF.and (HF.typ 0 τ) (F τ))

theorem sat_typeSplit1 {lo hi : PType S → R002.Claude3Fold.Aff} {k : ℕ}
    (F : PType S → HF (PType S) 1 k) (x : PState S) (V : Fin k → Set (PState S)) :
    HF.Sat lo hi t (typeSplit1 F) ![x] V ↔ HF.Sat lo hi t (F x.1) ![x] V := by
  simp only [typeSplit1, sat_bigOr, List.mem_map]
  constructor
  · rintro ⟨φ, ⟨τ, -, rfl⟩, h⟩
    simp only [HF.Sat, Matrix.cons_val_zero] at h
    obtain ⟨rfl, h⟩ := h
    exact h
  · intro h
    exact ⟨_, ⟨x.1, mem_allTypes _, rfl⟩, by simpa using h⟩

/-! ## Degrees near a pinned corner -/

/-- The neighbour row of corner `m` along `w`, shifted by `n` steps of the row walk. -/
def cornerNbr (τ : PType S) (m : Fin S.M) (w : List (Letter S)) (ηc n : ℤ) : RowSet S :=
  nbrRow (cornerRow S m) τ.f w (rotN τ.k (dS ηc n))

theorem cornerNbr_wf (τ : PType S) (m : Fin S.M) (w : List (Letter S)) (ηc n : ℤ) :
    (cornerNbr τ m w ηc n).WF := nbrRow_wf (cornerRow_wf m) _ _ _

theorem cornerNbr_single (τ : PType S) (m : Fin S.M) (w : List (Letter S)) (ηc n : ℤ) :
    (cornerNbr τ m w ηc n).Single t 0 := nbrRow_single (cornerRow_single m) _ _ _

theorem pinned_deg_iff (hE : Embedded S t) {y : PState S} {m : Fin S.M} {w : List (Letter S)}
    {ηc : ℤ} (hηc : ηc = 0 ∨ ηc = 1) (hp : PinOK t y m w ηc) (n : ℤ) (d : ℕ) {k : ℕ}
    (ν : Fin 1 → PState S) (V : Fin k → Set (PState S)) :
    HF.Sat stLo stHi t (degAllHFo (cornerNbr y.1 m w ηc n) d none) ν V ↔
      ∀ v, RV t y (2 * (cornerY S y.1.k m w).1.eval t + ηc + n) v → deg (graph S t) v = d := by
  rw [sat_degAllHFo hE (cornerNbr_wf _ _ _ _ _) d none ν V (cornerNbr_single _ _ _ _ _)]
  have hrp : rp y (2 * (cornerY S y.1.k m w).1.eval t + ηc) =
      (wordAff S w).apply t ((S.mx m).eval t, (S.my m).eval t) :=
    (rp_eq_corner_iff y m w _).2 ⟨ηc, hηc, rfl, hp.2.2.2⟩
  have hAt : ∀ P, (cornerNbr y.1 m w ηc n).At t (hgt ν none) P ↔
      P = rp y (2 * (cornerY S y.1.k m w).1.eval t + ηc + n) := by
    intro P
    rw [cornerNbr, nbrRow_at', rp_shift y _ _ _ hηc, hrp]
    constructor
    · rintro ⟨p, hp', -, rfl⟩
      rw [show hgt ν none = 0 from rfl, cornerRow_at] at hp'
      rw [hp']
    · rintro rfl
      exact ⟨_, (cornerRow_at m _).2 rfl, hp.2.2.1, rfl⟩
  constructor
  · rintro H v ⟨hz, rfl⟩
    exact H _ ((hAt _).2 rfl) hz
  · intro H P hA hP
    rw [hAt] at hA
    subst hA
    exact H _ ⟨hP, rfl⟩

/-! ## Root degrees -/

/-- The root degree formula for a type. -/
noncomputable def e1T (τ : PType S) : HF (PType S) 1 0 :=
  match τ.root with
  | none => hfTrue
  | some m => bigAnd ((wordsLT S S.C).flatMap fun w => ([0, 1] : List ℤ).map fun ηr =>
      HF.imp (pinHF τ m w ηr 0)
        (HF.and (degAllHFo (cornerNbr τ m w ηr 0) 5 none)
          (degAllHFo (cornerNbr τ m w ηr 1) 6 none)))

theorem rootAt_iff_pin (hE : Embedded S t) (x : PState S) (i : ℤ) :
    RootAt t x i ↔ ∃ m, x.1.root = some m ∧ ∃ w ηr, (ηr = 0 ∨ ηr = 1) ∧ PinOK t x m w ηr ∧
      i = 2 * (cornerY S x.1.k m w).1.eval t + ηr := by
  simp only [RootAt, atCorner_iff_pin hE]

theorem sat_e1T (hE : Embedded S t) (x : PState S) :
    HF.Sat stLo stHi t (e1T x.1) ![x] Fin.elim0 ↔ E1P t x := by
  unfold e1T E1P
  simp only [rootAt_iff_pin hE]
  cases h : x.1.root with
  | none => simp
  | some m =>
    simp only [sat_bigAnd, List.mem_flatMap, List.mem_map, mem_wordsLT, forall_exists_index,
      and_imp, Option.some.injEq]
    constructor
    · rintro H i m' rfl w ηr hηr hp rfl
      have := (HF.sat_imp.1 (H _ w hp.1 ηr (by rcases hηr with rfl | rfl <;> simp) rfl))
        ((sat_pinHF x m w ηr 0 _ _ rfl hp.1).2 hp)
      rw [HF.Sat, pinned_deg_iff hE hηr hp, pinned_deg_iff hE hηr hp, add_zero] at this
      exact this
    · rintro H φ w hw ηr hηr rfl
      rw [HF.sat_imp, sat_pinHF x m w ηr 0 _ _ rfl hw]
      intro hp
      have hηr' : ηr = 0 ∨ ηr = 1 := by simpa using hηr
      rw [HF.Sat, pinned_deg_iff hE hηr' hp, pinned_deg_iff hE hηr' hp, add_zero]
      exact H _ m rfl w ηr hηr' hp rfl

theorem def1_E1P : Def1 S E1P :=
  ⟨typeSplit1 e1T, 0, fun t _ hV _ x _ => by
    rw [sat_typeSplit1, sat_e1T (valid_embedded hV)]⟩

/-! ## Terminal degrees -/

/-- The terminal degree clause for the (unique) exit index. -/
def T1 (t : ℕ) (y : PState S) : Prop :=
  ∀ e, ExitAt t y e → y.1.term ≠ none →
    (∀ v, RV t y (e + 2) v → deg (graph S t) v = 5) ∧
      (∀ v, RV t y (e + 1) v → deg (graph S t) v = 6)

theorem exitAt_some_iff {y : PState S} {m : Fin S.M} (h : y.1.term = some m) (e : ℤ) :
    ExitAt t y e ↔ AtCorner t y (e + 2) m := by
  unfold ExitAt
  constructor
  · rintro ⟨-, H⟩; exact H m h
  · intro H
    refine ⟨fun h' => by simp [h] at h', fun m' hm' => ?_⟩
    rw [h, Option.some.injEq] at hm'
    exact hm' ▸ H

/-- The terminal degree formula for a type. -/
noncomputable def t1T (τ : PType S) : HF (PType S) 1 0 :=
  match τ.term with
  | none => hfTrue
  | some m => bigAnd ((wordsLT S S.C).flatMap fun w => ([0, 1] : List ℤ).map fun ηt =>
      HF.imp (pinHF τ m w ηt 0)
        (HF.and (degAllHFo (cornerNbr τ m w ηt 0) 5 none)
          (degAllHFo (cornerNbr τ m w ηt (-1)) 6 none)))

theorem sat_t1T (hE : Embedded S t) (y : PState S) :
    HF.Sat stLo stHi t (t1T y.1) ![y] Fin.elim0 ↔ T1 t y := by
  unfold t1T T1
  cases h : y.1.term with
  | none => simp
  | some m =>
    simp only [exitAt_some_iff h, atCorner_iff_pin hE, sat_bigAnd, List.mem_flatMap,
      List.mem_map, mem_wordsLT, forall_exists_index, and_imp]
    constructor
    · rintro H e w ηt hηt hp he -
      have := (HF.sat_imp.1 (H _ w hp.1 ηt (by rcases hηt with rfl | rfl <;> simp) rfl))
        ((sat_pinHF y m w ηt 0 _ _ rfl hp.1).2 hp)
      rw [HF.Sat, pinned_deg_iff hE hηt hp, pinned_deg_iff hE hηt hp, add_zero] at this
      have h2 : e + 2 = 2 * (cornerY S y.1.k m w).1.eval t + ηt := he
      have h1 : e + 1 = 2 * (cornerY S y.1.k m w).1.eval t + ηt + -1 := by omega
      rw [h2, h1]
      exact this
    · rintro H φ w hw ηt hηt rfl
      rw [HF.sat_imp, sat_pinHF y m w ηt 0 _ _ rfl hw]
      intro hp
      have hηt' : ηt = 0 ∨ ηt = 1 := by simpa using hηt
      rw [HF.Sat, pinned_deg_iff hE hηt' hp, pinned_deg_iff hE hηt' hp, add_zero]
      have := H (2 * (cornerY S y.1.k m w).1.eval t + ηt - 2) w ηt hηt' hp (by ring)
        (by simp)
      rw [show 2 * (cornerY S y.1.k m w).1.eval t + ηt - 2 + 2 =
          2 * (cornerY S y.1.k m w).1.eval t + ηt by ring,
        show 2 * (cornerY S y.1.k m w).1.eval t + ηt - 2 + 1 =
          2 * (cornerY S y.1.k m w).1.eval t + ηt + -1 by ring] at this
      exact this

theorem def1_T1 : Def1 S T1 :=
  ⟨typeSplit1 t1T, 0, fun t _ hV _ x _ => by
    rw [sat_typeSplit1, sat_t1T (valid_embedded hV)]⟩

theorem pt_qT_iff (hV : Valid S t) (x y : PState S) :
    PT .qT t x y ↔ PT .q0 t x y ∨ T1 t y := by
  constructor
  · intro H
    by_cases h : PT .q0 t x y
    · exact Or.inl h
    · right
      simp only [PT, QIdx.Q, imp_false, not_forall, not_not] at h
      obtain ⟨i, e, ht, hp⟩ := h
      intro e' he'
      rw [ExitAt.unique hV he' hp.2.2.2.2]
      exact H i e ht hp
  · rintro (h | h) i e ht hp
    · exact (h i e ht hp).elim
    · exact h e hp.2.2.2.2

theorem pr_qT_iff (hV : Valid S t) (y : PState S) :
    PR .qT t y ↔ PR .q0 t y ∨ T1 t y := by
  constructor
  · intro H
    by_cases h : PR .q0 t y
    · exact Or.inl h
    · right
      simp only [PR, QIdx.Q, imp_false, not_forall, not_not] at h
      obtain ⟨i, e, hr, hp⟩ := h
      intro e' he'
      rw [ExitAt.unique hV he' hp.2.2.2.2]
      exact H i e hr hp
  · rintro (h | h) i e hr hp
    · exact (h i e hr hp).elim
    · exact h e hp.2.2.2.2

theorem def2_pt_qT : Def2 S (PT .qT) :=
  def2_congr (def2_or_snd def2_pt_q0 def1_T1) 0 fun _ _ hV _ x _ y _ => (pt_qT_iff hV x y).symm

theorem def1_pr_qT (h0 : Def1 S (PR .q0)) : Def1 S (PR .qT) :=
  def1_congr (def1_or h0 def1_T1) 0 fun _ _ hV _ y _ => (pr_qT_iff hV y).symm

end ClaudeChallenge2.State
