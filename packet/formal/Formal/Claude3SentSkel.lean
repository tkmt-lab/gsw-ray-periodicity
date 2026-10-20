import Formal.Claude3SentPred

/-!
# Theorem 1a, G6: the sentence from the atoms

Written by a Claude worker (2026-10-20, Theorem 1a, parts G6/A).

Given formulas for the atoms (`Atoms`), `pathSentence A` is the sentence
`∃ X, CondPass ∧ CondDeg ∧ CondDisj ∧ CondEnds` with every atom replaced by its formula.
`holds_pathSentence` : if the atom formulas are correct at `t` (`Atoms.OK`), the sentence holds
at `t` iff some state set satisfies `CondCore`. `geoSentence_of_atoms` :
`(∀ S, AtomsStatement S) → GeoSentenceStatement`.
-/

noncomputable section

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo R002.Claude3Fold

variable {S : Sig}

/-- Formulas for the atoms. -/
structure Atoms (S : Sig) where
  da : HF (PType S) 2 0
  db : HF (PType S) 2 0
  dc : HF (PType S) 2 0
  e1 : HF (PType S) 1 0
  pr : QIdx → HF (PType S) 1 0
  pt : QIdx → HF (PType S) 2 0

/-- The atom formulas are correct at `t` (on the states at `t`). -/
def Atoms.OK (A : Atoms S) (t : ℕ) : Prop :=
  (∀ x y, x ∈ St (stLo (S := S)) stHi t → y ∈ St (stLo (S := S)) stHi t →
      (HF.Sat stLo stHi t A.da ![x, y] Fin.elim0 ↔ DaR t x y)) ∧
    (∀ x y, x ∈ St (stLo (S := S)) stHi t → y ∈ St (stLo (S := S)) stHi t →
      (HF.Sat stLo stHi t A.db ![x, y] Fin.elim0 ↔ DbR t x y)) ∧
    (∀ x y, x ∈ St (stLo (S := S)) stHi t → y ∈ St (stLo (S := S)) stHi t →
      (HF.Sat stLo stHi t A.dc ![x, y] Fin.elim0 ↔ DcR t x y)) ∧
    (∀ x, x ∈ St (stLo (S := S)) stHi t → (HF.Sat stLo stHi t A.e1 ![x] Fin.elim0 ↔ E1P t x)) ∧
    (∀ q x, x ∈ St (stLo (S := S)) stHi t →
      (HF.Sat stLo stHi t (A.pr q) ![x] Fin.elim0 ↔ PR q t x)) ∧
    (∀ q x y, x ∈ St (stLo (S := S)) stHi t → y ∈ St (stLo (S := S)) stHi t →
      (HF.Sat stLo stHi t (A.pt q) ![x, y] Fin.elim0 ↔ PT q t x y))

/-- Formulas with one free set variable `X`. -/
abbrev FX (S : Sig) (m : ℕ) := HF (PType S) m 1

/-- `∀ x ∈ X`. -/
def allX {m : ℕ} (φ : FX S (m + 1)) : FX S m := HF.allF (HF.imp (HF.mem 0 0) φ)

/-- `∃ x ∈ X`. -/
def exX {m : ℕ} (φ : FX S (m + 1)) : FX S m := HF.exF (HF.and (HF.mem 0 0) φ)

theorem sat_allX {t m : ℕ} (φ : FX S (m + 1)) (ν : Fin m → PState S)
    (V : Fin 1 → Set (PState S)) (hX : V 0 ⊆ St stLo stHi t) :
    HF.Sat stLo stHi t (allX φ) ν V ↔ ∀ s ∈ V 0, HF.Sat stLo stHi t φ (Fin.cons s ν) V := by
  simp only [allX, HF.sat_allF, HF.sat_imp, HF.Sat, Fin.cons_zero]
  exact ⟨fun H s hs => H s (hX hs) hs, fun H s _ hs => H s hs⟩

theorem sat_exX {t m : ℕ} (φ : FX S (m + 1)) (ν : Fin m → PState S)
    (V : Fin 1 → Set (PState S)) (hX : V 0 ⊆ St stLo stHi t) :
    HF.Sat stLo stHi t (exX φ) ν V ↔ ∃ s ∈ V 0, HF.Sat stLo stHi t φ (Fin.cons s ν) V := by
  simp only [exX, HF.Sat, Fin.cons_zero]
  exact ⟨fun ⟨s, _, hs, h⟩ => ⟨s, hs, h⟩, fun ⟨s, hs, h⟩ => ⟨s, hX hs, hs, h⟩⟩

theorem sat_allX' {t m : ℕ} (φ : FX S (m + 1)) (ν : Fin m → PState S)
    (V : Fin 1 → Set (PState S)) (hX : V 0 ⊆ St stLo stHi t) :
    HF.Sat stLo stHi t (allX φ) ν V ↔ ∀ s : V 0, HF.Sat stLo stHi t φ (Fin.cons s.1 ν) V := by
  rw [sat_allX φ ν V hX, Subtype.forall]

theorem sat_exX' {t m : ℕ} (φ : FX S (m + 1)) (ν : Fin m → PState S)
    (V : Fin 1 → Set (PState S)) (hX : V 0 ⊆ St stLo stHi t) :
    HF.Sat stLo stHi t (exX φ) ν V ↔ ∃ s : V 0, HF.Sat stLo stHi t φ (Fin.cons s.1 ν) V := by
  rw [sat_exX φ ν V hX, Subtype.exists]; simp only [exists_prop]

/-- Context lookups at depth 2 and 3. -/
@[simp] theorem cons_two {α : Type} {m : ℕ} (a b c : α) (ν : Fin m → α) :
    (Fin.cons a (Fin.cons b (Fin.cons c ν)) : Fin (m + 3) → α) 2 = c := rfl

section
variable (A : Atoms S)

/-- `Trans x y`. -/
def trF {m : ℕ} (a b : Fin m) : FX S m := HF.neg (at2 (A.pt .q0) a b)

/-- Passages of `a` (entered at the root or from any state of `X`) have property `q`. -/
def passF {m : ℕ} (q : QIdx) (a : Fin m) : FX S m :=
  HF.and (at1 (A.pr q) a) (allX (at2 (A.pt q) 0 a.succ))

/-- `CondPass`. -/
def passCF : FX S 0 :=
  allX (HF.or (HF.neg (at1 (A.pr .q0) 0)) (exX (HF.neg (at2 (A.pt .q0) 0 1))))

/-- `CondDeg` (`a` is variable `1`, `b` variable `0` after the two outer quantifiers). -/
def degCF : FX S 0 :=
  exX <| exX <| bigAnd [typeHF (fun τ => τ.root ≠ none) 1, typeHF (fun τ => τ.term ≠ none) 0,
    allX (HF.imp (typeHF (fun τ => τ.root ≠ none) 0) (HF.eq 0 2)),
    allX (HF.imp (typeHF (fun τ => τ.term ≠ none) 0) (HF.eq 0 1)),
    allX (HF.imp (typeHF (fun τ => τ.term = none) 0)
      (exX (HF.and (trF A 1 0) (allX (HF.imp (trF A 2 0) (HF.eq 0 1)))))),
    allX (HF.imp (typeHF (fun τ => τ.root = none) 0)
      (exX (HF.and (trF A 0 1) (allX (HF.imp (trF A 0 2) (HF.eq 0 1))))))]

/-- `CondDisj` (in the form `DisjA`). -/
def disjCF : FX S 0 :=
  bigAnd [allX (allX (HF.imp (HF.neg (HF.eq 1 0)) (HF.imp (HF.neg (trF A 1 0))
      (HF.imp (HF.neg (trF A 0 1)) (at2 A.da 1 0))))),
    allX (allX (at2 A.db 1 0)),
    allX (allX (HF.imp (HF.neg (HF.eq 0 1)) (at2 A.dc 1 0)))]

/-- `CondEnds` (in the form `EndsA`). -/
def endsCF : FX S 0 :=
  bigAnd [allX (at1 A.e1 0), allX (passF A .qT 0),
    allX (HF.imp (typeHF (fun τ => τ.root ≠ none) 0) (typeHF (fun τ => τ.par = false) 0)),
    allX (allX (HF.imp (trF A 1 0)
      (HF.and (HF.imp (typeHF (fun τ => τ.par = true) 0) (passF A (.qP true) 1))
        (HF.imp (typeHF (fun τ => τ.par = false) 0) (passF A (.qP false) 1))))),
    allX (passF A .qE 0), allX (passF A .qL 0)]

/-- **The sentence.** -/
def pathSentence : HSentence (PType S) :=
  HF.exS (bigAnd [passCF A, degCF A, disjCF A, endsCF A])

end

section Sem
variable {A : Atoms S} {t : ℕ} (hA : A.OK t) {V : Fin 1 → Set (PState S)}
  (hX : V 0 ⊆ St stLo stHi t)
include hA hX

theorem sat_passCF (ν : Fin 0 → PState S) :
    HF.Sat stLo stHi t (passCF A) ν V ↔ ∀ y ∈ V 0, ¬ PR .q0 t y ∨ ∃ x ∈ V 0, ¬ PT .q0 t x y := by
  have hXS : ∀ x : V 0, x.1 ∈ St stLo stHi t := fun x => hX x.2
  simp only [passCF, sat_allX' _ _ _ hX, sat_exX' _ _ _ hX,
    HF.sat_or, HF.Sat, sat_at1, sat_at2, Fin.cons_zero, Fin.cons_one, hA.2.2.2.2.1 _ _ (hXS _),
    hA.2.2.2.2.2 _ _ _ (hXS _) (hXS _)]
  simp only [Subtype.forall, Subtype.exists, exists_prop]

theorem sat_degCF (ν : Fin 0 → PState S) :
    HF.Sat stLo stHi t (degCF A) ν V ↔ CondDeg t (V 0) := by
  have hXS : ∀ x : V 0, x.1 ∈ St stLo stHi t := fun x => hX x.2
  simp only [degCF, trF, bigAnd, sat_allX' _ _ _ hX, sat_exX' _ _ _ hX, HF.sat_imp,
    HF.Sat, sat_at2, sat_typeHF, sat_hfTrue, and_true, Fin.cons_zero, Fin.cons_one, cons_two,
    hA.2.2.2.2.2 _ _ _ (hXS _) (hXS _)]
  simp only [Subtype.forall, Subtype.exists, exists_prop, CondDeg, trans_iff]

theorem sat_disjCF (ν : Fin 0 → PState S) :
    HF.Sat stLo stHi t (disjCF A) ν V ↔ DisjA t (V 0) := by
  have hXS : ∀ x : V 0, x.1 ∈ St stLo stHi t := fun x => hX x.2
  simp only [disjCF, trF, bigAnd, sat_allX' _ _ _ hX, HF.sat_imp,
    HF.Sat, sat_at2, sat_hfTrue, and_true, Fin.cons_zero, Fin.cons_one,
    hA.2.2.2.2.2 _ _ _ (hXS _) (hXS _), hA.1 _ _ (hXS _) (hXS _), hA.2.1 _ _ (hXS _) (hXS _),
    hA.2.2.1 _ _ (hXS _) (hXS _)]
  simp only [Subtype.forall, DisjA, trans_iff]

theorem sat_passF {m : ℕ} (q : QIdx) (a : Fin m) (ν : Fin m → PState S)
    (ha : ν a ∈ St stLo stHi t) :
    HF.Sat stLo stHi t (passF A q a) ν V ↔ PR q t (ν a) ∧ ∀ x ∈ V 0, PT q t x (ν a) := by
  have hXS : ∀ x : V 0, x.1 ∈ St stLo stHi t := fun x => hX x.2
  simp only [passF, sat_allX' _ _ _ hX, HF.Sat, sat_at1, sat_at2, Fin.cons_zero, Fin.cons_succ,
    hA.2.2.2.2.1 _ _ ha, hA.2.2.2.2.2 _ _ _ (hXS _) ha, Subtype.forall]

theorem sat_passF0 {m : ℕ} (q : QIdx) (s : V 0) (ν : Fin m → PState S) :
    HF.Sat stLo stHi t (passF A q 0) (Fin.cons s.1 ν) V ↔ PR q t s.1 ∧ ∀ x ∈ V 0, PT q t x s.1 :=
  sat_passF hA hX q 0 _ (hX s.2)

theorem sat_passF1 {m : ℕ} (q : QIdx) (s' : PState S) (s : V 0) (ν : Fin m → PState S) :
    HF.Sat stLo stHi t (passF A q 1) (Fin.cons s' (Fin.cons s.1 ν)) V ↔
      PR q t s.1 ∧ ∀ x ∈ V 0, PT q t x s.1 :=
  sat_passF hA hX q 1 _ (hX s.2)

theorem sat_endsCF (ν : Fin 0 → PState S) :
    HF.Sat stLo stHi t (endsCF A) ν V ↔ EndsA t (V 0) := by
  have hXS : ∀ x : V 0, x.1 ∈ St stLo stHi t := fun x => hX x.2
  simp only [endsCF, trF, bigAnd, sat_allX' _ _ _ hX, HF.sat_imp,
    HF.Sat, sat_at1, sat_at2, sat_typeHF, sat_hfTrue, and_true, Fin.cons_zero, Fin.cons_one,
    hA.2.2.2.2.2 _ _ _ (hXS _) (hXS _), hA.2.2.2.1 _ (hXS _), sat_passF0 hA hX, sat_passF1 hA hX]
  simp only [Subtype.forall, EndsA, trans_iff]

end Sem

/-- **The sentence is correct** when the atom formulas are. -/
theorem holds_pathSentence {A : Atoms S} {t : ℕ} (hA : A.OK t) :
    Holds stLo stHi t (pathSentence A) ↔ ∃ X ⊆ St (stLo (S := S)) stHi t, CondCore t X := by
  unfold Holds pathSentence
  simp only [HF.Sat, bigAnd, sat_hfTrue, and_true]
  refine exists_congr fun X => and_congr_right fun hX => ?_
  have hX' : (Fin.cons X (fun i => i.elim0) : Fin 1 → Set (PState S)) 0 ⊆ St stLo stHi t := hX
  rw [sat_passCF hA hX', sat_degCF hA hX', sat_disjCF hA hX', sat_endsCF hA hX']
  simp only [Fin.cons_zero]
  rw [CondCore, condPass_iff, condDisj_iff, condEnds_iff]

/-- **G6 from the atoms.** -/
theorem geoSentence_of_atoms (hAt : ∀ S : Sig, AtomsStatement S) : GeoSentenceStatement := by
  intro S
  obtain ⟨⟨da, ta, hda⟩, ⟨db, tb, hdb⟩, ⟨dc, tc, hdc⟩, ⟨e1, te, he1⟩, hq⟩ := hAt S
  choose hq1 hq2 using hq
  choose pr tpr hpr using hq1
  choose pt tpt hpt using hq2
  let A : Atoms S := ⟨da, db, dc, e1, pr, pt⟩
  have hle : ∀ q, tpr q + tpt q ≤ ∑ q, (tpr q + tpt q) := fun q =>
    Finset.single_le_sum (f := fun q => tpr q + tpt q) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ q)
  refine ⟨pathSentence A, ta + tb + tc + te + ∑ q, (tpr q + tpt q),
    fun t ht hV hTC => (holds_pathSentence ?_).symm⟩
  refine ⟨fun x y hx hy => hda t (by omega) hV hTC x hx y hy,
    fun x y hx hy => hdb t (by omega) hV hTC x hx y hy,
    fun x y hx hy => hdc t (by omega) hV hTC x hx y hy,
    fun x hx => he1 t (by omega) hV hTC x hx,
    fun q x hx => hpr q t (by have := hle q; omega) hV hTC x hx,
    fun q x y hx hy => hpt q t (by have := hle q; omega) hV hTC x hx y hy⟩

end ClaudeChallenge2.State
