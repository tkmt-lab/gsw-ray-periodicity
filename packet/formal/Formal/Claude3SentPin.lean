import Formal.Claude3SentTransHF

/-!
# Theorem 1a, G6: corners pin indices (one-state formulas)

Written by a Claude worker (2026-10-20, Theorem 1a, parts G6/A).

* `PinOK`, `atCorner_iff_pin` : a marked corner on the row of `y` at index `j` is given by a
  word `w` and a parity `ηc` (`PinOK`: word, chain charts, height `h + ηc = H_c(t)`), with
  `j = 2 X_c(t) + ηc`.
* `pinHF`, `sat_pinHF` : `PinOK` as a formula in the height of one variable.
* `bndLeHF`, `leBndHF` : `σ h + c(t) ≤ X(t)` and `X(t) ≤ σ h + c(t)` for `σ ∈ {0, -1}`.
* `loLeHF`, `leHiHF` : `lo ≤ 2 X(t) + η` and `2 X(t) + η ≤ hi` (affine `X`).
* `ifHF` : a constant proposition.
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo
open R002.Claude3Fold (HF)

variable {S : Sig} {t : ℕ}

/-- The corner `m` is pinned on the row of `y` by the word `w` with parity `ηc`. -/
def PinOK (t : ℕ) (y : PState S) (m : Fin S.M) (w : List (Letter S)) (ηc : ℤ) : Prop :=
  w.length < S.C ∧ WordOK S w (S.mchart m) y.1.f ∧
    (∀ c ∈ wordCharts S w (S.mchart m), c.Mem t ((S.mx m).eval t, (S.my m).eval t)) ∧
      y.2 + ηc = (cornerY S y.1.k m w).2.eval t

theorem atCorner_iff_pin (hE : Embedded S t) (y : PState S) (j : ℤ) (m : Fin S.M) :
    AtCorner t y j m ↔ ∃ w ηc, (ηc = 0 ∨ ηc = 1) ∧ PinOK t y m w ηc ∧
      j = 2 * (cornerY S y.1.k m w).1.eval t + ηc := by
  rw [atCorner_iff_word hE]
  constructor
  · rintro ⟨w, hw, hok, hch, he⟩
    obtain ⟨ηc, hηc, hj, hh⟩ := (rp_eq_corner_iff y m w j).1 he
    exact ⟨w, ηc, hηc, ⟨hw, hok, hch, hh⟩, hj⟩
  · rintro ⟨w, ηc, hηc, ⟨hw, hok, hch, hh⟩, hj⟩
    exact ⟨w, hw, hok, hch, (rp_eq_corner_iff y m w j).2 ⟨ηc, hηc, hj, hh⟩⟩

/-- `PinOK` as a formula (without the length condition, which comes from the word list). -/
noncomputable def pinHF {n k : ℕ} (τ : PType S) (m : Fin S.M) (w : List (Letter S)) (ηc : ℤ)
    (v : Fin n) : HF (PType S) n k :=
  if WordOK S w (S.mchart m) τ.f then
    bigAnd [chainHF (wordCharts S w (S.mchart m)) (S.mx m, S.my m),
      HF.le v ⟨(cornerY S τ.k m w).2.a, (cornerY S τ.k m w).2.b - ηc⟩,
      HF.nle v ⟨-(cornerY S τ.k m w).2.a, -(cornerY S τ.k m w).2.b + ηc⟩]
  else hfFalse

theorem sat_pinHF {lo hi : PType S → R002.Claude3Fold.Aff} {n k : ℕ} (y : PState S)
    (m : Fin S.M) (w : List (Letter S)) (ηc : ℤ) (v : Fin n) (ν : Fin n → PState S)
    (V : Fin k → Set (PState S)) (hv : ν v = y) (hw : w.length < S.C) :
    HF.Sat lo hi t (pinHF y.1 m w ηc v) ν V ↔ PinOK t y m w ηc := by
  subst hv
  simp only [pinHF, sat_ite_false, sat_bigAnd, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, sat_chainHF, HF.Sat, R002.Claude3Fold.Aff.eval, PinOK, hw,
    true_and, ClaudeChallenge2.Aff.eval]
  constructor
  · rintro ⟨hok, hch, h1, h2⟩
    exact ⟨hok, hch, by linarith⟩
  · rintro ⟨hok, hch, h⟩
    exact ⟨hok, hch, by linarith, by linarith⟩

/-! ## Bounds against affine positions -/

/-- `σ h + c(t) ≤ X(t)` (for `σ ∈ {0, -1}`). -/
def bndLeHF {n k : ℕ} (b : Bnd) (X : ClaudeChallenge2.Aff) (v : Fin n) : HF (PType S) n k :=
  if b.σ = 0 then HF.tNonneg (fsub X b.c) else HF.nle v (fsub X b.c)

theorem sat_bndLeHF {lo hi : PType S → R002.Claude3Fold.Aff} {n k : ℕ} {b : Bnd} (hb : b.WF)
    (X : ClaudeChallenge2.Aff) (v : Fin n) (ν : Fin n → PState S) (V : Fin k → Set (PState S)) :
    HF.Sat lo hi t (bndLeHF b X v) ν V ↔ b.σ * (ν v).2 + b.c.eval t ≤ X.eval t := by
  rcases hb with h | h <;> simp only [bndLeHF, h, ↓reduceIte, HF.Sat, fsub_eval,
    show (-1 : ℤ) ≠ 0 by norm_num] <;> constructor <;> intro H <;> linarith

/-- `X(t) ≤ σ h + c(t)` (for `σ ∈ {0, -1}`). -/
def leBndHF {n k : ℕ} (b : Bnd) (X : ClaudeChallenge2.Aff) (v : Fin n) : HF (PType S) n k :=
  if b.σ = 0 then HF.tNonneg (fsub b.c X) else HF.le v (fsub b.c X)

theorem sat_leBndHF {lo hi : PType S → R002.Claude3Fold.Aff} {n k : ℕ} {b : Bnd} (hb : b.WF)
    (X : ClaudeChallenge2.Aff) (v : Fin n) (ν : Fin n → PState S) (V : Fin k → Set (PState S)) :
    HF.Sat lo hi t (leBndHF b X v) ν V ↔ X.eval t ≤ b.σ * (ν v).2 + b.c.eval t := by
  rcases hb with h | h <;> simp only [leBndHF, h, ↓reduceIte, HF.Sat, fsub_eval,
    show (-1 : ℤ) ≠ 0 by norm_num] <;> constructor <;> intro H <;> linarith

/-- `lo ≤ 2 X(t) + η` for the state at `v` of type `τ`. -/
def loLeHF {n k : ℕ} (τ : PType S) (η : ℤ) (X : ClaudeChallenge2.Aff) (v : Fin n) :
    HF (PType S) n k :=
  bigAnd ((lowsY τ η).map fun b => bndLeHF b X v)

theorem sat_loLeHF {lo hi : PType S → R002.Claude3Fold.Aff} {n k : ℕ} (y : PState S) {η : ℤ}
    (hη : η = 0 ∨ η = 1) (X : ClaudeChallenge2.Aff) (v : Fin n) (ν : Fin n → PState S)
    (V : Fin k → Set (PState S)) (hv : ν v = y) :
    HF.Sat lo hi t (loLeHF y.1 η X v) ν V ↔ loS t y ≤ 2 * X.eval t + η := by
  subst hv
  rw [lo_le_iff _ hη, loLeHF, sat_bigAnd]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact forall₂_congr fun b hb => sat_bndLeHF (lowsY_wf _ _ b hb) X v ν V

/-- `2 X(t) + η ≤ hi` for the state at `v` of type `τ`. -/
def leHiHF {n k : ℕ} (τ : PType S) (η : ℤ) (X : ClaudeChallenge2.Aff) (v : Fin n) :
    HF (PType S) n k :=
  bigAnd ((upsY τ η).map fun b => leBndHF b X v)

theorem sat_leHiHF {lo hi : PType S → R002.Claude3Fold.Aff} {n k : ℕ} (y : PState S) {η : ℤ}
    (hη : η = 0 ∨ η = 1) (X : ClaudeChallenge2.Aff) (v : Fin n) (ν : Fin n → PState S)
    (V : Fin k → Set (PState S)) (hv : ν v = y) :
    HF.Sat lo hi t (leHiHF y.1 η X v) ν V ↔ 2 * X.eval t + η ≤ hiS t y := by
  subst hv
  rw [le_hi_iff _ hη, leHiHF, sat_bigAnd]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact forall₂_congr fun b hb => sat_leBndHF (upsY_wf _ _ b hb) X v ν V

open Classical in
/-- A constant proposition. -/
noncomputable def ifHF {n k : ℕ} (p : Prop) : HF (PType S) n k := if p then hfTrue else hfFalse

theorem sat_ifHF {lo hi : PType S → R002.Claude3Fold.Aff} {n k : ℕ} (p : Prop)
    (ν : Fin n → PState S) (V : Fin k → Set (PState S)) :
    HF.Sat lo hi t (ifHF (S := S) p) ν V ↔ p := by
  classical
  by_cases hp : p <;> simp [ifHF, hp]

/-- `0 ≤ A(t)`. -/
theorem sat_tNonneg_toF {lo hi : PType S → R002.Claude3Fold.Aff} {n k : ℕ}
    (A : ClaudeChallenge2.Aff) (ν : Fin n → PState S) (V : Fin k → Set (PState S)) :
    HF.Sat lo hi t (HF.tNonneg (toFAff A)) ν V ↔ 0 ≤ A.eval t := Iff.rfl

end ClaudeChallenge2.State
