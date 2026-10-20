import Formal.Claude3SentPred
import Formal.Claude3IdentRow

/-!
# Theorem 1a, G6: row descriptors of the passages

Written by a Claude worker (2026-10-20, Theorem 1a, parts G6/A).

* `exitBnd`, `ExitGuard`, `hiS_branch`, `exitRow_at` : the last triangle index `u = hiS` of a
  state is `2 (U_x - 1) + 1` (when `h ≤ U_s - U_x - 1`) or `2 (U_s - h - 1)` (otherwise), so the
  exit points `rp σ (u + k)`, `k = 0, 1, 2`, are single-point rows `rowPtPt` with well-formed
  bounds.
* `lowsY`, `upsY`, `lo_le_iff`, `le_hi_iff` : `lo ≤ 2 X + η ≤ hi` as own-height bounds on `X`.
* `dS`, `rp_shift` : the row walk advances by a translation depending only on the parity.
* `affApply`, `cornerY`, `rp_eq_corner_iff`, `atCorner_iff_word` : a marked corner on a row is
  pinned (index and height) by a word, with explicit affine data.
* `nbrRow_at'` : the neighbour row through the points of the base row.
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo

variable {S : Sig} {t : ℕ}

/-- `A + c`. -/
def affAdd (A : ClaudeChallenge2.Aff) (c : ℤ) : ClaudeChallenge2.Aff := ⟨A.a, A.b + c⟩

@[simp] theorem affAdd_eval (A : ClaudeChallenge2.Aff) (c : ℤ) (t : ℕ) :
    (affAdd A c).eval t = A.eval t + c := by
  simp only [affAdd, ClaudeChallenge2.Aff.eval]; ring

/-! ## Exit points -/

/-- The bound and parity of the exit point `u + k` in branch `b`. -/
def exitBnd (τ : PType S) : Bool → ℕ → Bnd × ℤ
  | false, 0 => (⟨0, affAdd (rc τ).ux (-1)⟩, 1)
  | false, 1 => (⟨0, (rc τ).ux⟩, 0)
  | false, _ => (⟨0, (rc τ).ux⟩, 1)
  | true, 0 => (⟨-1, affAdd (rc τ).us (-1)⟩, 0)
  | true, 1 => (⟨-1, affAdd (rc τ).us (-1)⟩, 1)
  | true, _ => (⟨-1, (rc τ).us⟩, 0)

/-- The exit branch: `true` iff `U_s - U_x ≤ h`. -/
def ExitGuard (τ : PType S) (b : Bool) (t : ℕ) (h : ℤ) : Prop :=
  if b then (rc τ).us.eval t - (rc τ).ux.eval t ≤ h else h ≤ (rc τ).us.eval t - (rc τ).ux.eval t - 1

theorem exitGuard_exists (τ : PType S) (t : ℕ) (h : ℤ) : ∃ b, ExitGuard τ b t h := by
  by_cases hc : (rc τ).us.eval t - (rc τ).ux.eval t ≤ h
  · exact ⟨true, by simpa [ExitGuard] using hc⟩
  · exact ⟨false, by simp only [ExitGuard]; simp only [Bool.false_eq_true, ↓reduceIte]; omega⟩

theorem exitBnd_wf (τ : PType S) (b : Bool) (k : ℕ) : (exitBnd τ b k).1.WF := by
  rcases b with _ | _ <;> rcases k with _ | _ | _ <;> simp [exitBnd, Bnd.WF]

theorem exitBnd_par (τ : PType S) (b : Bool) (k : ℕ) :
    (exitBnd τ b k).2 = 0 ∨ (exitBnd τ b k).2 = 1 := by
  rcases b with _ | _ <;> rcases k with _ | _ | _ <;> simp [exitBnd]

theorem hiS_branch (σ : PState S) (b : Bool) (hg : ExitGuard σ.1 b t σ.2) (k : ℕ) (hk : k ≤ 2) :
    hiS t σ + k = 2 * ((exitBnd σ.1 b k).1.σ * σ.2 + (exitBnd σ.1 b k).1.c.eval t) +
      (exitBnd σ.1 b k).2 := by
  simp only [hiS, hi, eps, Be, Bo, min_def]
  rcases b with _ | _ <;> rcases k with _ | _ | _ | k <;>
    simp only [ExitGuard, exitBnd, Bool.false_eq_true, ↓reduceIte, affAdd_eval] at hg ⊢ <;>
    split_ifs <;> omega

/-- The exit point `rp σ (u + k)` as a single-point row. -/
def exitRow (τ : PType S) (b : Bool) (k : ℕ) : RowSet S :=
  rowPtPt τ.f τ.k (exitBnd τ b k).2 (exitBnd τ b k).1

theorem exitRow_wf (τ : PType S) (b : Bool) (k : ℕ) : (exitRow τ b k).WF :=
  rowPtPt_wf _ _ _ (exitBnd_wf τ b k)

theorem exitRow_at (σ : PState S) (b : Bool) (hg : ExitGuard σ.1 b t σ.2) (k : ℕ) (hk : k ≤ 2)
    (z : ℤ × ℤ) : (exitRow σ.1 b k).At t σ.2 z ↔ z = rp σ (hiS t σ + k) := by
  rw [exitRow, rowPtPt_at _ _ (exitBnd_par σ.1 b k), hiS_branch σ b hg k hk]
  rfl

theorem exitRow_at0 (σ : PState S) (b : Bool) (hg : ExitGuard σ.1 b t σ.2) (z : ℤ × ℤ) :
    (exitRow σ.1 b 0).At t σ.2 z ↔ z = rp σ (hiS t σ) := by
  simpa using exitRow_at σ b hg 0 (by norm_num) z

theorem exitRow_at1 (σ : PState S) (b : Bool) (hg : ExitGuard σ.1 b t σ.2) (z : ℤ × ℤ) :
    (exitRow σ.1 b 1).At t σ.2 z ↔ z = rp σ (hiS t σ + 1) := by
  simpa using exitRow_at σ b hg 1 (by norm_num) z

theorem exitRow_at2 (σ : PState S) (b : Bool) (hg : ExitGuard σ.1 b t σ.2) (z : ℤ × ℤ) :
    (exitRow σ.1 b 2).At t σ.2 z ↔ z = rp σ (hiS t σ + 2) := by
  simpa using exitRow_at σ b hg 2 (by norm_num) z

/-! ## Passage ranges -/

/-- Lower bounds of `X` for `lo ≤ 2 X + η`. -/
def lowsY (τ : PType S) (η : ℤ) : List Bnd :=
  [⟨0, (rc τ).lx⟩, ⟨-1, affAdd (rc τ).ls (-η)⟩]

/-- Upper bounds of `X` for `2 X + η ≤ hi`. -/
def upsY (τ : PType S) (η : ℤ) : List Bnd :=
  [⟨0, affAdd (rc τ).ux (-1)⟩, ⟨-1, affAdd (rc τ).us (-1 - η)⟩]

theorem lowsY_wf (τ : PType S) (η : ℤ) : ∀ b ∈ lowsY τ η, b.WF := by
  simp [lowsY, Bnd.WF]

theorem upsY_wf (τ : PType S) (η : ℤ) : ∀ b ∈ upsY τ η, b.WF := by
  simp [upsY, Bnd.WF]

theorem lo_le_iff (σ : PState S) {η : ℤ} (hη : η = 0 ∨ η = 1) (X : ℤ) :
    loS t σ ≤ 2 * X + η ↔ ∀ b ∈ lowsY σ.1 η, b.σ * σ.2 + b.c.eval t ≤ X := by
  simp only [loS, lo, delta, Ae, Ao, lowsY, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, affAdd_eval, max_def]
  split_ifs <;> constructor <;> intro H <;> omega

theorem le_hi_iff (σ : PState S) {η : ℤ} (_hη : η = 0 ∨ η = 1) (X : ℤ) :
    2 * X + η ≤ hiS t σ ↔ ∀ b ∈ upsY σ.1 η, X ≤ b.σ * σ.2 + b.c.eval t := by
  simp only [hiS, hi, eps, Be, Bo, upsY, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, affAdd_eval, min_def]
  split_ifs <;> constructor <;> intro H <;> omega

/-! ## Shifts along the row walk -/

/-- The step of the row walk from an index of parity `η` by `n`. -/
def dS (η n : ℤ) : ℤ × ℤ := rowPt 0 (η + n) - rowPt 0 η

theorem rowPt_shift (h X η n : ℤ) (_hη : η = 0 ∨ η = 1) :
    rowPt h (2 * X + η + n) = rowPt h (2 * X + η) + dS η n := by
  simp only [rowPt, dS, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.mk.injEq]
  constructor <;> omega

theorem rp_shift (σ : PState S) (X η n : ℤ) (hη : η = 0 ∨ η = 1) :
    rp σ (2 * X + η + n) = rp σ (2 * X + η) + rotN σ.1.k (dS η n) := by
  rw [rp, rowPt_shift _ _ _ _ hη, rotN_add]; rfl

/-! ## Marked corners on a row -/

/-- An affine map applied to a point with affine coordinates. -/
def affApply (φ : AffMap) (p : ClaudeChallenge2.Aff × ClaudeChallenge2.Aff) :
    ClaudeChallenge2.Aff × ClaudeChallenge2.Aff :=
  (addAff (rotAff φ.J p).1 φ.A, addAff (rotAff φ.J p).2 φ.B)

theorem affApply_eval (φ : AffMap) (p : ClaudeChallenge2.Aff × ClaudeChallenge2.Aff) (t : ℕ) :
    φ.apply t (p.1.eval t, p.2.eval t) = ((affApply φ p).1.eval t, (affApply φ p).2.eval t) := by
  simp only [AffMap.apply, rotN_affPair, affApply, addAff_eval, Prod.mk_add_mk]

/-- The corner `m` carried by word `w`, in the aligned coordinates `(position, height)` of
direction `k`. -/
def cornerY (S : Sig) (k : ℕ) (m : Fin S.M) (w : List (Letter S)) :
    ClaudeChallenge2.Aff × ClaudeChallenge2.Aff :=
  rotAff (6 - k) (affApply (wordAff S w) (S.mx m, S.my m))

theorem rotN_inj {k : ℕ} (hk : k < 6) {z z' : ℤ × ℤ} (h : rotN k z = rotN k z') : z = z' := by
  have : rotN (6 - k) (rotN k z) = rotN (6 - k) (rotN k z') := by rw [h]
  rwa [← rotN_add_exp, show 6 - k + k = 6 by omega, rotN_six, ← rotN_add_exp,
    show 6 - k + k = 6 by omega, rotN_six] at this

theorem rp_eq_corner_iff (σ : PState S) (m : Fin S.M) (w : List (Letter S)) (j : ℤ) :
    rp σ j = (wordAff S w).apply t ((S.mx m).eval t, (S.my m).eval t) ↔
      ∃ ηc : ℤ, (ηc = 0 ∨ ηc = 1) ∧ j = 2 * (cornerY S σ.1.k m w).1.eval t + ηc ∧
        σ.2 + ηc = (cornerY S σ.1.k m w).2.eval t := by
  have hk : (σ.1.k : ℕ) < 6 := σ.1.k.isLt
  have key : (wordAff S w).apply t ((S.mx m).eval t, (S.my m).eval t) =
      rotN σ.1.k ((cornerY S σ.1.k m w).1.eval t, (cornerY S σ.1.k m w).2.eval t) := by
    rw [cornerY, ← rotN_affPair, ← rotN_add_exp, show (σ.1.k : ℕ) + (6 - σ.1.k) = 6 by omega,
      rotN_six]
    exact affApply_eval _ (S.mx m, S.my m) t
  rw [key, rp]
  constructor
  · intro h
    have h' := rotN_inj hk h
    simp only [rowPt, Prod.mk.injEq] at h'
    exact ⟨j % 2, by omega, by omega, by omega⟩
  · rintro ⟨ηc, hηc, rfl, he⟩
    congr 1
    rw [rowPt_two_mul _ _ _ hηc, he]

theorem atCorner_iff_word (hE : Embedded S t) (σ : PState S) (j : ℤ) (m : Fin S.M) :
    AtCorner t σ j m ↔ ∃ w : List (Letter S), w.length < S.C ∧ WordOK S w (S.mchart m) σ.1.f ∧
      (∀ c ∈ wordCharts S w (S.mchart m), c.Mem t ((S.mx m).eval t, (S.my m).eval t)) ∧
        rp σ j = (wordAff S w).apply t ((S.mx m).eval t, (S.my m).eval t) := by
  rw [← ident_iff_word hE]
  constructor
  · rintro ⟨v, ⟨hz, rfl⟩, ⟨hm, hv⟩⟩
    exact ⟨hm, hz, hv⟩
  · rintro ⟨hm, hz, hv⟩
    exact ⟨_, ⟨hz, rfl⟩, ⟨hm, hv⟩⟩

/-! ## Neighbour rows through points -/

theorem nbrRow_at' (R : RowSet S) (g : Fin S.C) (w : List (Letter S)) (u : ℤ × ℤ) (h : ℤ)
    (z : ℤ × ℤ) :
    (nbrRow R g w u).At t h z ↔ ∃ p, R.At t h p ∧ (∀ ch ∈ wordCharts S w R.f, ch.Mem t p) ∧
      z = (wordAff S w).apply t p + u := by
  rw [nbrRow_at]
  constructor
  · rintro ⟨x, hc, hch, rfl⟩
    exact ⟨_, ⟨x, hc, rfl⟩, hch, rfl⟩
  · rintro ⟨p, ⟨x, hc, rfl⟩, hch, rfl⟩
    exact ⟨x, hc, hch, rfl⟩

end ClaudeChallenge2.State
