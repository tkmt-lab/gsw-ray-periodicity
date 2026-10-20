import Formal.Claude3SentTail

/-!
# Theorem 1a, G6: the entry point in the coordinates of the successor

Written by a Claude worker (2026-10-20, Theorem 1a, parts G6/A).

For a transition witness (exit branch `b` of `x`, word `w`), the entry point `Φ_w (q_{u+1})` has
aligned coordinates (in the direction of `y`) `(entV.1 h_x + entG.1(t), entV.2 h_x + entG.2(t))`,
with `entV` a unit vector (`entry_coords`, `entV_mem`). The entry index of a transition is the
one given by any witness (`entry_of_witness`).
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo

variable {S : Sig} {t : ℕ}

theorem rotN_smul (K : ℕ) (h a b : ℤ) :
    rotN K (h * a, h * b) = (h * (rotN K (a, b)).1, h * (rotN K (a, b)).2) := by
  induction K with
  | zero => rfl
  | succ K ih =>
    simp only [rotN, ih, rot, Prod.mk.injEq]
    constructor <;> ring

/-- The total rotation from the aligned coordinates of `x` to those of `y` along `w`. -/
def entK (τx τy : PType S) (w : List (Letter S)) : ℕ :=
  6 - (τy.k : ℕ) + (wordAff S w).J + τx.k

/-- The direction of the entry point as the height of `x` grows. -/
def entV (τx τy : PType S) (b : Bool) (w : List (Letter S)) : ℤ × ℤ :=
  rotN (entK τx τy w) ((exitBnd τx b 1).1.σ, 1)

/-- The constant part of the entry point. -/
def entG (τx τy : PType S) (b : Bool) (w : List (Letter S)) :
    ClaudeChallenge2.Aff × ClaudeChallenge2.Aff :=
  (addAff (rotAff (entK τx τy w) ((exitBnd τx b 1).1.c, constAff (exitBnd τx b 1).2)).1
      (rotAff (6 - (τy.k : ℕ)) ((wordAff S w).A, (wordAff S w).B)).1,
    addAff (rotAff (entK τx τy w) ((exitBnd τx b 1).1.c, constAff (exitBnd τx b 1).2)).2
      (rotAff (6 - (τy.k : ℕ)) ((wordAff S w).A, (wordAff S w).B)).2)

theorem entV_mem (τx τy : PType S) (b : Bool) (w : List (Letter S)) :
    entV τx τy b w ∈ unitVec := by
  refine rotN_mem_unitVec _ ?_
  rcases exitBnd_wf τx b 1 with h | h <;> rw [h] <;> simp [unitVec]

theorem entry_coords (x : PState S) (τy : PType S) (b : Bool) (hg : ExitGuard x.1 b t x.2)
    (w : List (Letter S)) :
    rotN (6 - (τy.k : ℕ)) ((wordAff S w).apply t (rp x (hiS t x + 1))) =
      ((entV x.1 τy b w).1 * x.2 + (entG x.1 τy b w).1.eval t,
        (entV x.1 τy b w).2 * x.2 + (entG x.1 τy b w).2.eval t) := by
  have h1 : hiS t x + 1 = 2 * ((exitBnd x.1 b 1).1.σ * x.2 + (exitBnd x.1 b 1).1.c.eval t) +
      (exitBnd x.1 b 1).2 := by simpa using hiS_branch x b hg 1 (by norm_num)
  have hP : rowPt x.2 (hiS t x + 1) = (x.2 * (exitBnd x.1 b 1).1.σ, x.2 * 1) +
      ((exitBnd x.1 b 1).1.c.eval t, (constAff (exitBnd x.1 b 1).2).eval t) := by
    rw [h1, rowPt_two_mul _ _ _ (exitBnd_par x.1 b 1)]
    simp only [constAff_eval, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  have h₃ := rotN_affPair (entK x.1 τy w) ((exitBnd x.1 b 1).1.c, constAff (exitBnd x.1 b 1).2) t
  have h₄ := rotN_affPair (6 - (τy.k : ℕ)) ((wordAff S w).A, (wordAff S w).B) t
  simp only at h₃ h₄
  rw [rp, AffMap.apply, rotN_add, ← rotN_add_exp, ← rotN_add_exp, hP, rotN_add, rotN_smul]
  rw [show 6 - (τy.k : ℕ) + (wordAff S w).J + x.1.k = entK x.1 τy w from rfl, h₃, h₄]
  simp only [entV, entG, entK, addAff_eval, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

theorem rp_eq_iff_rot (y : PState S) (j : ℤ) (Q : ℤ × ℤ) :
    rp y j = Q ↔ rowPt y.2 j = rotN (6 - (y.1.k : ℕ)) Q := by
  have hk : (y.1.k : ℕ) < 6 := y.1.k.isLt
  constructor
  · rintro rfl
    rw [rp, ← rotN_add_exp, show 6 - (y.1.k : ℕ) + y.1.k = 6 by omega, rotN_six]
  · intro h
    rw [rp, h, rotN_rotN_inv hk]

theorem rp_eq_entry_iff (x y : PState S) (b : Bool) (hg : ExitGuard x.1 b t x.2)
    (w : List (Letter S)) (X : ℤ) {η : ℤ} (hη : η = 0 ∨ η = 1) :
    rp y (2 * X + η) = (wordAff S w).apply t (rp x (hiS t x + 1)) ↔
      X = (entV x.1 y.1 b w).1 * x.2 + (entG x.1 y.1 b w).1.eval t ∧
        y.2 + η = (entV x.1 y.1 b w).2 * x.2 + (entG x.1 y.1 b w).2.eval t := by
  rw [rp_eq_iff_rot, entry_coords x y.1 b hg, rowPt_two_mul _ _ _ hη, Prod.mk.injEq]

/-- The entry index of a transition is that of any witness. -/
theorem entry_of_witness (hE : Embedded S t) {x y : PState S} {i : ℤ} (hT : TransAt t x y i)
    {w : List (Letter S)} (hw : w.length < S.C) (hok : WordOK S w x.1.f y.1.f)
    (hch : ∀ c ∈ wordCharts S w x.1.f, c.Mem t (rp x (hiS t x + 1))) {j : ℤ}
    (hrp : rp y j = (wordAff S w).apply t (rp x (hiS t x + 1))) : i = j := by
  obtain ⟨-, -, -, ⟨v, ⟨hz, rfl⟩, ⟨hzx, hq⟩⟩, -⟩ := hT
  obtain ⟨hzq, hzy, hq'⟩ :=
    (ident_iff_word hE x.1.f y.1.f (rp x (hiS t x + 1)) (rp y j)).2 ⟨w, hw, hok, hch, hrp⟩
  have h₁ : pt S t y.1.f (rp y i) hz = pt S t y.1.f _ hzy := hq.symm.trans hq'
  have h₂ := hE y.1.f _ _ hz hzy h₁
  exact rowPt_injective _ (rotN_inj y.1.k.isLt h₂)

end ClaudeChallenge2.State
