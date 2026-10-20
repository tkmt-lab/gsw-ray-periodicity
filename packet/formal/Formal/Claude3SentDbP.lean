import Formal.Claude3SentDbNP

/-!
# Theorem 1a, G6: condition 3 (b), the parallel case

Written by a Claude worker (2026-10-20, Theorem 1a, parts G6/A).

If the entry point moves along the rows of `y` (`entV.2 = 0`), the height of `y` is fixed
(`h_y = entG.2 - η`) and only the start of the output moves with `h_x`. The output points are
encoded by an auxiliary state `z` of type `τz` (chart of `y`, direction `k_y + 5`), whose
height is the position along the row (`rp_rot5`): a point `rotN k_z (-H, h_z)` (`affA`), or
`rotN k_z (-H, h_z + 1)` at the upper end (`affB`), or, if the chart has one row in direction
`k_z`, a fixed point (`cstC`). `meetY_p` : the output meets a row iff one of the three holds.
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo

variable {S : Sig} {t : ℕ}

/-- The auxiliary type. -/
def τz (τ : PType S) : PType S := ⟨τ.f, τ.k + 5, none, none, false⟩

theorem rp_rot5 (y : PState S) (X' : ℤ) {η' : ℤ} (hη' : η' = 0 ∨ η' = 1) :
    rp y (2 * X' + η') = rotN (τz y.1).k (-(y.2 + η'), X' + (y.2 + η')) := by
  have hk : (y.1.k : ℕ) < 6 := y.1.k.isLt
  have h1 : rotN (τz y.1).k (-(y.2 + η'), X' + (y.2 + η')) =
      rotN ((τz y.1).k + 1) (X', y.2 + η') := by
    rw [rotN_add_exp]; rfl
  rw [h1, rp, rowPt_two_mul _ _ _ hη', rotN_mod ((τz y.1).k + 1), rotN_mod (y.1.k : ℕ)]
  congr 1
  simp only [τz, Fin.val_add]
  omega

/-- The row height `H = h_y + η'` as an affine function (in the parallel case). -/
def pH (τx τy : PType S) (b : Bool) (w : List (Letter S)) (η η' : ℤ) : ClaudeChallenge2.Aff :=
  affAdd (entG τx τy b w).2 (η' - η)

/-- Output point at aux height `h` (`X' = h - H`). -/
def affA (τx τy : PType S) (b : Bool) (w : List (Letter S)) (η η' : ℤ) : RowSet S :=
  affineRow τy.f (τz τy).k zeroAff zeroAff ⟨0, negAff (pH τx τy b w η η')⟩

/-- Output point at aux height `h` (`X' = h + 1 - H`). -/
def affB (τx τy : PType S) (b : Bool) (w : List (Letter S)) (η η' : ℤ) : RowSet S :=
  affineRow τy.f (τz τy).k (constAff (rotN (τz τy).k (0, 1)).1)
    (constAff (rotN (τz τy).k (0, 1)).2) ⟨0, negAff (pH τx τy b w η η')⟩

/-- The output point at the bottom row of direction `k_z` (`X' = L - H`). -/
def cstC (τx τy : PType S) (b : Bool) (w : List (Letter S)) (η η' : ℤ) : RowSet S :=
  constRow τy.f (rotAff (τz τy).k (negAff (pH τx τy b w η η'), (rc (τz τy)).ly)).1
    (rotAff (τz τy).k (negAff (pH τx τy b w η η'), (rc (τz τy)).ly)).2

/-- The range condition of an output position `X'`. -/
def PCond (t : ℕ) (x y : PState S) (b : Bool) (w : List (Letter S)) (η η' : ℤ) (ed' : ED S)
    (X' : ℤ) : Prop :=
  (entV x.1 y.1 b w).1 * x.2 + (entG x.1 y.1 b w).1.eval t + (η - η' + 3) / 2 ≤ X' ∧
    ∀ b' ∈ edUps y.1 η' ed', X' ≤ b'.σ * y.2 + b'.c.eval t

theorem meetY_p {x y : PState S} {b : Bool} {w : List (Letter S)} {η : ℤ}
    (hh : y.2 + η = (entG x.1 y.1 b w).2.eval t)
    (ed' : ED S) {η' : ℤ} (hη' : η' = 0 ∨ η' = 1) (R : RowSet S) (h : ℤ) :
    MeetY t y (entI t x y b w η) ed' η' R h ↔
      (∃ hz, RowsIn t ((τz y.1), hz) ∧ PCond t x y b w η η' ed'
          (hz - (pH x.1 y.1 b w η η').eval t) ∧ Meet S t (affA x.1 y.1 b w η η') hz R h) ∨
      (∃ hz, RowsIn t ((τz y.1), hz) ∧ PCond t x y b w η η' ed'
          (hz + 1 - (pH x.1 y.1 b w η η').eval t) ∧ Meet S t (affB x.1 y.1 b w η η') hz R h) ∨
      (PCond t x y b w η η' ed' ((rc (τz y.1)).ly.eval t - (pH x.1 y.1 b w η η').eval t) ∧
        Meet S t (cstC x.1 y.1 b w η η') 0 R h) := by
  have hH : (pH x.1 y.1 b w η η').eval t = y.2 + η' := by
    simp only [pH, affAdd_eval]; omega
  -- the output points by their position
  have hY : ∀ z, YOut t y (entI t x y b w η) ed' η' z ↔ ∃ X', PCond t x y b w η η' ed' X' ∧
      z = rotN (τz y.1).k (-(pH x.1 y.1 b w η η').eval t, X' + (pH x.1 y.1 b w η η').eval t) := by
    intro z
    simp only [YOut, PCond, entI, hH, ← rp_rot5 y _ hη']
    refine exists_congr fun X' => ?_
    constructor
    · rintro ⟨h₁, h₂, rfl⟩; exact ⟨⟨by omega, h₂⟩, rfl⟩
    · rintro ⟨⟨h₁, h₂⟩, rfl⟩; exact ⟨by omega, h₂, rfl⟩
  have hA : ∀ hz z, (affA x.1 y.1 b w η η').At t hz z ↔
      z = rotN (τz y.1).k (-(pH x.1 y.1 b w η η').eval t, hz) := by
    intro hz z
    rw [affA, affineRow_at]
    simp only [zero_mul, zero_add, negAff_eval, zeroAff_eval, Prod.mk_zero_zero, add_zero]
  have hB : ∀ hz z, (affB x.1 y.1 b w η η').At t hz z ↔
      z = rotN (τz y.1).k (-(pH x.1 y.1 b w η η').eval t, hz + 1) := by
    intro hz z
    rw [affB, affineRow_at, show ((-(pH x.1 y.1 b w η η').eval t, hz + 1) : ℤ × ℤ) =
      (-(pH x.1 y.1 b w η η').eval t, hz) + (0, 1) by simp, rotN_add]
    simp
  have hC : ∀ z, (cstC x.1 y.1 b w η η').At t 0 z ↔
      z = rotN (τz y.1).k (-(pH x.1 y.1 b w η η').eval t, (rc (τz y.1)).ly.eval t) := by
    intro z
    rw [cstC, constRow_at, ← rotN_affPair]
    simp
  have hmem : ∀ p, (S.chart y.1.f).Mem t (rotN (τz y.1).k p) ↔ (rc (τz y.1)).Mem t p :=
    fun p => mem_rotN_iff _ _ _ _
  constructor
  · rintro ⟨z₁, z₂, hY₁, hA₂, hz₁, hz₂, hq⟩
    obtain ⟨X', hc, rfl⟩ := (hY _).1 hY₁
    have hm := (hmem _).1 hz₁
    simp only [Chart.Mem] at hm
    obtain ⟨-, -, hL, hU, -, -⟩ := hm
    set H := (pH x.1 y.1 b w η η').eval t
    by_cases h₁ : X' + H + 1 ≤ (rc (τz y.1)).uy.eval t
    · refine Or.inl ⟨X' + H, ⟨hL, h₁⟩, by rwa [add_sub_cancel_right], _, z₂,
        (hA _ _).2 rfl, hA₂, hz₁, hz₂, hq⟩
    · by_cases h₂ : (rc (τz y.1)).ly.eval t ≤ (rc (τz y.1)).uy.eval t - 1
      · refine Or.inr (Or.inl ⟨X' + H - 1, ⟨(by omega : (rc (τz y.1)).ly.eval t ≤ X' + H - 1),
          (by omega : X' + H - 1 + 1 ≤ (rc (τz y.1)).uy.eval t)⟩, by
          rwa [show X' + H - 1 + 1 - H = X' by ring], _, z₂,
          (hB _ _).2 (by rw [sub_add_cancel]), hA₂, hz₁, hz₂, hq⟩)
      · have hX : X' = (rc (τz y.1)).ly.eval t - H := by omega
        refine Or.inr (Or.inr ⟨hX ▸ hc, _, z₂, (hC _).2 (by rw [hX, sub_add_cancel]), hA₂, hz₁,
          hz₂, hq⟩)
  · rintro (⟨hz, -, hc, z₁, z₂, h₁, h₂, hz₁, hz₂, hq⟩ | ⟨hz, -, hc, z₁, z₂, h₁, h₂, hz₁, hz₂, hq⟩ |
      ⟨hc, z₁, z₂, h₁, h₂, hz₁, hz₂, hq⟩)
    · rw [hA] at h₁
      exact ⟨z₁, z₂, (hY _).2 ⟨_, hc, by rw [h₁, sub_add_cancel]⟩, h₂, hz₁, hz₂, hq⟩
    · rw [hB] at h₁
      exact ⟨z₁, z₂, (hY _).2 ⟨_, hc, by rw [h₁]; ring_nf⟩, h₂, hz₁, hz₂, hq⟩
    · rw [hC] at h₁
      exact ⟨z₁, z₂, (hY _).2 ⟨_, hc, by rw [h₁, sub_add_cancel]⟩, h₂, hz₁, hz₂, hq⟩

end ClaudeChallenge2.State
