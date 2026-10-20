import Formal.Claude3SentDbW

/-!
# Theorem 1a, G6: condition 3 (b), the non-parallel case

Written by a Claude worker (2026-10-20, Theorem 1a, parts G6/A).

If the entry point moves across the rows of `y` as the height of `x` grows (`entV.2 = ±1`), the
heights are linked (`h_y + η = entV.2 h_x + entG.2`), the entry position is an own-height bound
of `y` (`σ = entV.1 entV.2 ∈ {0, -1}`, `np_entry`) and the output of `y` is a row (`npRow`).
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo

variable {S : Sig} {t : ℕ}

/-- The slope of the entry position in the height of `y`. -/
def npS (τx τy : PType S) (b : Bool) (w : List (Letter S)) : ℤ :=
  (entV τx τy b w).1 * (entV τx τy b w).2

/-- The constant of the entry position. -/
def npC (τx τy : PType S) (b : Bool) (w : List (Letter S)) (η : ℤ) : ClaudeChallenge2.Aff :=
  ⟨-(npS τx τy b w * (entG τx τy b w).2.a) + (entG τx τy b w).1.a,
    npS τx τy b w * η - npS τx τy b w * (entG τx τy b w).2.b + (entG τx τy b w).1.b⟩

theorem npC_eval (τx τy : PType S) (b : Bool) (w : List (Letter S)) (η : ℤ) (t : ℕ) :
    (npC τx τy b w η).eval t = npS τx τy b w * η - npS τx τy b w * (entG τx τy b w).2.eval t +
      (entG τx τy b w).1.eval t := by
  simp only [npC, ClaudeChallenge2.Aff.eval]; ring

theorem np_cases (τx τy : PType S) (b : Bool) (w : List (Letter S))
    (hv : (entV τx τy b w).2 ≠ 0) :
    ((entV τx τy b w).2 = 1 ∨ (entV τx τy b w).2 = -1) ∧
      (npS τx τy b w = 0 ∨ npS τx τy b w = -1) := by
  have hm := entV_mem τx τy b w
  unfold npS
  generalize entV τx τy b w = v at *
  rw [mem_unitVec_iff] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

theorem np_entry {x y : PState S} {b : Bool} {w : List (Letter S)} {η : ℤ}
    (hv : (entV x.1 y.1 b w).2 ≠ 0)
    (hh : y.2 + η = (entV x.1 y.1 b w).2 * x.2 + (entG x.1 y.1 b w).2.eval t) :
    (entV x.1 y.1 b w).1 * x.2 + (entG x.1 y.1 b w).1.eval t =
      npS x.1 y.1 b w * y.2 + (npC x.1 y.1 b w η).eval t := by
  rw [npC_eval]
  unfold npS
  rcases (np_cases x.1 y.1 b w hv).1 with h | h <;> rw [h] at hh ⊢
  · have : x.2 = y.2 + η - (entG x.1 y.1 b w).2.eval t := by linarith
    rw [this]; ring
  · have : x.2 = -(y.2 + η - (entG x.1 y.1 b w).2.eval t) := by linarith
    rw [this]; ring

/-- The output row of `y` in the non-parallel case. -/
def npRow (τx τy : PType S) (b : Bool) (w : List (Letter S)) (η η' : ℤ) (ed' : ED S) :
    RowSet S :=
  rowPtRow τy.f τy.k η' [⟨npS τx τy b w, affAdd (npC τx τy b w η) ((η - η' + 3) / 2)⟩]
    (edUps τy η' ed')

theorem npRow_wf (τx τy : PType S) (b : Bool) (w : List (Letter S)) (η η' : ℤ) (ed' : ED S)
    (hv : (entV τx τy b w).2 ≠ 0) : (npRow τx τy b w η η' ed').WF := by
  refine rowPtRow_wf _ _ _ ?_ ?_
  · simp only [List.mem_singleton, forall_eq, Bnd.WF]
    exact (np_cases τx τy b w hv).2
  · cases ed' with
    | hi => simpa [edUps, Bnd.WF] using upsY_wf τy η'
    | pin => simp [edUps, Bnd.WF]

theorem meetY_np {x y : PState S} {b : Bool} {w : List (Letter S)} {η : ℤ} (_hη : η = 0 ∨ η = 1)
    (hv : (entV x.1 y.1 b w).2 ≠ 0)
    (hh : y.2 + η = (entV x.1 y.1 b w).2 * x.2 + (entG x.1 y.1 b w).2.eval t)
    (ed' : ED S) {η' : ℤ} (hη' : η' = 0 ∨ η' = 1) (R : RowSet S) (h : ℤ) :
    MeetY t y (entI t x y b w η) ed' η' R h ↔ Meet S t (npRow x.1 y.1 b w η η' ed') y.2 R h := by
  have he := np_entry (t := t) hv hh
  have hY : ∀ z, YOut t y (entI t x y b w η) ed' η' z ↔
      (npRow x.1 y.1 b w η η' ed').At t y.2 z := by
    intro z
    rw [npRow, rowPtRow_at _ _ hη']
    simp only [YOut, entI, he, List.mem_singleton, forall_eq, affAdd_eval]
    refine exists_congr fun X' => ?_
    constructor
    · rintro ⟨h₁, h₂, rfl⟩; exact ⟨⟨by omega, h₂⟩, rfl⟩
    · rintro ⟨⟨h₁, h₂⟩, rfl⟩; exact ⟨by omega, h₂, rfl⟩
  simp only [MeetY, Meet, hY]
  rfl

end ClaudeChallenge2.State
