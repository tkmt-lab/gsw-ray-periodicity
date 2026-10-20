import Formal.Claude3StateDef

/-!
# Theorem 1a, G4: basic facts about row points, passages and transitions

Written by a Claude worker (2026-10-20, Theorem 1a, parts G4/G5).

* `RV.unique`, `RV.inj` : a row point has one vertex; under `Valid` distinct row points of one
  state have distinct vertices.
* `PassOK.rv` : every point `rp σ j`, `i ≤ j ≤ e + 2`, of a valid passage lies in the chart.
* `RV.adj`, `RV.next` : unit steps are edges; four consecutive row points are a forced step.
* `ExitAt.unique`, `RootAt.unique`, `TransAt.unique` : exit, root start and transition entry are
  determined by the states (used by G6 to replace the index quantifiers by terms).
* `TransAt.next` : the generic transition is a forced step.
* `St_finite` : the state domain at `t` is finite.
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo

variable {S : Sig} {t : ℕ}

theorem mem_rp_iff (σ : PState S) (i : ℤ) :
    (S.chart σ.1.f).Mem t (rp σ i) ↔ (rc σ.1).Mem t (rowPt σ.2 i) :=
  mem_rotN_iff _ _ _ _

theorem rv_of_mem {σ : PState S} {i : ℤ} (hz : (S.chart σ.1.f).Mem t (rp σ i)) :
    RV t σ i (pt S t σ.1.f (rp σ i) hz) := ⟨hz, rfl⟩

theorem RV.mem {σ : PState S} {i : ℤ} {v : Vertex S t} (h : RV t σ i v) :
    (S.chart σ.1.f).Mem t (rp σ i) := h.1

theorem RV.unique {σ : PState S} {i : ℤ} {v w : Vertex S t} (hv : RV t σ i v)
    (hw : RV t σ i w) : v = w := by
  obtain ⟨_, rfl⟩ := hv
  obtain ⟨_, rfl⟩ := hw
  rfl

theorem RV.congr {σ : PState S} {i j : ℤ} {v : Vertex S t} (hv : RV t σ i v) (e : i = j) :
    RV t σ j v := e ▸ hv

theorem rp_injective (σ : PState S) : Function.Injective (rp σ) := fun _ _ e =>
  rowPt_injective _ (rotN_injective _ e)

theorem RV.inj (hV : Valid S t) {σ : PState S} {i j : ℤ} {v : Vertex S t} (hi : RV t σ i v)
    (hj : RV t σ j v) : i = j := by
  obtain ⟨h1, e1⟩ := hi
  obtain ⟨h2, e2⟩ := hj
  exact rp_injective σ (valid_pt_inj hV h1 h2 (e1.trans e2.symm))

theorem rp_step1 (σ : PState S) (i : ℤ) : rp σ (i + 1) - rp σ i ∈ unitVec := by
  unfold rp; rw [← rotN_sub]; exact rotN_mem_unitVec _ (rowPt_step1 _ _)

theorem rp_step2 (σ : PState S) (i : ℤ) : rp σ (i + 2) - rp σ i ∈ unitVec := by
  unfold rp; rw [← rotN_sub, rowPt_step2]; exact rotN_mem_unitVec _ (by decide)

theorem rp_step3 (σ : PState S) (i : ℤ) : rp σ (i + 3) ≠ rp σ i := fun e =>
  rowPt_step3 _ _ (rotN_injective _ e)

/-- A unit step between row points is an edge. -/
theorem RV.adj (hV : Valid S t) {σ : PState S} {i j : ℤ} {v w : Vertex S t} (hv : RV t σ i v)
    (hw : RV t σ j w) (hu : rp σ j - rp σ i ∈ unitVec) : (graph S t).Adj v w := by
  obtain ⟨h1, rfl⟩ := hv
  obtain ⟨h2, rfl⟩ := hw
  exact valid_adj_of_unit hV h1 h2 hu

theorem RV.adj1 (hV : Valid S t) {σ : PState S} {i : ℤ} {v w : Vertex S t} (hv : RV t σ i v)
    (hw : RV t σ (i + 1) w) : (graph S t).Adj v w := hv.adj hV hw (rp_step1 σ i)

theorem RV.adj2 (hV : Valid S t) {σ : PState S} {i : ℤ} {v w : Vertex S t} (hv : RV t σ i v)
    (hw : RV t σ (i + 2) w) : (graph S t).Adj v w := hv.adj hV hw (rp_step2 σ i)

/-- Four consecutive row points form a forced step. -/
theorem RV.next (hV : Valid S t) {σ : PState S} {i : ℤ} {v₀ v₁ v₂ v₃ : Vertex S t}
    (h₀ : RV t σ i v₀) (h₁ : RV t σ (i + 1) v₁) (h₂ : RV t σ (i + 2) v₂)
    (h₃ : RV t σ (i + 3) v₃) : Next (graph S t) v₀ v₁ v₂ v₃ := by
  obtain ⟨m₀, rfl⟩ := h₀
  obtain ⟨m₁, rfl⟩ := h₁
  obtain ⟨m₂, rfl⟩ := h₂
  obtain ⟨m₃, rfl⟩ := h₃
  have s1 := rp_step1 σ (i + 1)
  have s0 := rp_step1 σ i
  have s2 := rp_step2 σ i
  have s2' := rp_step2 σ (i + 1)
  have s1' := rp_step1 σ (i + 2)
  have s3 := rp_step3 σ i
  rw [show i + 1 + 1 = i + 2 by ring] at s1
  rw [show i + 1 + 2 = i + 3 by ring] at s2'
  rw [show i + 2 + 1 = i + 3 by ring] at s1'
  exact (valid_next_iff hV m₁ m₂ m₀ m₃ s1 s0 s2 s2' s1' (Ne.symm s3) _).2 rfl

/-! ## Passages -/

theorem PassOK.rows {σ : PState S} {i e : ℤ} (h : PassOK t σ i e) : RowsIn t σ := h.1

/-- Every point of a valid passage (indices `i … e+2`) lies in the chart. -/
theorem PassOK.mem {σ : PState S} {i e : ℤ} (h : PassOK t σ i e) {j : ℤ} (hj : i ≤ j)
    (hj' : j ≤ e + 2) : (S.chart σ.1.f).Mem t (rp σ j) := by
  obtain ⟨hr, hl, hie, heh, -⟩ := h
  rw [mem_rp_iff]
  by_cases hje : j ≤ e
  · exact ((rowTri_iff hr j).2 ⟨by unfold loS at hl; omega, by unfold hiS at heh; omega⟩).1
  · have T := (rowTri_iff hr e).2 ⟨by unfold loS at hl; omega, by unfold hiS at heh; omega⟩
    rcases (show j = e + 1 ∨ j = e + 2 by omega) with rfl | rfl
    · exact T.2.1
    · exact T.2.2

theorem PassOK.rv {σ : PState S} {i e : ℤ} (h : PassOK t σ i e) {j : ℤ} (hj : i ≤ j)
    (hj' : j ≤ e + 2) : ∃ v, RV t σ j v := ⟨_, rv_of_mem (h.mem hj hj')⟩

/-- Row points with triangle index in `[lo, hi]` lie in the chart (with their two successors). -/
theorem mem_of_tri {σ : PState S} (hr : RowsIn t σ) {j : ℤ} (h1 : loS t σ ≤ j)
    (h2 : j ≤ hiS t σ) {m : ℤ} (hm : 0 ≤ m) (hm' : m ≤ 2) :
    (S.chart σ.1.f).Mem t (rp σ (j + m)) := by
  rw [mem_rp_iff]
  have T := (rowTri_iff hr j).2 ⟨h1, h2⟩
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl
  · simpa using T.1
  · exact T.2.1
  · exact T.2.2

/-- Conversely, if three consecutive row points lie in the chart, the rows do and the triangle
index lies in `[lo, hi]`. -/
theorem tri_of_mem {σ : PState S} {j : ℤ} (h0 : (S.chart σ.1.f).Mem t (rp σ j))
    (h1 : (S.chart σ.1.f).Mem t (rp σ (j + 1))) (h2 : (S.chart σ.1.f).Mem t (rp σ (j + 2))) :
    RowsIn t σ ∧ loS t σ ≤ j ∧ j ≤ hiS t σ := by
  rw [mem_rp_iff] at h0 h1 h2
  have T : TriIn (rc σ.1) t (rowPt σ.2) j := ⟨h0, h1, h2⟩
  have hr := rowTri_rows T
  exact ⟨hr, (rowTri_iff hr j).1 T⟩

theorem CornerV.unique {m : Fin S.M} {v w : Vertex S t} (hv : CornerV t m v)
    (hw : CornerV t m w) : v = w := by
  obtain ⟨_, rfl⟩ := hv
  obtain ⟨_, rfl⟩ := hw
  rfl

theorem AtCorner.inj (hV : Valid S t) {σ : PState S} {i j : ℤ} {m : Fin S.M}
    (hi : AtCorner t σ i m) (hj : AtCorner t σ j m) : i = j := by
  obtain ⟨v, hv, cv⟩ := hi
  obtain ⟨w, hw, cw⟩ := hj
  rw [CornerV.unique cv cw] at hv
  exact hv.inj hV hw

/-- The exit index is determined by the state. -/
theorem ExitAt.unique (hV : Valid S t) {σ : PState S} {e e' : ℤ} (h : ExitAt t σ e)
    (h' : ExitAt t σ e') : e = e' := by
  cases hτ : σ.1.term with
  | none => rw [h.1 hτ, h'.1 hτ]
  | some m =>
    have := AtCorner.inj hV (h.2 m hτ) (h'.2 m hτ)
    omega

theorem PassOK.exit_unique (hV : Valid S t) {σ : PState S} {i i' e e' : ℤ}
    (h : PassOK t σ i e) (h' : PassOK t σ i' e') : e = e' :=
  ExitAt.unique hV h.2.2.2.2 h'.2.2.2.2

/-- The root start index is determined by the state. -/
theorem RootAt.unique (hV : Valid S t) {σ : PState S} {i i' : ℤ} (h : RootAt t σ i)
    (h' : RootAt t σ i') : i = i' := by
  obtain ⟨m, hm, hc⟩ := h
  obtain ⟨m', hm', hc'⟩ := h'
  rw [hm] at hm'
  cases hm'
  exact AtCorner.inj hV hc hc'

/-- The entry index of a transition is determined by the two states. -/
theorem TransAt.unique (hV : Valid S t) {x y : PState S} {i i' : ℤ} (h : TransAt t x y i)
    (h' : TransAt t x y i') : i = i' := by
  obtain ⟨-, -, -, ⟨v, hv, hxv⟩, -⟩ := h
  obtain ⟨-, -, -, ⟨w, hw, hxw⟩, -⟩ := h'
  rw [hxv.unique hxw] at hv
  exact hv.inj hV hw

theorem TransAt.not_root {x y : PState S} {i i' : ℤ} (h : TransAt t x y i) :
    ¬ RootAt t y i' := by
  rintro ⟨m, hm, -⟩
  rw [h.2.1] at hm
  cases hm

/-- The generic transition is a forced step: `c'` continues `(q_u, q_{u+1}, q_{u+2})`. -/
theorem TransAt.next (hV : Valid S t) {x y : PState S} {i : ℤ} (h : TransAt t x y i)
    {w v₀ v₁ v₂ : Vertex S t} (hw : RV t x (hiS t x) w) (h₀ : RV t y i v₀)
    (h₁ : RV t y (i + 1) v₁) (h₂ : RV t y (i + 2) v₂) :
    Next (graph S t) w v₀ v₁ v₂ :=
  ⟨h.2.2.2.2.2 v₂ w h₂ hw, h₀.adj2 hV h₂, by
    have := h₁.adj1 hV (h₂.congr (by ring : i + 2 = i + 1 + 1))
    simpa using this⟩

/-- The state domain at `t` is finite. -/
theorem St_finite (t : ℕ) : (R002.Claude3Fold.St (stLo (S := S)) stHi t).Finite := by
  have : R002.Claude3Fold.St (stLo (S := S)) stHi t ⊆
      ⋃ τ : PType S, (fun h : ℤ => (τ, h)) '' Set.Icc ((stLo τ).eval t) ((stHi τ).eval t) := by
    rintro ⟨τ, h⟩ hs
    exact Set.mem_iUnion.2 ⟨τ, h, hs, rfl⟩
  exact (Set.finite_iUnion fun τ => (Set.finite_Icc _ _).image _).subset this

end ClaudeChallenge2.State
