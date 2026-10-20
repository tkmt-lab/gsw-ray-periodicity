import Formal.Claude5O2Spec
import Formal.Claude4C1G4
import Mathlib.Tactic.IntervalCases

/-!
# O2: the pillow-and-pockets model

Written by a Claude worker (2026-10-20, O2 bridge session).

The two hexagons of O2 are the same hexagon: the reflection `ψ (x, y) = (y - d, x + d)` carries
the chart of cell 1 onto the chart of cell 0 so that `Aᵢ, Cᵢ` land on themselves and `Dᵢ` on
`Bᵢ` (the midpoint of a `2t`-side).  So O2 is a doubled hexagon ("pillow") sewn along its three
`d`-sides, with a rhombus ("pocket", two `t`-triangles) inserted into each slit `2t`-side.

* vertices `(k, z)`: `k = 0` every point of the hexagon `Hx`; `k = 1` a point of `Hx` off the
  `d`-sides; `k = 2 + i` an interior point of rhombus `i` (coordinates `[0,t]²`, corners
  `A = (0,0)`, `D = (t,0)`, `C = (t,t)`, `B = (0,t)`);
* five charts `c` (`0, 1` hexagons, `2 + i` rhombi) with `ch c z` the vertex of a chart point;
  the boundary of rhombus `i` goes to the `2t`-side `i` of the hexagon (`sp i`, the side
  `i = 0` is `y = 0`; the others are its images under the 120° rotation of the hexagon);
* `AdjM`: a unit step inside one chart.
-/

set_option linter.unusedVariables false

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

/-- A model vertex: sheet and point. -/
abbrev MV : Type := ℤ × (ℤ × ℤ)

section defs

variable (t d : ℤ)

/-- The hexagon (cell 0's chart): sides `y = 0` (A0 B0 C0), `x = 2t` (C0 A1), `x + y = 2t + d`
(A1 B1 C1), `y = 2t + d` (C1 A2), `x = -d` (A2 B2 C2), `x + y = 0` (C2 A0). -/
def Hx (z : ℤ × ℤ) : Prop :=
  0 ≤ z.2 ∧ z.1 ≤ 2 * t ∧ z.1 + z.2 ≤ 2 * t + d ∧ z.2 ≤ 2 * t + d ∧ -d ≤ z.1 ∧ 0 ≤ z.1 + z.2

/-- On one of the three `d`-sides. -/
def OnD (z : ℤ × ℤ) : Prop := z.1 = 2 * t ∨ z.2 = 2 * t + d ∨ z.1 + z.2 = 0

/-- The closed rhombus. -/
def Rh (z : ℤ × ℤ) : Prop := 0 ≤ z.1 ∧ z.1 ≤ t ∧ 0 ≤ z.2 ∧ z.2 ≤ t

/-- The open rhombus. -/
def RhI (z : ℤ × ℤ) : Prop := 0 < z.1 ∧ z.1 < t ∧ 0 < z.2 ∧ z.2 < t

instance (z : ℤ × ℤ) : Decidable (OnD t d z) := by unfold OnD; infer_instance

instance (z : ℤ × ℤ) : Decidable (RhI t z) := by unfold RhI; infer_instance

/-- The point at parameter `l ∈ [0, 2t]` of the `2t`-side `i` (from `Aᵢ` through `Bᵢ` to
`Cᵢ`). -/
def sp (i : ℕ) (l : ℤ) : ℤ × ℤ :=
  match i with
  | 0 => (l, 0)
  | 1 => (2 * t - l, l + d)
  | _ => (-d, 2 * t + d - l)

/-- Sheet of a rhombus boundary point (`0` on `A B C`, `1` on `A D C` off `A, C`). -/
def rk (z : ℤ × ℤ) : ℤ := if z.1 = 0 ∨ z.2 = t then 0 else 1

/-- Side parameter of a rhombus boundary point. -/
def rl (z : ℤ × ℤ) : ℤ :=
  if z.1 = 0 then z.2 else if z.2 = t then t + z.1 else if z.2 = 0 then z.1 else t + z.2

/-- The vertex of a chart point. -/
def ch : ℕ → ℤ × ℤ → MV
  | 0, z => (0, z)
  | 1, z => (if OnD t d z then 0 else 1, z)
  | i + 2, z => if RhI t z then ((i : ℤ) + 2, z) else (rk t z, sp t d i (rl t z))

/-- The domain of a chart. -/
def Dom : ℕ → ℤ × ℤ → Prop
  | 0, z => Hx t d z
  | 1, z => Hx t d z
  | _ + 2, z => Rh t z

/-- Model vertices. -/
def Valid (v : MV) : Prop :=
  (v.1 = 0 ∧ Hx t d v.2) ∨ (v.1 = 1 ∧ Hx t d v.2 ∧ ¬ OnD t d v.2) ∨
    ((v.1 = 2 ∨ v.1 = 3 ∨ v.1 = 4) ∧ RhI t v.2)

abbrev MS : Type := {v : MV // Valid t d v}

/-- Adjacency: a unit step inside one chart. -/
def AdjM (v w : MV) : Prop :=
  v ≠ w ∧ ∃ c, c < 5 ∧ ∃ z u, Dom t d c z ∧ Dom t d c (z + u) ∧ u ∈ unitVec ∧
    ch t d c z = v ∧ ch t d c (z + u) = w

end defs

variable {t d : ℤ}

theorem unit_iff {u : ℤ × ℤ} : u ∈ unitVec ↔
    u = (1, 0) ∨ u = (0, 1) ∨ u = (-1, 1) ∨ u = (-1, 0) ∨ u = (0, -1) ∨ u = (1, -1) := by
  simp [unitVec]

theorem unit_neg {u : ℤ × ℤ} (h : u ∈ unitVec) : -u ∈ unitVec := by
  rw [unit_iff] at h ⊢
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem adjM_symm {v w : MV} (h : AdjM t d v w) : AdjM t d w v := by
  obtain ⟨hne, c, hc, z, u, h1, h2, hu, rfl, rfl⟩ := h
  refine ⟨fun e => hne e.symm, c, hc, z + u, -u, h2, by simpa using h1, unit_neg hu, rfl,
    by simp⟩

/-- The model graph. -/
def GM (t d : ℤ) : SimpleGraph (MS t d) where
  Adj x y := AdjM t d x.1 y.1
  symm := ⟨fun _ _ h => adjM_symm h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem gm_adj {x y : MS t d} : (GM t d).Adj x y ↔ AdjM t d x.1 y.1 := Iff.rfl

/-! ## Basic facts about the charts -/

theorem ch0 (z : ℤ × ℤ) : ch t d 0 z = (0, z) := rfl

theorem ch1_onD {z : ℤ × ℤ} (h : OnD t d z) : ch t d 1 z = (0, z) := by simp [ch, h]

theorem ch1_nD {z : ℤ × ℤ} (h : ¬ OnD t d z) : ch t d 1 z = (1, z) := by simp [ch, h]

theorem chR_int (i : ℕ) {z : ℤ × ℤ} (h : RhI t z) : ch t d (i + 2) z = ((i : ℤ) + 2, z) := by
  simp [ch, h]

theorem chR_bd (i : ℕ) {z : ℤ × ℤ} (h : ¬ RhI t z) :
    ch t d (i + 2) z = (rk t z, sp t d i (rl t z)) := by
  simp [ch, h]

theorem sp_onD (ht : 1 ≤ t) (hd : 1 ≤ d) {i : ℕ} (hi : i < 3) {l : ℤ} (h0 : 0 ≤ l)
    (h2 : l ≤ 2 * t) : OnD t d (sp t d i l) ↔ l = 0 ∨ l = 2 * t := by
  interval_cases i <;> simp [sp, OnD] <;> omega

theorem sp_hx (ht : 1 ≤ t) (hd : 1 ≤ d) {i : ℕ} (hi : i < 3) {l : ℤ} (h0 : 0 ≤ l)
    (h2 : l ≤ 2 * t) : Hx t d (sp t d i l) := by
  interval_cases i <;> simp [sp, Hx] <;> omega

macro "rb_tac" : tactic =>
  `(tactic| (simp only [rk, rl]; split_ifs <;>
    first | rfl | (exfalso; omega) | (congr 1 <;> first | omega | (congr 1 <;> omega))))

/-- Rhombus side `A B` (`x = 0`) is the first half of the hexagon side, sheet 0. -/
theorem chR_AB (ht : 1 ≤ t) (i : ℕ) {z : ℤ × ℤ} (h1 : z.1 = 0) :
    ch t d (i + 2) z = ch t d 0 (sp t d i z.2) := by
  rw [chR_bd i (by simp [RhI]; omega), ch0]
  rb_tac

/-- Rhombus side `B C` (`y = t`) is the second half of the hexagon side, sheet 0. -/
theorem chR_BC (ht : 1 ≤ t) (i : ℕ) {z : ℤ × ℤ} (h1 : z.2 = t) (h0 : 0 ≤ z.1) :
    ch t d (i + 2) z = ch t d 0 (sp t d i (t + z.1)) := by
  rw [chR_bd i (by simp [RhI]; omega), ch0]
  rb_tac

/-- Rhombus side `A D` (`y = 0`) is the first half of the side on sheet 1. -/
theorem chR_AD (ht : 1 ≤ t) (hd : 1 ≤ d) {i : ℕ} (hi : i < 3) {z : ℤ × ℤ} (h1 : z.2 = 0)
    (h0 : 0 ≤ z.1) (h2 : z.1 ≤ t) : ch t d (i + 2) z = ch t d 1 (sp t d i z.1) := by
  rw [chR_bd i (by simp [RhI]; omega)]
  by_cases hz : z.1 = 0
  · rw [ch1_onD ((sp_onD (l := z.1) ht hd hi (by omega) (by omega)).2 (by omega))]
    rb_tac
  · rw [ch1_nD (fun h => by have := (sp_onD (l := z.1) ht hd hi (by omega) (by omega)).1 h; omega)]
    rb_tac

/-- Rhombus side `D C` (`x = t`) is the second half of the side on sheet 1. -/
theorem chR_DC (ht : 1 ≤ t) (hd : 1 ≤ d) {i : ℕ} (hi : i < 3) {z : ℤ × ℤ} (h1 : z.1 = t)
    (h0 : 0 ≤ z.2) (h2 : z.2 ≤ t) : ch t d (i + 2) z = ch t d 1 (sp t d i (t + z.2)) := by
  rw [chR_bd i (by simp [RhI]; omega)]
  by_cases hz : z.2 = t
  · rw [ch1_onD ((sp_onD (l := t + z.2) ht hd hi (by omega) (by omega)).2 (by omega))]
    rb_tac
  · rw [ch1_nD (fun h => by have := (sp_onD (l := t + z.2) ht hd hi (by omega) (by omega)).1 h; omega)]
    rb_tac

end Claude5O2
