import Formal.Claude7D12Spec
import Formal.Claude4C1G4
import Mathlib.Tactic.IntervalCases

/-!
# D12: the seam-circle model

Written by a Claude worker (2026-10-22, D12 bridge session), adapting `Claude5D14Model.lean`.

The two cells of D12 are regular hexagons `H0`, `H1` of side `L = r + 2s` (cell 0 is `H_L`
translated by `(-(r + s), 0)`, cell 1 is `H_L`), each side cut at a label, and every one of the
twelve labelled segments of `H0` is glued to the equally labelled segment of `H1`: the sphere is
two hexagons whose boundary circles are glued with the corners shifted by `s`.  We keep the cell
coordinates as the two charts and record a boundary point by its arclength on the common seam
circle of length `6L`.

* vertices `(0, z)` (`z` interior to `H0`), `(1, z)` (`z` interior to `H1`), `(2, (l, 0))`
  (`0 ≤ l < 6r + 12s`, a point of the seam);
* `a0`, `a1` : arclength of a boundary point of `H0` (counterclockwise from the label-0 point
  `(0,0)`) and of `H1` (clockwise from its label-0 corner `(0,0)`); glued points have equal
  arclength, and the label-`j` point has arclength `⌊j/2⌋ (r + 2s) + (j mod 2) s`;
* `ch c z` : the vertex of the point `z` of chart `c`;
* `AdjM` : a unit step inside one chart.
-/

set_option linter.unusedVariables false

/-- `omega` after clearing `True`/`False` atoms left by `simp` in the hypotheses. -/
macro "d12om" : tactic => `(tactic| ((try simp only [or_true, true_or, not_true_eq_false,
  false_or, or_false, not_false_eq_true, true_and, and_true] at *) <;> omega))

namespace Claude7D12

open ClaudeChallenge Claude2Aligned

/-- A model vertex. -/
abbrev MV : Type := ℤ × (ℤ × ℤ)

section defs

variable (r s : ℤ)

/-- Cell 0: sides `y = 0`, `x = s`, `x + y = r + 3s`, `y = 2r + 4s`, `x = -2r - 3s`,
`x + y = -r - s`. -/
def H0 (z : ℤ × ℤ) : Prop :=
  0 ≤ z.2 ∧ z.2 ≤ 2 * r + 4 * s ∧ -2 * r - 3 * s ≤ z.1 ∧ z.1 ≤ s ∧ -r - s ≤ z.1 + z.2 ∧
    z.1 + z.2 ≤ r + 3 * s

def I0 (z : ℤ × ℤ) : Prop :=
  0 < z.2 ∧ z.2 < 2 * r + 4 * s ∧ -2 * r - 3 * s < z.1 ∧ z.1 < s ∧ -r - s < z.1 + z.2 ∧
    z.1 + z.2 < r + 3 * s

/-- Cell 1: sides `y = 0`, `x = r + 2s`, `x + y = 2r + 4s`, `y = 2r + 4s`, `x = -r - 2s`,
`x + y = 0`. -/
def H1 (z : ℤ × ℤ) : Prop :=
  0 ≤ z.2 ∧ z.2 ≤ 2 * r + 4 * s ∧ -r - 2 * s ≤ z.1 ∧ z.1 ≤ r + 2 * s ∧ 0 ≤ z.1 + z.2 ∧
    z.1 + z.2 ≤ 2 * r + 4 * s

def I1 (z : ℤ × ℤ) : Prop :=
  0 < z.2 ∧ z.2 < 2 * r + 4 * s ∧ -r - 2 * s < z.1 ∧ z.1 < r + 2 * s ∧ 0 < z.1 + z.2 ∧
    z.1 + z.2 < 2 * r + 4 * s

instance (z : ℤ × ℤ) : Decidable (I0 r s z) := by unfold I0; infer_instance

instance (z : ℤ × ℤ) : Decidable (I1 r s z) := by unfold I1; infer_instance

/-- Arclength on the boundary of `H0`, counterclockwise from `(0,0)`. -/
def a0 (z : ℤ × ℤ) : ℤ :=
  if z.2 = 0 then (if 0 ≤ z.1 then z.1 else 6 * r + 12 * s + z.1)
  else if z.1 = s then s + z.2
  else if z.1 + z.2 = r + 3 * s ∨ z.2 = 2 * r + 4 * s then r + 4 * s - z.1
  else 5 * r + 11 * s - z.2

/-- Arclength on the boundary of `H1`, clockwise from `(0,0)`. -/
def a1 (z : ℤ × ℤ) : ℤ :=
  if z.1 + z.2 = 0 ∨ z.1 = -r - 2 * s then z.2
  else if z.2 = 2 * r + 4 * s ∨ z.1 + z.2 = 2 * r + 4 * s then 3 * r + 6 * s + z.1
  else if z.1 = r + 2 * s then 5 * r + 10 * s - z.2
  else 6 * r + 12 * s - z.1

/-- The domain of a chart. -/
def Dom : ℕ → ℤ × ℤ → Prop
  | 0, z => H0 r s z
  | _, z => H1 r s z

/-- The interior of a chart. -/
def Inn : ℕ → ℤ × ℤ → Prop
  | 0, z => I0 r s z
  | _, z => I1 r s z

/-- The arclength of a boundary point of a chart. -/
def arc : ℕ → ℤ × ℤ → ℤ
  | 0, z => a0 r s z
  | _, z => a1 r s z

/-- The vertex of a chart point. -/
def ch : ℕ → ℤ × ℤ → MV
  | 0, z => if I0 r s z then (0, z) else (2, (a0 r s z, 0))
  | _, z => if I1 r s z then (1, z) else (2, (a1 r s z, 0))

/-- Model vertices. -/
def Valid (v : MV) : Prop :=
  (v.1 = 0 ∧ I0 r s v.2) ∨ (v.1 = 1 ∧ I1 r s v.2) ∨
    (v.1 = 2 ∧ v.2.2 = 0 ∧ 0 ≤ v.2.1 ∧ v.2.1 < 6 * r + 12 * s)

abbrev MS : Type := {v : MV // Valid r s v}

/-- Adjacency: a unit step inside one chart. -/
def AdjM (v w : MV) : Prop :=
  v ≠ w ∧ ∃ c, c < 2 ∧ ∃ z u, Dom r s c z ∧ Dom r s c (z + u) ∧ u ∈ unitVec ∧
    ch r s c z = v ∧ ch r s c (z + u) = w

/-- Neighbouring arclengths on the seam circle. -/
def ArcAdj (l l' : ℤ) : Prop :=
  l' = l + 1 ∨ l = l' + 1 ∨ (l = 0 ∧ l' = 6 * r + 12 * s - 1) ∨ (l' = 0 ∧ l = 6 * r + 12 * s - 1)

end defs

variable {r s : ℤ}

theorem unit_iff {u : ℤ × ℤ} : u ∈ unitVec ↔
    u = (1, 0) ∨ u = (0, 1) ∨ u = (-1, 1) ∨ u = (-1, 0) ∨ u = (0, -1) ∨ u = (1, -1) := by
  simp [unitVec]

theorem unit_neg {u : ℤ × ℤ} (h : u ∈ unitVec) : -u ∈ unitVec := by
  rw [unit_iff] at h ⊢
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem adjM_symm {v w : MV} (h : AdjM r s v w) : AdjM r s w v := by
  obtain ⟨hne, c, hc, z, u, h1, h2, hu, rfl, rfl⟩ := h
  refine ⟨fun e => hne e.symm, c, hc, z + u, -u, h2, by simpa using h1, unit_neg hu, rfl,
    by simp⟩

/-- The model graph. -/
def GM (r s : ℤ) : SimpleGraph (MS r s) where
  Adj x y := AdjM r s x.1 y.1
  symm := ⟨fun _ _ h => adjM_symm h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem gm_adj {x y : MS r s} : (GM r s).Adj x y ↔ AdjM r s x.1 y.1 := Iff.rfl

/-- Unit vectors by components. -/
def U2 (a b : ℤ) : Prop :=
  (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = -1 ∧ b = 1) ∨ (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = -1) ∨
    (a = 1 ∧ b = -1)

theorem unit_U2 {u : ℤ × ℤ} : u ∈ unitVec ↔ U2 u.1 u.2 := by
  obtain ⟨a, b⟩ := u
  simp [unit_iff, U2]

theorem unit_sub {ρ ρ' : ℤ × ℤ} : ρ' - ρ ∈ unitVec ↔ U2 (ρ'.1 - ρ.1) (ρ'.2 - ρ.2) := by
  rw [unit_U2]; rfl

/-! ## Basic facts about the charts -/

theorem c_cases {c : ℕ} (hc : c < 2) : c = 0 ∨ c = 1 := by omega

theorem ch0_I {z : ℤ × ℤ} (h : I0 r s z) : ch r s 0 z = (0, z) := by simp [ch, h]

theorem ch0_B {z : ℤ × ℤ} (h : ¬ I0 r s z) : ch r s 0 z = (2, (a0 r s z, 0)) := by simp [ch, h]

theorem ch1_I {z : ℤ × ℤ} (h : I1 r s z) : ch r s 1 z = (1, z) := by simp [ch, h]

theorem ch1_B {z : ℤ × ℤ} (h : ¬ I1 r s z) : ch r s 1 z = (2, (a1 r s z, 0)) := by simp [ch, h]

theorem ch_I {c : ℕ} (hc : c < 2) {z : ℤ × ℤ} (h : Inn r s c z) : ch r s c z = ((c : ℤ), z) := by
  rcases c_cases hc with rfl | rfl
  · exact ch0_I h
  · exact ch1_I h

theorem ch_B {c : ℕ} (hc : c < 2) {z : ℤ × ℤ} (h : ¬ Inn r s c z) :
    ch r s c z = (2, (arc r s c z, 0)) := by
  rcases c_cases hc with rfl | rfl
  · exact ch0_B h
  · exact ch1_B h

/-- Boundary points of cell 0 lie on one of the six sides. -/
theorem bd0_cases {z : ℤ × ℤ} (h : H0 r s z) (hb : ¬ I0 r s z) :
    z.2 = 0 ∨ z.1 = s ∨ z.1 + z.2 = r + 3 * s ∨ z.2 = 2 * r + 4 * s ∨ z.1 = -2 * r - 3 * s ∨
      z.1 + z.2 = -r - s := by
  simp only [H0, I0] at h hb; omega

theorem bd1_cases {z : ℤ × ℤ} (h : H1 r s z) (hb : ¬ I1 r s z) :
    z.2 = 0 ∨ z.1 = r + 2 * s ∨ z.1 + z.2 = 2 * r + 4 * s ∨ z.2 = 2 * r + 4 * s ∨
      z.1 = -r - 2 * s ∨ z.1 + z.2 = 0 := by
  simp only [H1, I1] at h hb; omega

theorem a0_range (hr : 1 ≤ r) (hs : 1 ≤ s) {z : ℤ × ℤ} (h : H0 r s z) (hb : ¬ I0 r s z) :
    0 ≤ a0 r s z ∧ a0 r s z < 6 * r + 12 * s := by
  have hc := bd0_cases h hb
  simp only [H0] at h
  unfold a0; split_ifs <;> omega

theorem a1_range (hr : 1 ≤ r) (hs : 1 ≤ s) {z : ℤ × ℤ} (h : H1 r s z) (hb : ¬ I1 r s z) :
    0 ≤ a1 r s z ∧ a1 r s z < 6 * r + 12 * s := by
  have hc := bd1_cases h hb
  simp only [H1] at h
  unfold a1; split_ifs <;> omega

end Claude7D12
