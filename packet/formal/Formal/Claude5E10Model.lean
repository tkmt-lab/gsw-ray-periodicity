import Formal.Claude5E10Spec
import Formal.Claude4C1G4
import Mathlib.Tactic.IntervalCases

/-!
# E10: the tube model

Written by a Claude worker (2026-10-20, E10 bridge session).

The sphere E10(p,r,s) is a lower hexagonal cap, a tube of circumference `3m` (`m = 2r + s`) and
height `2p`, and an upper hexagonal cap glued with a twist `w` (`w = p mod 3m`).

* vertices `(0, z)` (`z` interior to the lower cap `HL`, cell 0 coordinates), `(1, z)` (`z`
  interior to the upper cap `HU`, cell 1 coordinates), `(2, (u, h))` (`0 ≤ u < 3m`, `0 ≤ h ≤ 2p`,
  a tube point; `h = 0` and `h = 2p` are the two seams);
* charts `0` (lower cap), `1` (upper cap), `2` (the tube, the infinite strip `0 ≤ x + y ≤ 2p`
  with `u = x mod 3m`, `h = x + y`);
* `aL` : clockwise arclength on the lower cap from `L0`; the boundary point `z` is the tube
  point `(aL z, 0)`;
* `aU` : counterclockwise arclength on the upper cap from `U0`; the boundary point `z` is the
  tube point `(aU z + w mod 3m, 2p)`;
* `AdjM` : a unit step inside one chart.
-/

set_option linter.unusedVariables false

/-- `omega` after clearing `True`/`False` atoms (E10). -/
macro "e10om" : tactic => `(tactic| ((try simp only [or_true, true_or, not_true_eq_false,
  false_or, or_false, not_false_eq_true, true_and, and_true] at *) <;> omega))

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

/-- A model vertex. -/
abbrev MV : Type := ℤ × (ℤ × ℤ)

section defs

variable (p r s w : ℤ)

/-- Lower cap (cell 0): `L0 (0,0), L1 (r,0), L2 (r,r+s), L3 (0,2r+s), L4 (-(r+s),2r+s),
`L5 (-(r+s),r+s)`. -/
def HL (z : ℤ × ℤ) : Prop :=
  0 ≤ z.2 ∧ z.2 ≤ 2 * r + s ∧ -(r + s) ≤ z.1 ∧ z.1 ≤ r ∧ 0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ 2 * r + s

def IL (z : ℤ × ℤ) : Prop :=
  0 < z.2 ∧ z.2 < 2 * r + s ∧ -(r + s) < z.1 ∧ z.1 < r ∧ 0 < z.1 + z.2 ∧ z.1 + z.2 < 2 * r + s

/-- Upper cap (cell 1): `U0 (0,0), U5 (r+s,0), U4 (r+s,r), U3 (0,2r+s), U2 (-r,2r+s),
`U1 (-r,r)`. -/
def HU (z : ℤ × ℤ) : Prop :=
  0 ≤ z.2 ∧ z.2 ≤ 2 * r + s ∧ -r ≤ z.1 ∧ z.1 ≤ r + s ∧ 0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ 2 * r + s

def IU (z : ℤ × ℤ) : Prop :=
  0 < z.2 ∧ z.2 < 2 * r + s ∧ -r < z.1 ∧ z.1 < r + s ∧ 0 < z.1 + z.2 ∧ z.1 + z.2 < 2 * r + s

/-- The tube chart. -/
def HT (z : ℤ × ℤ) : Prop := 0 ≤ z.1 + z.2 ∧ z.1 + z.2 ≤ 2 * p

instance (z : ℤ × ℤ) : Decidable (IL r s z) := by unfold IL; infer_instance

instance (z : ℤ × ℤ) : Decidable (IU r s z) := by unfold IU; infer_instance

/-- Clockwise arclength on the lower cap from `L0` (values in `[0, 3m)`). -/
def aL (z : ℤ × ℤ) : ℤ :=
  if z.1 + z.2 = 0 ∧ z.1 ≤ 0 then z.2
  else if z.1 = -(r + s) then z.2
  else if z.2 = 2 * r + s ∨ z.1 + z.2 = 2 * r + s then 3 * r + 2 * s + z.1
  else if z.1 = r then 5 * r + 3 * s - z.2
  else 6 * r + 3 * s - z.1

/-- Counterclockwise arclength on the upper cap from `U0` (values in `[0, 3m)`). -/
def aU (z : ℤ × ℤ) : ℤ :=
  if z.2 = 0 ∧ 0 ≤ z.1 then z.1
  else if z.1 = r + s then r + s + z.2
  else if z.1 + z.2 = 2 * r + s ∨ z.2 = 2 * r + s then 3 * r + 2 * s - z.1
  else if z.1 = -r then 6 * r + 3 * s - z.2
  else 6 * r + 3 * s + z.1

/-- Reduction of `[0, 6m)` to `[0, 3m)`. -/
def wrap (x : ℤ) : ℤ := if x < 3 * (2 * r + s) then x else x - 3 * (2 * r + s)

/-- The domain of a chart. -/
def Dom : ℕ → ℤ × ℤ → Prop
  | 0, z => HL r s z
  | 1, z => HU r s z
  | _, z => HT p z

/-- The vertex of a chart point. -/
def ch : ℕ → ℤ × ℤ → MV
  | 0, z => if IL r s z then (0, z) else (2, (aL r s z, 0))
  | 1, z => if IU r s z then (1, z) else (2, (wrap r s (aU r s z + w), 2 * p))
  | _, z => (2, (z.1 % (3 * (2 * r + s)), z.1 + z.2))

/-- Model vertices. -/
def Valid (v : MV) : Prop :=
  (v.1 = 0 ∧ IL r s v.2) ∨ (v.1 = 1 ∧ IU r s v.2) ∨
    (v.1 = 2 ∧ 0 ≤ v.2.1 ∧ v.2.1 < 3 * (2 * r + s) ∧ 0 ≤ v.2.2 ∧ v.2.2 ≤ 2 * p)

abbrev MS : Type := {v : MV // Valid p r s v}

/-- Adjacency: a unit step inside one chart. -/
def AdjM (v x : MV) : Prop :=
  v ≠ x ∧ ∃ c, c < 3 ∧ ∃ z u, Dom p r s c z ∧ Dom p r s c (z + u) ∧ u ∈ unitVec ∧
    ch p r s w c z = v ∧ ch p r s w c (z + u) = x

end defs

variable {p r s w : ℤ}

theorem unit_iff {u : ℤ × ℤ} : u ∈ unitVec ↔
    u = (1, 0) ∨ u = (0, 1) ∨ u = (-1, 1) ∨ u = (-1, 0) ∨ u = (0, -1) ∨ u = (1, -1) := by
  simp [unitVec]

theorem unit_neg {u : ℤ × ℤ} (h : u ∈ unitVec) : -u ∈ unitVec := by
  rw [unit_iff] at h ⊢
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem adjM_symm {v x : MV} (h : AdjM p r s w v x) : AdjM p r s w x v := by
  obtain ⟨hne, c, hc, z, u, h1, h2, hu, rfl, rfl⟩ := h
  refine ⟨fun e => hne e.symm, c, hc, z + u, -u, h2, by simpa using h1, unit_neg hu, rfl,
    by simp⟩

/-- The model graph. -/
def GM (p r s w : ℤ) : SimpleGraph (MS p r s) where
  Adj x y := AdjM p r s w x.1 y.1
  symm := ⟨fun _ _ h => adjM_symm h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem gm_adj {x y : MS p r s} : (GM p r s w).Adj x y ↔ AdjM p r s w x.1 y.1 := Iff.rfl

/-- Unit vectors by components. -/
def U2 (a b : ℤ) : Prop :=
  (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = -1 ∧ b = 1) ∨ (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = -1) ∨
    (a = 1 ∧ b = -1)

theorem unit_U2 {u : ℤ × ℤ} : u ∈ unitVec ↔ U2 u.1 u.2 := by
  obtain ⟨a, b⟩ := u
  simp [unit_iff, U2]

theorem unit_sub {ρ ρ' : ℤ × ℤ} : ρ' - ρ ∈ unitVec ↔ U2 (ρ'.1 - ρ.1) (ρ'.2 - ρ.2) := by
  rw [unit_U2]; rfl

/-! ## Basic facts -/

theorem c_cases {c : ℕ} (hc : c < 3) : c = 0 ∨ c = 1 ∨ c = 2 := by omega

theorem chL_I {z : ℤ × ℤ} (h : IL r s z) : ch p r s w 0 z = (0, z) := by simp [ch, h]

theorem chL_B {z : ℤ × ℤ} (h : ¬ IL r s z) : ch p r s w 0 z = (2, (aL r s z, 0)) := by
  simp [ch, h]

theorem chU_I {z : ℤ × ℤ} (h : IU r s z) : ch p r s w 1 z = (1, z) := by simp [ch, h]

theorem chU_B {z : ℤ × ℤ} (h : ¬ IU r s z) :
    ch p r s w 1 z = (2, (wrap r s (aU r s z + w), 2 * p)) := by simp [ch, h]

theorem chT (z : ℤ × ℤ) : ch p r s w 2 z = (2, (z.1 % (3 * (2 * r + s)), z.1 + z.2)) := rfl

/-- Boundary points of the lower cap lie on one of the six sides. -/
theorem bdL_cases {z : ℤ × ℤ} (h : HL r s z) (hb : ¬ IL r s z) :
    z.2 = 0 ∨ z.1 = r ∨ z.1 + z.2 = 2 * r + s ∨ z.2 = 2 * r + s ∨ z.1 = -(r + s) ∨
      z.1 + z.2 = 0 := by
  simp only [HL, IL] at h hb; omega

theorem bdU_cases {z : ℤ × ℤ} (h : HU r s z) (hb : ¬ IU r s z) :
    z.2 = 0 ∨ z.1 = r + s ∨ z.1 + z.2 = 2 * r + s ∨ z.2 = 2 * r + s ∨ z.1 = -r ∨
      z.1 + z.2 = 0 := by
  simp only [HU, IU] at h hb; omega

theorem aL_range (hr : 1 ≤ r) (hs : 1 ≤ s) {z : ℤ × ℤ} (h : HL r s z) (hb : ¬ IL r s z) :
    0 ≤ aL r s z ∧ aL r s z < 3 * (2 * r + s) := by
  have hc := bdL_cases h hb
  simp only [HL] at h
  unfold aL; split_ifs <;> omega

theorem aU_range (hr : 1 ≤ r) (hs : 1 ≤ s) {z : ℤ × ℤ} (h : HU r s z) (hb : ¬ IU r s z) :
    0 ≤ aU r s z ∧ aU r s z < 3 * (2 * r + s) := by
  have hc := bdU_cases h hb
  simp only [HU] at h
  unfold aU; split_ifs <;> omega

theorem wrap_range (hr : 1 ≤ r) (hs : 1 ≤ s) {x : ℤ} (h0 : 0 ≤ x)
    (h1 : x < 6 * (2 * r + s)) : 0 ≤ wrap r s x ∧ wrap r s x < 3 * (2 * r + s) := by
  unfold wrap; split_ifs <;> omega

theorem emod_range (hr : 1 ≤ r) (hs : 1 ≤ s) (x : ℤ) :
    0 ≤ x % (3 * (2 * r + s)) ∧ x % (3 * (2 * r + s)) < 3 * (2 * r + s) :=
  ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩

/-- Chart points are model vertices. -/
theorem ch_valid (hp : 1 ≤ p) (hr : 1 ≤ r) (hs : 1 ≤ s) (hw0 : 0 ≤ w)
    (hw1 : w < 3 * (2 * r + s)) {c : ℕ} (hc : c < 3) {z : ℤ × ℤ} (hz : Dom p r s c z) :
    Valid p r s (ch p r s w c z) := by
  rcases c_cases hc with rfl | rfl | rfl
  · by_cases h : IL r s z
    · rw [chL_I h]; exact Or.inl ⟨rfl, h⟩
    · rw [chL_B h]
      have := aL_range hr hs hz h
      exact Or.inr (Or.inr ⟨rfl, this.1, this.2, le_refl _, by dsimp only; omega⟩)
  · by_cases h : IU r s z
    · rw [chU_I h]; exact Or.inr (Or.inl ⟨rfl, h⟩)
    · rw [chU_B h]
      have := aU_range hr hs hz h
      have := wrap_range hr hs (x := aU r s z + w) (by omega) (by omega)
      exact Or.inr (Or.inr ⟨rfl, this.1, this.2, by dsimp only; omega, le_refl _⟩)
  · rw [chT]
    have := emod_range hr hs z.1
    simp only [Dom, HT] at hz
    exact Or.inr (Or.inr ⟨rfl, this.1, this.2, hz.1, hz.2⟩)

end Claude5E10
