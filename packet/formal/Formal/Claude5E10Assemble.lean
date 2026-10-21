import Formal.Claude5E10Rho

/-!
# E10 model: an invariant from reduced tables

Written by a Claude worker (2026-10-20, E10 bridge session).

A region of parameters supplies reduced tables: `GL`, `GU` (cap line states up to the threefold
rotation) and `CT0` (tube line states, offsets modulo `m`).  The obligations `RedOK` (checked
for each region in generated files) give the full invariant `GG` with `InvOK` (`assemble`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w k : ℤ}

/-- The twist is `k` modulo `m`, and so is `p`. -/
structure Tw (p r s w k : ℤ) : Prop where
  qw : ∃ a : ℤ, w = k + (2 * r + s) * a
  qp : ∃ b : ℤ, p = k + (2 * r + s) * b

/-- Tables. -/
structure Tabs where
  GL : ℤ × ℤ → ℤ → ℤ → Prop
  GU : ℤ × ℤ → ℤ → ℤ → Prop
  CT0 : ℤ × ℤ → ℤ → ℤ → Prop

def Tabs.red (T : Tabs) (c : ℕ) : ℤ × ℤ → ℤ → ℤ → Prop := if c = 0 then T.GL else T.GU

/-- Cap states: a rotation of a reduced state. -/
def Tabs.cap (T : Tabs) (r s : ℤ) (c : ℕ) (d : ℤ × ℤ) (E ε : ℤ) : Prop :=
  ∃ t, t < 3 ∧ T.red c ((ρS r s c)^[t] (d, E)).1 ((ρS r s c)^[t] (d, E)).2 ε

/-- Tube states: offsets modulo `m`. -/
def Tabs.tube (T : Tabs) (r s : ℤ) (d : ℤ × ℤ) (E ε : ℤ) : Prop :=
  ∃ f Q, T.CT0 d f ε ∧ E = f + (2 * r + s) * Q

/-- Horizontal tube states (along a seam). -/
def Hz (p : ℤ) (d : ℤ × ℤ) (E ε : ℤ) : Prop :=
  (d = (1, -1) ∧ E = 0 ∧ ε = 1) ∨ (d = (-1, 1) ∧ E = 0 ∧ ε = -1) ∨
    (d = (1, -1) ∧ E = 2 * p ∧ ε = -1) ∨ (d = (-1, 1) ∧ E = -(2 * p) ∧ ε = 1)

/-- The assembled invariant. -/
def Tabs.GG (T : Tabs) (p r s : ℤ) (c : ℕ) (d : ℤ × ℤ) (E ε : ℤ) : Prop :=
  if c = 0 then T.cap r s 0 d E ε else if c = 1 then T.cap r s 1 d E ε
  else T.tube r s d E ε ∨ Hz p d E ε

/-- Base corners of the caps (one per rotation orbit). -/
def bc (r s : ℤ) : ℕ → ℕ → ℤ × ℤ
  | 0, 0 => (0, 0) | 0, _ => (r, 0)
  | _, 0 => (0, 0) | _, _ => (r + s, 0)

/-- The reduced obligations. -/
structure RedOK (p r s w k : ℤ) (T : Tabs) : Prop where
  startC : ∀ c, c < 2 → ∀ i, i < 2 → ∀ b e, CapDom r s c b → CapDom r s c e →
    b - bc r s c i ∈ unitVec → e - bc r s c i ∈ unitVec → e - b ∈ unitVec →
    T.cap r s c (e - bc r s c i) (cross (e - bc r s c i) (bc r s c i)) (cross (e - bc r s c i) (b - bc r s c i))
  capT : ∀ c, c < 2 → ∀ j, j < 6 → ∀ d E ε zE zO, T.red c d E ε → CapDom r s c zE →
    CapDom r s c zO → OnSide r s c j zE → OnSide r s c j zO → zO - zE ∈ unitVec →
    cross d zE = E → cross d (zO - zE) = ε → (Out r s c j (zE + d) ∨ Out r s c j (zO + d)) →
    T.tube r s (rotN (gk c j) d) (E + cross (rotN (gk c j) d) (gτ p r s w c j)) ε
  Tcap : ∀ c, c < 2 → ∀ j, j < 2 → ∀ d' f ε yE yO (Z : ℤ), T.CT0 (rotN (gk c j) d') f ε →
    CapDom r s c yE → CapDom r s c yO → OnSide r s c j yE → OnSide r s c j yO →
    yO - yE ∈ unitVec →
    cross d' yE = f - cross (rotN (gk c j) d') (gτ p r s w c j) + (2 * r + s) * Z →
    cross d' (yO - yE) = ε → (Inn1 r s c j (yE + d') ∨ Inn1 r s c j (yO + d')) →
    T.cap r s c d' (cross d' yE) ε
  avoidC : ∀ c, c < 2 → ∀ d E ε z, T.red c d E ε → CornerPos p r s w c z → cross d z ≠ E + ε
  avoidT : ∀ d f ε, T.CT0 d f ε → ∀ cc, (cc = 0 ∨ cc = r + s) →
    ¬ (2 * r + s) ∣ (f + ε + (d.1 + d.2) * cc) ∧
      ¬ (2 * r + s) ∣ (f + ε - (d.1 * (k - cc) - d.2 * (cc + k)))
  startT : ∀ cc, (cc = 0 ∨ cc = r + s) → ∀ u v, u ∈ unitVec → v ∈ unitVec → v - u ∈ unitVec →
    v.1 + v.2 ≠ 0 →
    ((0 ≤ u.1 + u.2 ∧ 0 ≤ v.1 + v.2) → T.tube r s v (-(v.1 + v.2) * cc) (cross v u)) ∧
    ((u.1 + u.2 ≤ 0 ∧ v.1 + v.2 ≤ 0) →
      T.tube r s v (v.1 * (k - cc) - v.2 * (cc + k)) (cross v u))

/-! ## Iterated rotation -/

theorem tube_shift {T : Tabs} {d : ℤ × ℤ} {E ε : ℤ} (h : T.tube r s d E ε) (Z : ℤ) :
    T.tube r s d (E + (2 * r + s) * Z) ε := by
  obtain ⟨f, Q, h1, rfl⟩ := h
  exact ⟨f, Q + Z, h1, by ring⟩

theorem tube_eq {T : Tabs} {d : ℤ × ℤ} {E E' ε : ℤ} (h : T.tube r s d E ε) (Z : ℤ)
    (e : E' = E + (2 * r + s) * Z) : T.tube r s d E' ε := e ▸ tube_shift h Z

theorem ρS_state (c : ℕ) (d z : ℤ × ℤ) :
    ρS r s c (d, cross d z) = (rotN 2 d, cross (rotN 2 d) (ρz r s c z)) := by
  simp only [ρS, cross_ρz]

theorem ρS_snd_add (c : ℕ) (d : ℤ × ℤ) (E X : ℤ) (t : ℕ) :
    ((ρS r s c)^[t] (d, E + X)) = (((ρS r s c)^[t] (d, E)).1, ((ρS r s c)^[t] (d, E)).2 + X) := by
  induction t generalizing d E with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    simp only [ρS]
    rw [show E + X + cross (rotN 2 d) (ρτ r s c) = (E + cross (rotN 2 d) (ρτ r s c)) + X by ring,
      ih]

end Claude5E10
