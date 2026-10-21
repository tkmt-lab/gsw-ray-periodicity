import Formal.Claude5E10Deg

/-!
# E10 model: inner neighbours of the boundary points of the caps

Written by a Claude worker (2026-10-20, E10 bridge session).

A boundary point of a cap has two inner neighbours (unit steps into the interior) on a side and
one at a corner (`inL_card`, `inU_card`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option linter.style.maxHeartbeats false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

instance (a : ℤ) : Decidable (IsArc r s a) := by unfold IsArc; infer_instance

/-- Inner unit steps of a boundary point of the lower cap. -/
def inL (r s : ℤ) (l : ℤ) : Finset (ℤ × ℤ) := U6.filter (fun e => IL r s (PL r s l + e))

def inU (r s : ℤ) (l : ℤ) : Finset (ℤ × ℤ) := U6.filter (fun e => IU r s (PU r s l + e))

theorem card_U6_filter (P : ℤ × ℤ → Prop) [DecidablePred P] :
    (U6.filter P).card = (if P (1, 0) then 1 else 0) + (if P (0, 1) then 1 else 0) +
      (if P (-1, 1) then 1 else 0) + (if P (-1, 0) then 1 else 0) +
      (if P (0, -1) then 1 else 0) + (if P (1, -1) then 1 else 0) := by
  rw [Finset.card_filter]
  simp only [U6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

set_option maxHeartbeats 4000000 in
-- six boundary pieces times six unit steps
theorem PL_cases (r s l : ℤ) : (l ≤ r + s ∧ PL r s l = (-l, l)) ∨
    (r + s < l ∧ l ≤ 2 * r + s ∧ PL r s l = (-(r + s), l)) ∨
    (2 * r + s < l ∧ l ≤ 3 * r + 2 * s ∧ PL r s l = (l - 3 * r - 2 * s, 2 * r + s)) ∨
    (3 * r + 2 * s < l ∧ l ≤ 4 * r + 2 * s ∧ PL r s l = (l - 3 * r - 2 * s, 5 * r + 3 * s - l)) ∨
    (4 * r + 2 * s < l ∧ l ≤ 5 * r + 3 * s ∧ PL r s l = (r, 5 * r + 3 * s - l)) ∨
    (5 * r + 3 * s < l ∧ PL r s l = (6 * r + 3 * s - l, 0)) := by
  unfold PL; split_ifs <;> simp <;> omega

set_option maxHeartbeats 4000000 in
-- six boundary pieces times six unit steps
theorem inL_card (hr : 1 ≤ r) (hs : 1 ≤ s) {l : ℤ} (h0 : 0 ≤ l) (h1 : l < 3 * (2 * r + s)) :
    (inL r s l).card = if IsArc r s l then 1 else 2 := by
  unfold inL
  rw [card_U6_filter]
  rcases PL_cases r s l with ⟨a, e⟩ | ⟨a, b, e⟩ | ⟨a, b, e⟩ | ⟨a, b, e⟩ | ⟨a, b, e⟩ | ⟨a, e⟩ <;>
    rw [e] <;> simp only [IsArc, IL, Prod.mk_add_mk] <;> split_ifs <;> omega

set_option maxHeartbeats 4000000 in
-- six boundary pieces times six unit steps
theorem PU_cases (r s l : ℤ) : (l ≤ r + s ∧ PU r s l = (l, 0)) ∨
    (r + s < l ∧ l ≤ 2 * r + s ∧ PU r s l = (r + s, l - r - s)) ∨
    (2 * r + s < l ∧ l ≤ 3 * r + 2 * s ∧ PU r s l = (3 * r + 2 * s - l, l - r - s)) ∨
    (3 * r + 2 * s < l ∧ l ≤ 4 * r + 2 * s ∧ PU r s l = (3 * r + 2 * s - l, 2 * r + s)) ∨
    (4 * r + 2 * s < l ∧ l ≤ 5 * r + 3 * s ∧ PU r s l = (-r, 6 * r + 3 * s - l)) ∨
    (5 * r + 3 * s < l ∧ PU r s l = (l - 6 * r - 3 * s, 6 * r + 3 * s - l)) := by
  unfold PU; split_ifs <;> simp <;> omega

set_option maxHeartbeats 4000000 in
-- six boundary pieces times six unit steps
theorem inU_card (hr : 1 ≤ r) (hs : 1 ≤ s) {l : ℤ} (h0 : 0 ≤ l) (h1 : l < 3 * (2 * r + s)) :
    (inU r s l).card = if IsArc r s l then 1 else 2 := by
  unfold inU
  rw [card_U6_filter]
  rcases PU_cases r s l with ⟨a, e⟩ | ⟨a, b, e⟩ | ⟨a, b, e⟩ | ⟨a, b, e⟩ | ⟨a, b, e⟩ | ⟨a, e⟩ <;>
    rw [e] <;> simp only [IsArc, IU, Prod.mk_add_mk] <;> split_ifs <;> omega

end Claude5E10
