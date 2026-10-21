import Formal.Claude5E10Kill2

/-!
# E10 model: the threefold rotation of the caps

Written by a Claude worker (2026-10-20, E10 bridge session).

`ρz c` rotates a cap by `120°` about its centre (`L0 ↦ L2`, `U0 ↦ U4`): side `j` goes to side
`j + 2`, and the side isometries commute with it up to a shift of the tube by a multiple of
`(m, −m)` (`gτ_ρ`).  `ρS c` is the induced map on line states `(d, E)`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

/-- Translation of the cap rotation. -/
def ρτ (r s : ℤ) : ℕ → ℤ × ℤ
  | 0 => (r, r + s)
  | _ => (r + s, r)

/-- The cap rotation. -/
def ρz (r s : ℤ) (c : ℕ) (z : ℤ × ℤ) : ℤ × ℤ := rotN 2 z + ρτ r s c

/-- The cap rotation on line states. -/
def ρS (r s : ℤ) (c : ℕ) (x : (ℤ × ℤ) × ℤ) : (ℤ × ℤ) × ℤ :=
  (rotN 2 x.1, x.2 + cross (rotN 2 x.1) (ρτ r s c))

/-- The tube shift of the side isometries under the rotation. -/
def lam : ℕ → ℕ → ℤ
  | 0, 4 => 2 | 0, 5 => 2 | 0, _ => -1
  | _, 4 => -2 | _, 5 => -2 | _, _ => 1

theorem ρz_sub (c : ℕ) (z z' : ℤ × ℤ) : ρz r s c z - ρz r s c z' = rotN 2 (z - z') := by
  simp only [ρz]; rw [← rotN_sub']; abel

theorem rotN_add2 (z d : ℤ × ℤ) : rotN 2 (z + d) = rotN 2 z + rotN 2 d := by
  simp only [rotN, rot]; ext <;> simp <;> ring

theorem ρz_add (c : ℕ) (z d : ℤ × ℤ) : ρz r s c (z + d) = ρz r s c z + rotN 2 d := by
  simp only [ρz]; rw [rotN_add2]; abel

theorem cross_ρz (c : ℕ) (d z : ℤ × ℤ) :
    cross (rotN 2 d) (ρz r s c z) = cross d z + cross (rotN 2 d) (ρτ r s c) := by
  simp only [ρz]; rw [cross_add', cross_rotN]

theorem capDom_ρ {c : ℕ} (hc : c < 2) (z : ℤ × ℤ) :
    CapDom r s c (ρz r s c z) ↔ CapDom r s c z := by
  obtain ⟨x, y⟩ := z
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;>
    simp only [CapDom, HL, HU, ρz, ρτ, rotN, rot, Prod.fst_add, Prod.snd_add, ite_true,
      show (1 : ℕ) ≠ 0 by norm_num, ite_false] <;> omega

set_option maxHeartbeats 1000000 in
-- twelve sides
theorem onSide_ρ {c j : ℕ} (hc : c < 2) (hj : j < 6) (z : ℤ × ℤ) :
    OnSide r s c ((j + 2) % 6) (ρz r s c z) ↔ OnSide r s c j z := by
  obtain ⟨x, y⟩ := z
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> interval_cases j <;>
    simp only [OnSide, ρz, ρτ, rotN, rot, Prod.fst_add, Prod.snd_add,
      Nat.reduceAdd, Nat.reduceMod] <;> omega

set_option maxHeartbeats 1000000 in
-- twelve sides
theorem out_ρ {c j : ℕ} (hc : c < 2) (hj : j < 6) (z : ℤ × ℤ) :
    Out r s c ((j + 2) % 6) (ρz r s c z) ↔ Out r s c j z := by
  obtain ⟨x, y⟩ := z
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> interval_cases j <;>
    simp only [Out, ρz, ρτ, rotN, rot, Prod.fst_add, Prod.snd_add,
      Nat.reduceAdd, Nat.reduceMod] <;> omega

set_option maxHeartbeats 1000000 in
-- twelve sides
theorem inn1_ρ {c j : ℕ} (hc : c < 2) (hj : j < 6) (z : ℤ × ℤ) :
    Inn1 r s c ((j + 2) % 6) (ρz r s c z) ↔ Inn1 r s c j z := by
  obtain ⟨x, y⟩ := z
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> interval_cases j <;>
    simp only [Inn1, ρz, ρτ, rotN, rot, Prod.fst_add, Prod.snd_add,
      Nat.reduceAdd, Nat.reduceMod] <;> omega

theorem corner_ρ_fwd {c : ℕ} (hc : c < 2) {z : ℤ × ℤ} (h : CornerPos p r s w c z) :
    CornerPos p r s w c (ρz r s c z) := by
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> simp only [CornerPos] at h ⊢ <;>
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [ρz, ρτ, rotN, rot, Prod.mk_add_mk, Prod.mk.injEq] <;> omega

theorem gk_ρ {c j : ℕ} (hc : c < 2) (hj : j < 6) (d : ℤ × ℤ) :
    rotN (gk c ((j + 2) % 6)) (rotN 2 d) = rotN (gk c j) d := by
  rw [rotN_add_mod]
  congr 1
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> interval_cases j <;> rfl

theorem gτ_ρ {c j : ℕ} (hc : c < 2) (hj : j < 6) :
    rotN (gk c ((j + 2) % 6)) (ρτ r s c) + gτ p r s w c ((j + 2) % 6) =
      gτ p r s w c j + (lam c j * (2 * r + s), -(lam c j * (2 * r + s))) := by
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> interval_cases j <;>
    simp only [gk, gτ, ρτ, lam, rotN, rot, Prod.mk_add_mk, Prod.mk.injEq] <;>
    constructor <;> ring

/-- The rotation commutes with the side isometries up to a tube shift. -/
theorem gmap_ρ {c j : ℕ} (hc : c < 2) (hj : j < 6) (z : ℤ × ℤ) :
    gmap p r s w c ((j + 2) % 6) (ρz r s c z) =
      gmap p r s w c j z + (lam c j * (2 * r + s), -(lam c j * (2 * r + s))) := by
  simp only [gmap, ρz]
  have hadd : ∀ (k : ℕ) (a b : ℤ × ℤ), rotN k (a + b) = rotN k a + rotN k b := by
    intro k a b
    induction k with
    | zero => rfl
    | succ k ih => simp only [rotN]; rw [ih]; simp only [rot]; ext <;> simp <;> ring
  have : (gk c ((j + 2) % 6) + 2) % 6 = gk c j := by
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> interval_cases j <;> rfl
  rw [hadd, rotN_add_mod, this, add_assoc, gτ_ρ hc hj, add_assoc]

theorem cross_shift (D : ℤ × ℤ) (l : ℤ) :
    cross D (l * (2 * r + s), -(l * (2 * r + s))) = (2 * r + s) * (-(l * (D.1 + D.2))) := by
  simp only [cross]; ring

theorem ρz3 (c : ℕ) (z : ℤ × ℤ) : ρz r s c (ρz r s c (ρz r s c z)) = z := by
  obtain ⟨x, y⟩ := z
  rcases Nat.eq_zero_or_pos c with rfl | h
  · simp only [ρz, ρτ, rotN, rot, Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring
  · have : ρτ r s c = (r + s, r) := by
      unfold ρτ; split <;> first | omega | rfl
    simp only [ρz, this, rotN, rot, Prod.mk_add_mk, Prod.mk.injEq]; constructor <;> ring

theorem ρS3 (c : ℕ) (x : (ℤ × ℤ) × ℤ) : ρS r s c (ρS r s c (ρS r s c x)) = x := by
  obtain ⟨⟨a, b⟩, E⟩ := x
  rcases Nat.eq_zero_or_pos c with rfl | h
  · simp only [ρS, ρτ, rotN, rot, cross, Prod.mk.injEq]; refine ⟨⟨by ring, by ring⟩, by ring⟩
  · have : ρτ r s c = (r + s, r) := by
      unfold ρτ; split <;> first | omega | rfl
    simp only [ρS, this, rotN, rot, cross, Prod.mk.injEq]; refine ⟨⟨by ring, by ring⟩, by ring⟩

theorem corner_ρ {c : ℕ} (hc : c < 2) (z : ℤ × ℤ) :
    CornerPos p r s w c (ρz r s c z) ↔ CornerPos p r s w c z := by
  constructor
  · intro h
    have := corner_ρ_fwd hc (corner_ρ_fwd hc h)
    rwa [ρz3] at this
  · exact corner_ρ_fwd hc

end Claude5E10
