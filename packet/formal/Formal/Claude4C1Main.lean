import Formal.Claude4C1Nec
import Formal.Claude4C1Suff

/-!
# C1: classification and rays

Written by a Claude worker (2026-10-20, C1 bridge session).

* `no_path_g4`, `c1_no_path` : no literal path for `r ≥ 1`, `s ≥ 2`;
* `c1_classification` : for `r, s ≥ 1`, a literal path exists in `c1Graph r s` iff `s = 1`;
* `c1_rays`           : on every ray `(r₀ + a t, s₀ + b t)`, existence is eventually constant
                        (`t₀ = 1`, period `1`).
-/

set_option linter.unusedSimpArgs false

namespace Claude4C1

open ClaudeChallenge Claude2Aligned

variable {r s : ℕ}

def σ23 : Equiv.Perm (Fin 4) := Equiv.swap 2 3

macro "mir_tac" : tactic =>
  `(tactic| (funext t; fin_cases t <;> simp [pm, σ23, Equiv.swap_apply_def, C01, B0, B1, B2, B3, B4]))

theorem mC01 : pm σ23 (C01 r s) = C01 r s := by mir_tac
theorem mB0 : pm σ23 (B0 r s) = B0 r s := by mir_tac
theorem mB1 : pm σ23 (B1 r s) = B4 r s := by mir_tac
theorem mB2 : pm σ23 (B2 r s) = B3 r s := by mir_tac
theorem mB3 : pm σ23 (B3 r s) = B2 r s := by mir_tac
theorem mB4 : pm σ23 (B4 r s) = B1 r s := by mir_tac

theorem no_mirror (hr : 1 ≤ r) (hs : 2 ≤ s) {n : ℕ} {p : ℕ → Surf r s}
    (hp : LiteralPath (G4 r s) n p) (h0 : (p 0).1 = C01 r s) {x1 x2 : Fin 4 → ℤ}
    (h1 : (p 1).1 = x1) (h2 : (p 2).1 = x2)
    (h : (pm σ23 x1 = B0 r s ∧ pm σ23 x2 = B1 r s) ∨ (pm σ23 x1 = B1 r s ∧ pm σ23 x2 = B2 r s) ∨
      (pm σ23 x1 = B1 r s ∧ pm σ23 x2 = B0 r s) ∨ (pm σ23 x1 = B2 r s ∧ pm σ23 x2 = B3 r s) ∨
      (pm σ23 x1 = B2 r s ∧ pm σ23 x2 = B1 r s)) : False := by
  refine no_canon hr hs (literal_pm σ23 hp) ?_ ?_
  · show pm σ23 (p 0).1 = C01 r s
    rw [h0, mC01]
  · have e1 : ((pmE σ23) (p 1)).1 = pm σ23 x1 := by rw [← h1]; rfl
    have e2 : ((pmE σ23) (p 2)).1 = pm σ23 x2 := by rw [← h2]; rfl
    rw [e1, e2]; exact h

theorem nec0 (hr : 1 ≤ r) (hs : 2 ≤ s) {n : ℕ} {p : ℕ → Surf r s}
    (hp : LiteralPath (G4 r s) n p) (h0 : (p 0).1 = C01 r s) : False := by
  have hp' := hp
  obtain ⟨h4, -, -, ha1, ha2, -⟩ := hp'
  have a1 : AdjR r s (C01 r s) (p 1).1 := h0 ▸ ha1 0 (by omega)
  have a2 : AdjR r s (C01 r s) (p 2).1 := h0 ▸ ha2 0 (by omega)
  have a12 : AdjR r s (p 1).1 (p 2).1 := ha1 1 (by omega)
  have hr1 : 1 ≤ r := hr
  have hs1 : 1 ≤ s := by omega
  rcases nbr_C01 (p 1).2 a1 with e1 | e1 | e1 | e1 | e1 <;>
  rcases nbr_C01 (p 2).2 a2 with e2 | e2 | e2 | e2 | e2 <;>
  rw [e1, e2] at a12
  -- p1 = B0
  · exact adjR_ne a12 rfl
  · exact no_canon hr hs hp h0 (Or.inl ⟨e1, e2⟩)
  · exact na02 a12
  · exact na03 a12
  · exact no_mirror hr hs hp h0 e1 e2 (Or.inl ⟨mB0, mB4⟩)
  -- p1 = B1
  · exact no_canon hr hs hp h0 (Or.inr (Or.inr (Or.inl ⟨e1, e2⟩)))
  · exact adjR_ne a12 rfl
  · exact no_canon hr hs hp h0 (Or.inr (Or.inl ⟨e1, e2⟩))
  · exact na13 a12
  · exact na14 hr1 hs1 a12
  -- p1 = B2
  · exact na02 (adjR_symm a12)
  · exact no_canon hr hs hp h0 (Or.inr (Or.inr (Or.inr (Or.inr ⟨e1, e2⟩))))
  · exact adjR_ne a12 rfl
  · exact no_canon hr hs hp h0 (Or.inr (Or.inr (Or.inr (Or.inl ⟨e1, e2⟩))))
  · exact na24 a12
  -- p1 = B3
  · exact na03 (adjR_symm a12)
  · exact na13 (adjR_symm a12)
  · exact no_mirror hr hs hp h0 e1 e2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨mB3, mB2⟩))))
  · exact adjR_ne a12 rfl
  · exact no_mirror hr hs hp h0 e1 e2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨mB3, mB4⟩))))
  -- p1 = B4
  · exact no_mirror hr hs hp h0 e1 e2 (Or.inr (Or.inr (Or.inl ⟨mB4, mB0⟩)))
  · exact na14 hr1 hs1 (adjR_symm a12)
  · exact na24 (adjR_symm a12)
  · exact no_mirror hr hs hp h0 e1 e2 (Or.inr (Or.inl ⟨mB4, mB3⟩))
  · exact adjR_ne a12 rfl

/-- **Necessity** in the model. -/
theorem no_path_g4 (hr : 1 ≤ r) (hs : 2 ≤ s) : ¬ ∃ n p, LiteralPath (G4 (r : ℤ) (s : ℤ)) n p := by
  rintro ⟨n, p, hp⟩
  have hc : CornerP r s (p 0).1 := by
    have d0 := hp.2.2.2.2.2.1
    rw [deg_g4 (by omega) (by omega)] at d0
    by_contra h
    rw [if_neg h] at d0
    omega
  obtain ⟨σ, hσ⟩ := corner_norm hr (by omega) (p 0).2 hc
  exact nec0 hr hs (literal_pm σ hp) hσ

/-- **Necessity**: C1(r,s) has no literal path for `r ≥ 1`, `s ≥ 2`. -/
theorem c1_no_path (hr : 1 ≤ r) (hs : 2 ≤ s) :
    ¬ ∃ n p, LiteralPath (c1Graph (r : ℤ) (s : ℤ)) n p := fun h =>
  no_path_g4 hr hs ((c1_iff_g4 (by omega) (by omega)).1 h)

/-- **C1 classification**: for `r, s ≥ 1`, a literal path exists iff `s = 1`. -/
theorem c1_classification (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    (∃ n p, LiteralPath (c1Graph (r : ℤ) (s : ℤ)) n p) ↔ s = 1 := by
  constructor
  · intro h
    by_contra hs1
    exact c1_no_path hr (by omega) h
  · rintro rfl
    exact c1_path_s1 r hr

/-- **C1 on rays** (from the classification). -/
theorem c1_rays (r₀ s₀ a b : ℕ) (hr : 1 ≤ r₀) (hs : 1 ≤ s₀) :
    ∃ t₀ P : ℕ, 0 < P ∧ ∀ t : ℕ, t₀ ≤ t →
      ((∃ n p, LiteralPath (c1Graph ((r₀ + a * t : ℕ) : ℤ) ((s₀ + b * t : ℕ) : ℤ)) n p) ↔
        (∃ n p, LiteralPath (c1Graph ((r₀ + a * (t + P) : ℕ) : ℤ)
          ((s₀ + b * (t + P) : ℕ) : ℤ)) n p)) := by
  refine ⟨1, 1, by norm_num, fun t ht => ?_⟩
  rw [c1_classification _ _ (by nlinarith) (by nlinarith),
    c1_classification _ _ (by nlinarith) (by nlinarith)]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · have h1 : 1 ≤ b * t := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    have h2 : 1 ≤ b * (t + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    constructor <;> intro h <;> omega

end Claude4C1
