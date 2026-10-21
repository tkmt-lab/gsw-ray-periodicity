import Formal.Claude5E10Suff

/-!
# E10 model: sufficiency for `r ≥ 2`

Written by a Claude worker (2026-10-20, E10 bridge session).

A lower corner at tube position `u₀` and an upper corner at `u₀ + 1` (`pathR`) or `u₀ − 1`
(`pathL`, `r ≥ 2`) are joined by a literal path straight up the tube.  With the twist
`w = j m + k`, such a pair exists exactly when `k ≡ d ± 1 (mod m)`, `d ∈ {0, r, r + s}`
(`suff_model`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

theorem chT_val (z : ℤ × ℤ) : ch p r s w 2 z = (2, (z.1 % (3 * (2 * r + s)), z.1 + z.2)) := rfl

theorem not_corner_mid (H : Hyp p r s w) {x h : ℤ} (h0 : h ≠ 0) (h1 : h ≠ 2 * p) :
    ¬ IsCornerV p r s w (2, (x, h)) := by
  rintro (⟨a, -, e⟩ | ⟨a, -, e⟩) <;> simp only [Prod.mk.injEq] at e <;> omega

theorem zz_even (u₀ : ℤ) (E : ℤ × ℤ) (k : ℕ) : zz u₀ E (2 * k) = (u₀, -u₀ + k) := by
  simp only [zz, show 2 * k % 2 = 0 by omega, show 2 * k / 2 = k by omega]; ext <;> simp

theorem zz_odd (u₀ : ℤ) (E : ℤ × ℤ) (k : ℕ) :
    zz u₀ E (2 * k + 1) = (u₀ + E.1, -u₀ + k + E.2) := by
  simp only [zz, show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega]
  ext <;> simp

theorem cornerV_low {x y u : ℤ} (hx : x = u) (hy : y = 0) (hu : IsArc r s u) :
    IsCornerV p r s w (2, (x, y)) := Or.inl ⟨u, hu, by rw [hx, hy]⟩

theorem cornerV_up {x y a : ℤ} (hx : x = wrap r s (a + w)) (hy : y = 2 * p) (ha : IsArc r s a) :
    IsCornerV p r s w (2, (x, y)) := Or.inr ⟨a, ha, by rw [hx, hy]⟩

theorem pathR (H : Hyp p r s w) {u₀ a : ℤ} (hu : IsArc r s u₀) (ha : IsArc r s a)
    (hup : wrap r s (a + w) = (u₀ + 1) % (3 * (2 * r + s))) :
    ∃ n q, LiteralPath (GM p r s w) n q := by
  have hp := H.hp; have hr := H.hr; have hs := H.hs
  have hu' := arc_range hr hs hu
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = p := ⟨p.toNat, by omega⟩
  refine tube_literal H u₀ (1, 0) (4 * N) (by simp [unitVec]) (by simp [unitVec]) (Or.inl rfl)
    (by omega) ⟨2 * N, by ring⟩ ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [HT, zz]
    have := Nat.mod_lt i (show 2 > 0 by norm_num)
    have : i / 2 < 2 * N := by omega
    constructor <;> push_cast <;> omega
  · rw [show (0 : ℕ) = 2 * 0 by rfl, zz_even, chT_val]
    exact cornerV_low (Int.emod_eq_of_lt hu'.1 hu'.2) (by simp) hu
  · apply not_corner_mid H <;> simp [zz] <;> omega
  · rw [show 4 * N - 2 = 2 * (2 * N - 1) by omega]
    apply not_corner_mid H <;> simp [zz, show 2 * (2 * N - 1) / 2 = 2 * N - 1 by omega] <;>
      push_cast [show 1 ≤ 2 * N by omega] <;> omega
  · rw [show 4 * N - 1 = 2 * (2 * N - 1) + 1 by omega, zz_odd, chT_val]
    refine cornerV_up (by rw [hup]) ?_ ha
    push_cast [show 1 ≤ 2 * N by omega]; omega

theorem arc_gap (hr : 2 ≤ r) (hs : 1 ≤ s) {a a' : ℤ} (ha : IsArc r s a) (ha' : IsArc r s a') :
    a' - a ≠ 1 ∧ a' - a ≠ 1 - 3 * (2 * r + s) ∧ a' - a ≠ -1 ∧ a' - a ≠ 3 * (2 * r + s) - 1 := by
  simp only [IsArc] at ha ha'
  omega

theorem pathL (H : Hyp p r s w) (hr2 : 2 ≤ r) {u₀ a : ℤ} (hu : IsArc r s u₀) (ha : IsArc r s a)
    (hup : wrap r s (a + w) = (u₀ + -1) % (3 * (2 * r + s))) :
    ∃ n q, LiteralPath (GM p r s w) n q := by
  have hp := H.hp; have hr := H.hr; have hs := H.hs; have := H.hw0; have := H.hw1
  have hP : 0 < 3 * (2 * r + s) := by omega
  have hu' := arc_range hr hs hu
  have ha' := arc_range hr hs ha
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = p := ⟨p.toNat, by omega⟩
  -- the residue of u₀ − 1
  have hm1 : (u₀ + -1) % (3 * (2 * r + s)) = u₀ - 1 ∨
      ((u₀ + -1) % (3 * (2 * r + s)) = 3 * (2 * r + s) - 1 ∧ u₀ = 0) := by
    by_cases h0 : u₀ = 0
    · right; rw [h0]; exact ⟨emod_eq_of hP (q := -1) (by ring) (by omega) (by omega), rfl⟩
    · left; exact emod_eq_of hP (q := 0) (by ring) (by omega) (by omega)
  refine tube_literal H u₀ (-1, 1) (4 * N + 2) (by simp [unitVec]) (by simp [unitVec])
    (Or.inr rfl) (by omega) ⟨2 * N + 1, by ring⟩ ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [HT, zz]
    have := Nat.mod_lt i (show 2 > 0 by norm_num)
    have : i / 2 ≤ 2 * N := by omega
    constructor <;> push_cast <;> omega
  · rw [show (0 : ℕ) = 2 * 0 by rfl, zz_even, chT_val]
    exact cornerV_low (Int.emod_eq_of_lt hu'.1 hu'.2) (by simp) hu
  · rw [show (1 : ℕ) = 2 * 0 + 1 by rfl, zz_odd, chT_val]
    simp only [Nat.cast_zero]
    rw [show u₀ + -1 + (-u₀ + 0 + 1) = 0 by ring, corner_low H]
    intro hc
    rcases hm1 with e | ⟨e, e'⟩ <;> rw [e] at hc
    · exact (arc_gap hr2 hs hu hc).2.2.1 (by ring)
    · exact (arc_gap hr2 hs hu hc).2.2.2 (by rw [e']; ring)
  · rw [show 4 * N + 2 - 2 = 2 * (2 * N) by omega, zz_even, chT_val]
    rw [Int.emod_eq_of_lt hu'.1 hu'.2, show u₀ + (-u₀ + ((2 * N : ℕ) : ℤ)) = 2 * p by
      push_cast; rw [← hN]; ring, corner_up H hu'.1 hu'.2]
    intro hc
    have e1 := (unwrapU_spec H hu'.1 hu'.2).2.2
    have g := arc_gap hr2 hs ha hc
    have l2 := arc_range hr hs hc
    unfold wrap at hup e1
    rcases hm1 with e | ⟨e, e'⟩ <;> rw [e] at hup <;> split_ifs at hup e1 <;> omega
  · rw [show 4 * N + 2 - 1 = 2 * (2 * N) + 1 by omega, zz_odd, chT_val]
    refine cornerV_up (by rw [hup]) ?_ ha
    push_cast; omega

end Claude5E10
