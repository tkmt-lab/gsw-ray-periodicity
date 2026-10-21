import Formal.Claude5E10Class
import Formal.Claude5E10Ray

/-!
# E10: the classification in the statement's form, and rays with `r ≥ 2` eventually

Written by a Claude worker (2026-10-20, E10 bridge session).

* `classification_int` : for `p ≥ 1`, `r ≥ 2`, `s ≥ 1`, a literal path exists iff
  `p ≡ d ± 1 (mod 2r + s)` for some `d ∈ {0, r, r + s}`;
* `rays_A` : on a ray with `b ≥ 1` or `r₀ ≥ 2`, path existence is eventually periodic.
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

theorem modeq_iff {p e v m : ℤ} (hm : 0 < m) (hv : e % m = v) : p ≡ e [ZMOD m] ↔ p % m = v := by
  unfold Int.ModEq; rw [hv]

theorem emod_val {e v m : ℤ} (hm : 0 < m) (q : ℤ) (h : e = v + m * q) (h0 : 0 ≤ v) (h1 : v < m) :
    e % m = v := emod_eq_of hm (q := q) (by rw [h]; ring) h0 h1

/-- **Classification**, statement form (integers). -/
theorem classification_int {p r s : ℤ} (hp : 1 ≤ p) (hr : 2 ≤ r) (hs : 1 ≤ s) :
    (∃ n q, LiteralPath (e10Graph p r s) n q) ↔
      ∃ d : ℤ, (d = 0 ∨ d = r ∨ d = r + s) ∧
        (p ≡ d + 1 [ZMOD 2 * r + s] ∨ p ≡ d - 1 [ZMOD 2 * r + s]) := by
  have hm : 0 < 2 * r + s := by omega
  rw [e10_classify hp hr hs]
  constructor
  · rintro (h | h | h | h | h | h)
    · exact ⟨0, Or.inl rfl, Or.inl ((modeq_iff hm (emod_val hm 0 (by ring) (by omega) (by omega))).2 h)⟩
    · exact ⟨r, Or.inr (Or.inl rfl), Or.inl ((modeq_iff hm (emod_val hm 0 (by ring) (by omega) (by omega))).2 h)⟩
    · exact ⟨r + s, Or.inr (Or.inr rfl), Or.inl ((modeq_iff hm (emod_val hm 0 (by ring) (by omega) (by omega))).2 h)⟩
    · exact ⟨0, Or.inl rfl, Or.inr ((modeq_iff hm (emod_val hm (-1) (by ring) (by omega) (by omega))).2 h)⟩
    · exact ⟨r, Or.inr (Or.inl rfl), Or.inr ((modeq_iff hm (emod_val hm 0 (by ring) (by omega) (by omega))).2 h)⟩
    · exact ⟨r + s, Or.inr (Or.inr rfl), Or.inr ((modeq_iff hm (emod_val hm 0 (by ring) (by omega) (by omega))).2 h)⟩
  · rintro ⟨d, hd, h | h⟩ <;> rcases hd with rfl | rfl | rfl
    · left; exact (modeq_iff hm (emod_val hm 0 (by ring) (by omega) (by omega))).1 h
    · right; left; exact (modeq_iff hm (emod_val hm 0 (by ring) (by omega) (by omega))).1 h
    · right; right; left; exact (modeq_iff hm (emod_val hm 0 (by ring) (by omega) (by omega))).1 h
    · right; right; right; left
      exact (modeq_iff hm (emod_val hm (-1) (by ring) (by omega) (by omega))).1 h
    · right; right; right; right; left
      exact (modeq_iff hm (emod_val hm 0 (by ring) (by omega) (by omega))).1 h
    · right; right; right; right; right
      exact (modeq_iff hm (emod_val hm 0 (by ring) (by omega) (by omega))).1 h

theorem emod_iff_dvd {p v m : ℤ} (hm : 0 < m) (h0 : 0 ≤ v) (h1 : v < m) :
    p % m = v ↔ m ∣ p - v := by
  constructor
  · intro h; exact ⟨p / m, by have := Int.mul_ediv_add_emod p m; linarith⟩
  · intro h
    obtain ⟨q, hq⟩ := h
    exact emod_eq_of hm (q := q) (by linarith) h0 h1

/-- Path existence for `r ≥ 2` as six divisibilities. -/
theorem path_iff_dvd {p r s : ℤ} (hp : 1 ≤ p) (hr : 2 ≤ r) (hs : 1 ≤ s) :
    (∃ n q, LiteralPath (e10Graph p r s) n q) ↔
      ((2 * r + s) ∣ p - 1 ∨ (2 * r + s) ∣ p - (r + 1) ∨ (2 * r + s) ∣ p - (r + s + 1) ∨
        (2 * r + s) ∣ p + 1 ∨ (2 * r + s) ∣ p - (r - 1) ∨ (2 * r + s) ∣ p - (r + s - 1)) := by
  have hm : 0 < 2 * r + s := by omega
  rw [e10_classify hp hr hs, emod_iff_dvd hm (by omega) (by omega), emod_iff_dvd hm (by omega) (by omega),
    emod_iff_dvd hm (by omega) (by omega), emod_iff_dvd hm (by omega) (by omega),
    emod_iff_dvd hm (by omega) (by omega), emod_iff_dvd hm (by omega) (by omega)]
  have e : (2 * r + s) ∣ p - (2 * r + s - 1) ↔ (2 * r + s) ∣ p + 1 := by
    rw [show p - (2 * r + s - 1) = (p + 1) - (2 * r + s) by ring]; exact dvd_sub_self_right
  rw [e]

/-- **Rays on which `r ≥ 2` eventually.** -/
theorem rays_A (p₀ r₀ s₀ a b c : ℕ) (hp : 1 ≤ p₀) (hr : 1 ≤ r₀) (hs : 1 ≤ s₀)
    (hb : 1 ≤ b ∨ 2 ≤ r₀) :
    EvPer (fun n : ℕ => ∃ k q, LiteralPath (e10Graph ((p₀ + a * n : ℕ) : ℤ) ((r₀ + b * n : ℕ) : ℤ)
      ((s₀ + c * n : ℕ) : ℤ)) k q) := by
  -- the six divisibilities along the ray
  have hM : ∀ n : ℕ, (0 : ℤ) < (2 * r₀ + s₀ : ℤ) + (2 * b + c : ℤ) * n := by intro n; positivity
  let D := fun (l₀ lam : ℤ) => fun n : ℕ =>
    ((2 * r₀ + s₀ : ℤ) + (2 * b + c : ℤ) * n) ∣ (l₀ + lam * n)
  have hD : ∀ l₀ lam, EvPer (D l₀ lam) := fun l₀ lam =>
    evper_dvd _ _ l₀ lam (by positivity) hM
  have h6 := evper_or (hD (p₀ - 1) a) (evper_or (hD (p₀ - (r₀ + 1)) (a - b))
    (evper_or (hD (p₀ - (r₀ + s₀ + 1)) (a - b - c)) (evper_or (hD (p₀ + 1) a)
      (evper_or (hD (p₀ - (r₀ - 1)) (a - b)) (hD (p₀ - (r₀ + s₀ - 1)) (a - b - c))))))
  refine evper_congr h6 1 (fun n hn => ?_)
  have hr2 : (2 : ℤ) ≤ ((r₀ + b * n : ℕ) : ℤ) := by
    push_cast; rcases hb with hb | hb <;> nlinarith
  rw [path_iff_dvd (by push_cast; nlinarith) hr2 (by push_cast; nlinarith)]
  have e0 : 2 * ((r₀ + b * n : ℕ) : ℤ) + ((s₀ + c * n : ℕ) : ℤ) = (2 * r₀ + s₀ : ℤ) + (2 * b + c : ℤ) * n := by
    push_cast; ring
  have e1 : ((p₀ + a * n : ℕ) : ℤ) - 1 = ((p₀ : ℤ) - 1) + (a : ℤ) * n := by push_cast; ring
  have e2 : ((p₀ + a * n : ℕ) : ℤ) - (((r₀ + b * n : ℕ) : ℤ) + 1) = ((p₀ : ℤ) - (r₀ + 1)) + ((a : ℤ) - b) * n := by
    push_cast; ring
  have e3 : ((p₀ + a * n : ℕ) : ℤ) - (((r₀ + b * n : ℕ) : ℤ) + ((s₀ + c * n : ℕ) : ℤ) + 1) =
      ((p₀ : ℤ) - (r₀ + s₀ + 1)) + ((a : ℤ) - b - c) * n := by push_cast; ring
  have e4 : ((p₀ + a * n : ℕ) : ℤ) + 1 = ((p₀ : ℤ) + 1) + (a : ℤ) * n := by push_cast; ring
  have e5 : ((p₀ + a * n : ℕ) : ℤ) - (((r₀ + b * n : ℕ) : ℤ) - 1) = ((p₀ : ℤ) - (r₀ - 1)) + ((a : ℤ) - b) * n := by
    push_cast; ring
  have e6 : ((p₀ + a * n : ℕ) : ℤ) - (((r₀ + b * n : ℕ) : ℤ) + ((s₀ + c * n : ℕ) : ℤ) - 1) =
      ((p₀ : ℤ) - (r₀ + s₀ - 1)) + ((a : ℤ) - b - c) * n := by push_cast; ring
  rw [e0, e1, e2, e3, e4, e5, e6]

end Claude5E10
