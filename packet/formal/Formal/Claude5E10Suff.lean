import Formal.Claude5E10Deg4

/-!
# E10 model: literal paths straight up the tube

Written by a Claude worker (2026-10-20, E10 bridge session).

A zigzag `zz i = (u₀, −u₀) + ⌊i/2⌋ (0, 1) + (i mod 2) E` (tube chart) runs from the lower seam to
the upper seam.  With `E = (1, 0)` it joins the tube position `u₀` below to `u₀ + 1` above in
`4p` points (`pathR`); with `E = (−1, 1)` it joins `u₀` to `u₀ − 1` in `4p + 2` points
(`pathL`).  If the ends are corners and their path neighbours are not, it is a literal path.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

/-- The zigzag. -/
def zz (u₀ : ℤ) (E : ℤ × ℤ) (i : ℕ) : ℤ × ℤ :=
  (u₀ + ((i % 2 : ℕ) : ℤ) * E.1, -u₀ + ((i / 2 : ℕ) : ℤ) + ((i % 2 : ℕ) : ℤ) * E.2)

theorem zz_step1 (u₀ : ℤ) (E : ℤ × ℤ) (i : ℕ) :
    zz u₀ E (i + 1) - zz u₀ E i = E ∨ zz u₀ E (i + 1) - zz u₀ E i = (0, 1) - E := by
  rcases Nat.even_or_odd' i with ⟨k, rfl | rfl⟩
  · left
    simp only [zz, show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega,
      show 2 * k % 2 = 0 by omega, show 2 * k / 2 = k by omega]
    ext <;> simp
  · right
    simp only [zz, show (2 * k + 1 + 1) % 2 = 0 by omega, show (2 * k + 1 + 1) / 2 = k + 1 by omega,
      show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega]
    ext <;> simp <;> ring

theorem zz_step2 (u₀ : ℤ) (E : ℤ × ℤ) (i : ℕ) : zz u₀ E (i + 2) - zz u₀ E i = (0, 1) := by
  simp only [zz, show (i + 2) % 2 = i % 2 by omega, show (i + 2) / 2 = i / 2 + 1 by omega]
  ext <;> simp <;> ring

/-- A zigzag up the tube is a literal path when its ends are corners and their path neighbours
are not. -/
theorem tube_literal (H : Hyp p r s w) (u₀ : ℤ) (E : ℤ × ℤ) (n : ℕ) (hE : E ∈ unitVec)
    (hE' : (0, 1) - E ∈ unitVec) (hx : E.1 = 1 ∨ E.1 = -1) (hn : 4 ≤ n) (hev : Even n)
    (hdom : ∀ i, i < n → HT p (zz u₀ E i))
    (c0 : IsCornerV p r s w (ch p r s w 2 (zz u₀ E 0)))
    (c1 : ¬ IsCornerV p r s w (ch p r s w 2 (zz u₀ E 1)))
    (c2 : ¬ IsCornerV p r s w (ch p r s w 2 (zz u₀ E (n - 2))))
    (c3 : IsCornerV p r s w (ch p r s w 2 (zz u₀ E (n - 1)))) :
    ∃ n q, LiteralPath (GM p r s w) n q := by
  have hP : 0 < 3 * (2 * r + s) := by have := H.hr; have := H.hs; omega
  let q : ℕ → MS p r s := fun i => ⟨ch p r s w 2 (zz u₀ E (min i (n - 1))),
    ch_valid H.hp H.hr H.hs H.hw0 H.hw1 (by norm_num) (hdom _ (by omega))⟩
  have hq : ∀ i, i < n → (q i).1 = ch p r s w 2 (zz u₀ E i) := by
    intro i hi; simp only [q]; rw [min_eq_left (by omega)]
  have inT : ∀ i, i < n → InC p r s w 2 (q i).1 (zz u₀ E i) :=
    fun i hi => ⟨by norm_num, hdom i hi, (hq i hi).symm⟩
  have small : ∀ i j, -3 < (zz u₀ E j).1 - (zz u₀ E i).1 ∧ (zz u₀ E j).1 - (zz u₀ E i).1 < 3 := by
    intro i j
    have : ((i % 2 : ℕ) : ℤ) ≤ 1 := by have := Nat.mod_lt i (show 2 > 0 by norm_num); omega
    have : ((j % 2 : ℕ) : ℤ) ≤ 1 := by have := Nat.mod_lt j (show 2 > 0 by norm_num); omega
    simp only [zz]
    rcases hx with h | h <;> rw [h] <;> constructor <;> omega
  have hne : ∀ i j, i < n → j < n → (q i).1 = (q j).1 → i = j := by
    intro i j hi hj e
    have := (inC_near2 H (inT i hi) (inT j hj) (by have := (small i j).1; omega) (by have := (small i j).2; omega)).1 e
    simp only [zz, Prod.mk.injEq] at this
    obtain ⟨e1, e2⟩ := this
    have hi2 := Nat.mod_lt i (show 2 > 0 by norm_num)
    have hj2 := Nat.mod_lt j (show 2 > 0 by norm_num)
    have em : i % 2 = j % 2 := by
      rcases hx with h | h <;> rw [h] at e1 <;> omega
    rw [em] at e2
    have : i / 2 = j / 2 := by omega
    omega
  refine ⟨n, q, hn, hev, fun i j hi hj e => hne i j hi hj (congrArg Subtype.val e), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    refine adj_of_chart (inT i (by omega)) (inT (i + 1) hi) ?_ (fun e => by
      have := hne i (i + 1) (by omega) hi e; omega)
    rcases zz_step1 u₀ E i with h | h <;> rw [h]
    exacts [hE, hE']
  · intro i hi
    refine adj_of_chart (inT i (by omega)) (inT (i + 2) hi) (by rw [zz_step2]; simp [unitVec])
      (fun e => by have := hne i (i + 2) (by omega) hi e; omega)
  · rcases deg_cases H (q 0) with ⟨-, h⟩ | ⟨h1, -⟩
    · exact h
    · exact absurd (by rw [hq 0 (by omega)]; exact c0) h1
  · rcases deg_cases H (q (n - 1)) with ⟨-, h⟩ | ⟨h1, -⟩
    · exact h
    · exact absurd (by rw [hq (n - 1) (by omega)]; exact c3) h1
  · rcases deg_cases H (q 1) with ⟨h1, -⟩ | ⟨-, h⟩
    · exact absurd (by rw [← hq 1 (by omega)]; exact h1) c1
    · exact h
  · rcases deg_cases H (q (n - 2)) with ⟨h1, -⟩ | ⟨-, h⟩
    · exact absurd (by rw [← hq (n - 2) (by omega)]; exact h1) c2
    · exact h

end Claude5E10
