import Formal.Claude5E10Model
import Mathlib.Tactic.Ring

/-!
# E10 model: the boundaries parametrised, injectivity, how the charts meet

Written by a Claude worker (2026-10-20, E10 bridge session).

* `PL l`, `PU l` : the boundary point of the lower / upper cap at arclength `l`;
* `aL_inj`, `aU_inj`, `chL_inj`, `chU_inj` : the caps are injective;
* `chT_eq` : two tube chart points give the same vertex iff they differ by a period
  `(3m, -3m)`;
* `chLT`, `chUT` : a vertex in a cap chart and in the tube is a seam point;
* `unit_PL`, `unit_PU` : boundary points are a unit apart iff their arclengths are neighbours.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

/-- The boundary point of the lower cap at clockwise arclength `l`. -/
def PL (r s l : ℤ) : ℤ × ℤ :=
  if l ≤ r + s then (-l, l) else if l ≤ 2 * r + s then (-(r + s), l)
  else if l ≤ 3 * r + 2 * s then (l - 3 * r - 2 * s, 2 * r + s)
  else if l ≤ 4 * r + 2 * s then (l - 3 * r - 2 * s, 5 * r + 3 * s - l)
  else if l ≤ 5 * r + 3 * s then (r, 5 * r + 3 * s - l)
  else (6 * r + 3 * s - l, 0)

/-- The boundary point of the upper cap at counterclockwise arclength `l`. -/
def PU (r s l : ℤ) : ℤ × ℤ :=
  if l ≤ r + s then (l, 0) else if l ≤ 2 * r + s then (r + s, l - r - s)
  else if l ≤ 3 * r + 2 * s then (3 * r + 2 * s - l, l - r - s)
  else if l ≤ 4 * r + 2 * s then (3 * r + 2 * s - l, 2 * r + s)
  else if l ≤ 5 * r + 3 * s then (-r, 6 * r + 3 * s - l)
  else (l - 6 * r - 3 * s, 6 * r + 3 * s - l)

theorem PL_spec (hr : 1 ≤ r) (hs : 1 ≤ s) {l : ℤ} (h0 : 0 ≤ l) (h1 : l < 3 * (2 * r + s)) :
    HL r s (PL r s l) ∧ ¬ IL r s (PL r s l) ∧ aL r s (PL r s l) = l := by
  unfold PL
  split_ifs <;> simp only [HL, IL, aL] <;> refine ⟨by omega, by omega, ?_⟩ <;> split_ifs <;>
    e10om

theorem PU_spec (hr : 1 ≤ r) (hs : 1 ≤ s) {l : ℤ} (h0 : 0 ≤ l) (h1 : l < 3 * (2 * r + s)) :
    HU r s (PU r s l) ∧ ¬ IU r s (PU r s l) ∧ aU r s (PU r s l) = l := by
  unfold PU
  split_ifs <;> simp only [HU, IU, aU] <;> refine ⟨by omega, by omega, ?_⟩ <;> split_ifs <;>
    e10om

theorem aL_inj (hr : 1 ≤ r) (hs : 1 ≤ s) {z z' : ℤ × ℤ} (h : HL r s z) (hb : ¬ IL r s z)
    (h' : HL r s z') (hb' : ¬ IL r s z') (e : aL r s z = aL r s z') : z = z' := by
  have c1 := bdL_cases h hb
  have c2 := bdL_cases h' hb'
  simp only [HL] at h h'
  obtain ⟨x, y⟩ := z
  obtain ⟨x', y'⟩ := z'
  simp only at c1 c2 h h' ⊢
  unfold aL at e
  simp only at e
  split_ifs at e <;> (simp only [Prod.mk.injEq]; omega)

theorem aU_inj (hr : 1 ≤ r) (hs : 1 ≤ s) {z z' : ℤ × ℤ} (h : HU r s z) (hb : ¬ IU r s z)
    (h' : HU r s z') (hb' : ¬ IU r s z') (e : aU r s z = aU r s z') : z = z' := by
  have c1 := bdU_cases h hb
  have c2 := bdU_cases h' hb'
  simp only [HU] at h h'
  obtain ⟨x, y⟩ := z
  obtain ⟨x', y'⟩ := z'
  simp only at c1 c2 h h' ⊢
  unfold aU at e
  simp only at e
  split_ifs at e <;> (simp only [Prod.mk.injEq]; omega)

theorem eq_PL (hr : 1 ≤ r) (hs : 1 ≤ s) {z : ℤ × ℤ} (h : HL r s z) (hb : ¬ IL r s z) :
    z = PL r s (aL r s z) := by
  have hl := aL_range hr hs h hb
  have := PL_spec hr hs hl.1 hl.2
  exact aL_inj hr hs h hb this.1 this.2.1 this.2.2.symm

theorem eq_PU (hr : 1 ≤ r) (hs : 1 ≤ s) {z : ℤ × ℤ} (h : HU r s z) (hb : ¬ IU r s z) :
    z = PU r s (aU r s z) := by
  have hl := aU_range hr hs h hb
  have := PU_spec hr hs hl.1 hl.2
  exact aU_inj hr hs h hb this.1 this.2.1 this.2.2.symm

theorem wrap_inj (hr : 1 ≤ r) (hs : 1 ≤ s) {x y : ℤ} (hx0 : 0 ≤ x) (hx1 : x < 6 * (2 * r + s))
    (hy0 : 0 ≤ y) (hy1 : y < 6 * (2 * r + s)) (h : wrap r s x = wrap r s y)
    (hx : x < 3 * (2 * r + s) ↔ y < 3 * (2 * r + s)) : x = y := by
  unfold wrap at h; split_ifs at h <;> omega

theorem wrap_eq_iff (hr : 1 ≤ r) (hs : 1 ≤ s) {x y : ℤ} (hx0 : 0 ≤ x)
    (hx1 : x < 6 * (2 * r + s)) (hy0 : 0 ≤ y) (hy1 : y < 3 * (2 * r + s)) :
    wrap r s x = y ↔ (x = y ∨ x = y + 3 * (2 * r + s)) := by
  unfold wrap; split_ifs <;> omega

theorem chL_inj (hr : 1 ≤ r) (hs : 1 ≤ s) {z z' : ℤ × ℤ} (hz : HL r s z) (hz' : HL r s z')
    (h : ch p r s w 0 z = ch p r s w 0 z') : z = z' := by
  by_cases h1 : IL r s z <;> by_cases h1' : IL r s z'
  · rw [chL_I h1, chL_I h1'] at h; exact congrArg Prod.snd h
  · rw [chL_I h1, chL_B h1'] at h; simp at h
  · rw [chL_B h1, chL_I h1'] at h; simp at h
  · rw [chL_B h1, chL_B h1'] at h
    simp only [Prod.mk.injEq, true_and, and_true] at h
    exact aL_inj hr hs hz h1 hz' h1' h

theorem chU_inj (hr : 1 ≤ r) (hs : 1 ≤ s) (hw0 : 0 ≤ w) (hw1 : w < 3 * (2 * r + s))
    {z z' : ℤ × ℤ} (hz : HU r s z) (hz' : HU r s z')
    (h : ch p r s w 1 z = ch p r s w 1 z') : z = z' := by
  by_cases h1 : IU r s z <;> by_cases h1' : IU r s z'
  · rw [chU_I h1, chU_I h1'] at h; exact congrArg Prod.snd h
  · rw [chU_I h1, chU_B h1'] at h; simp at h
  · rw [chU_B h1, chU_I h1'] at h; simp at h
  · rw [chU_B h1, chU_B h1'] at h
    simp only [Prod.mk.injEq, true_and, and_true] at h
    have a1 := aU_range hr hs hz h1
    have a2 := aU_range hr hs hz' h1'
    apply aU_inj hr hs hz h1 hz' h1'
    unfold wrap at h; split_ifs at h <;> omega

/-! ## The tube chart -/

/-- The tube period. -/
def per (r s : ℤ) : ℤ × ℤ := (3 * (2 * r + s), -(3 * (2 * r + s)))

theorem chT_eq {z z' : ℤ × ℤ} :
    ch p r s w 2 z = ch p r s w 2 z' ↔
      z.1 + z.2 = z'.1 + z'.2 ∧ z.1 % (3 * (2 * r + s)) = z'.1 % (3 * (2 * r + s)) := by
  simp only [chT, Prod.mk.injEq, true_and]; tauto

theorem chT_shift (z : ℤ × ℤ) (t : ℤ) :
    ch p r s w 2 (z + t • per r s) = ch p r s w 2 z := by
  rw [chT_eq]
  simp only [per, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul]
  refine ⟨by ring, ?_⟩
  rw [show z.1 + t * (3 * (2 * r + s)) = z.1 + (3 * (2 * r + s)) * t by ring,
    Int.add_mul_emod_self_left]

theorem HT_shift {z : ℤ × ℤ} (t : ℤ) (h : HT p z) : HT p (z + t • per r s) := by
  simp only [HT, per, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul] at h ⊢
  constructor <;> nlinarith [h.1, h.2]

/-- Two tube points of one vertex differ by a multiple of the period. -/
theorem chT_rep (hr : 1 ≤ r) (hs : 1 ≤ s) {z z' : ℤ × ℤ}
    (h : ch p r s w 2 z = ch p r s w 2 z') : ∃ t : ℤ, z' = z + t • per r s := by
  rw [chT_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hd : (3 * (2 * r + s)) ∣ z'.1 - z.1 := Int.ModEq.dvd h2
  obtain ⟨t, ht⟩ := hd
  refine ⟨t, ?_⟩
  obtain ⟨a, b⟩ := z
  obtain ⟨a', b'⟩ := z'
  simp only [per, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq] at h1 ht ⊢
  constructor <;> linarith

/-- A multiple of the period that is small is zero. -/
theorem per_small (hr : 1 ≤ r) (hs : 1 ≤ s) {t : ℤ} (h1 : -6 < t * (3 * (2 * r + s)))
    (h2 : t * (3 * (2 * r + s)) < 6) : t = 0 := by
  rcases lt_trichotomy t 0 with h | h | h
  · nlinarith
  · exact h
  · nlinarith

/-- Two nearby tube points of one vertex are equal. -/
theorem chT_near (hr : 1 ≤ r) (hs : 1 ≤ s) {z z' : ℤ × ℤ}
    (h : ch p r s w 2 z = ch p r s w 2 z') (h1 : -6 < z'.1 - z.1) (h2 : z'.1 - z.1 < 6) :
    z = z' := by
  obtain ⟨t, rfl⟩ := chT_rep hr hs h
  have : t = 0 := by
    apply per_small hr hs <;>
      simp only [per, Prod.fst_add, Prod.smul_mk, smul_eq_mul] at h1 h2 <;> linarith
  subst this; simp

/-! ## Charts meeting -/

theorem chL_ne_U (hp : 1 ≤ p) {z z' : ℤ × ℤ} : ch p r s w 0 z ≠ ch p r s w 1 z' := by
  by_cases h1 : IL r s z <;> by_cases h1' : IU r s z'
  · rw [chL_I h1, chU_I h1']; simp
  · rw [chL_I h1, chU_B h1']; simp
  · rw [chL_B h1, chU_I h1']; simp
  · rw [chL_B h1, chU_B h1']; simp; omega

/-- A vertex in the lower cap and in the tube is a lower seam point. -/
theorem chLT {z z' : ℤ × ℤ} (h : ch p r s w 0 z = ch p r s w 2 z') :
    ¬ IL r s z ∧ z'.1 + z'.2 = 0 ∧ z'.1 % (3 * (2 * r + s)) = aL r s z := by
  by_cases h1 : IL r s z
  · rw [chL_I h1, chT] at h; simp at h
  · rw [chL_B h1, chT] at h
    simp only [Prod.mk.injEq, true_and] at h
    exact ⟨h1, h.2.symm, h.1.symm⟩

theorem chUT {z z' : ℤ × ℤ} (h : ch p r s w 1 z = ch p r s w 2 z') :
    ¬ IU r s z ∧ z'.1 + z'.2 = 2 * p ∧ z'.1 % (3 * (2 * r + s)) = wrap r s (aU r s z + w) := by
  by_cases h1 : IU r s z
  · rw [chU_I h1, chT] at h; simp at h
  · rw [chU_B h1, chT] at h
    simp only [Prod.mk.injEq, true_and] at h
    exact ⟨h1, h.2.symm, h.1.symm⟩

/-! ## Unit steps along the boundaries -/

/-- Neighbouring arclengths on a seam circle. -/
def ArcAdj (r s l l' : ℤ) : Prop :=
  l' = l + 1 ∨ l = l' + 1 ∨ (l = 0 ∧ l' = 3 * (2 * r + s) - 1) ∨
    (l' = 0 ∧ l = 3 * (2 * r + s) - 1)

set_option maxHeartbeats 1000000 in
-- the piecewise boundary maps give many `omega` branches
theorem unit_PL (hr : 1 ≤ r) (hs : 1 ≤ s) {l l' : ℤ} (h0 : 0 ≤ l) (h1 : l < 3 * (2 * r + s))
    (h0' : 0 ≤ l') (h1' : l' < 3 * (2 * r + s)) :
    PL r s l' - PL r s l ∈ unitVec ↔ ArcAdj r s l l' := by
  rw [unit_sub]
  simp only [ArcAdj, U2]
  unfold PL
  split_ifs <;> simp only <;> omega

set_option maxHeartbeats 1000000 in
-- the piecewise boundary maps give many `omega` branches
theorem unit_PU (hr : 1 ≤ r) (hs : 1 ≤ s) {l l' : ℤ} (h0 : 0 ≤ l) (h1 : l < 3 * (2 * r + s))
    (h0' : 0 ≤ l') (h1' : l' < 3 * (2 * r + s)) :
    PU r s l' - PU r s l ∈ unitVec ↔ ArcAdj r s l l' := by
  rw [unit_sub]
  simp only [ArcAdj, U2]
  unfold PU
  split_ifs <;> simp only <;> omega

theorem unit_arcL (hr : 1 ≤ r) (hs : 1 ≤ s) {z z' : ℤ × ℤ} (h : HL r s z) (hb : ¬ IL r s z)
    (h' : HL r s z') (hb' : ¬ IL r s z') :
    z' - z ∈ unitVec ↔ ArcAdj r s (aL r s z) (aL r s z') := by
  have l1 := aL_range hr hs h hb
  have l2 := aL_range hr hs h' hb'
  conv_lhs => rw [eq_PL hr hs h hb, eq_PL hr hs h' hb']
  exact unit_PL hr hs l1.1 l1.2 l2.1 l2.2

theorem unit_arcU (hr : 1 ≤ r) (hs : 1 ≤ s) {z z' : ℤ × ℤ} (h : HU r s z) (hb : ¬ IU r s z)
    (h' : HU r s z') (hb' : ¬ IU r s z') :
    z' - z ∈ unitVec ↔ ArcAdj r s (aU r s z) (aU r s z') := by
  have l1 := aU_range hr hs h hb
  have l2 := aU_range hr hs h' hb'
  conv_lhs => rw [eq_PU hr hs h hb, eq_PU hr hs h' hb']
  exact unit_PU hr hs l1.1 l1.2 l2.1 l2.2

end Claude5E10
