import Formal.Claude3GeoBasic

/-!
# Theorem 1a, geometric foundation (2): unit triangles, common neighbours, the row lemma

Written by a Claude worker (2026-10-20, Theorem 1a geometric session).

* `valid_unitTri_adj`   : under `Valid`, a unit lattice triangle inside one chart is a
                          triangle (3-clique) of `graph S t`.
* `valid_common_iff`    : (key) under `Valid`, if an edge `P Q` of a chart has two distinct
                          apexes `A, B` in that chart (`A, B` unit-adjacent to `P` and `Q`), then
                          the common neighbours of `P, Q` in the whole surface graph are exactly
                          `A` and `B`; `valid_next_iff`: the forced continuation of `(A, P, Q)`
                          is `B`.
* `valid_edge_common_iff` : the same for the edge `z, z + u` (`u` a unit vector) and its two
                          apexes `z + rot u`, `z + rot⁵ u`.
* `forced_eq_pattern`   : a forced walk started on a "row pattern" lattice walk `W` inside one
                          chart follows `W` as long as `W` stays in the chart.
* `rowPt h i = (⌊i/2⌋, h + i mod 2)` : paper eq. (rows), `q_{2j} = (j,h)`, `q_{2j+1} = (j,h+1)`.
* `rowTri_iff`, `rowWalk_mem_iff` : paper eq. (triangle-bounds)/(passage): the triangle `T_i` lies
  in the chart iff `ℓ ≤ i ≤ u`, with `ℓ = 2Aₑ - δ = Aₑ + Aₒ`, `u = 2Bₑ + ε = Bₑ + Bₒ + 1`.
* `rowOutput_iff`       : paper eq. (output).
* `row_lemma`           : the row lemma for direction `(1,0)`.
-/

namespace ClaudeChallenge2.Geo

open ClaudeChallenge2

variable {S : Sig} {t : ℕ}

theorem pt_congr {f : Fin S.C} {z z' : ℤ × ℤ} (h : (S.chart f).Mem t z)
    (h' : (S.chart f).Mem t z') (e : z = z') : pt S t f z h = pt S t f z' h' := by
  subst e; rfl

/-! ## Unit triangles and the two common neighbours of an edge -/

/-- Under `Valid`, a unit lattice triangle inside one chart is a triangle of the graph. -/
theorem valid_unitTri_adj (hV : Valid S t) {f : Fin S.C} {a b c : ℤ × ℤ}
    (ha : (S.chart f).Mem t a) (hb : (S.chart f).Mem t b) (hc : (S.chart f).Mem t c)
    (hab : b - a ∈ unitVec) (hac : c - a ∈ unitVec) (hbc : c - b ∈ unitVec) :
    (graph S t).Adj (pt S t f a ha) (pt S t f b hb) ∧
      (graph S t).Adj (pt S t f a ha) (pt S t f c hc) ∧
        (graph S t).Adj (pt S t f b hb) (pt S t f c hc) :=
  ⟨valid_adj_of_unit hV ha hb hab, valid_adj_of_unit hV ha hc hac,
    valid_adj_of_unit hV hb hc hbc⟩

/-- **Key lemma.** Under `Valid`, let `P Q` be a unit edge of chart `f` and `A ≠ B` two points
of the same chart, each unit-adjacent to both `P` and `Q`. Then the common neighbours of
`P, Q` in the surface graph are exactly `A` and `B`. -/
theorem valid_common_iff (hV : Valid S t) {f : Fin S.C} {P Q A B : ℤ × ℤ}
    (hP : (S.chart f).Mem t P) (hQ : (S.chart f).Mem t Q) (hA : (S.chart f).Mem t A)
    (hB : (S.chart f).Mem t B) (hPQ : Q - P ∈ unitVec) (hAP : P - A ∈ unitVec)
    (hAQ : Q - A ∈ unitVec) (hPB : B - P ∈ unitVec) (hQB : B - Q ∈ unitVec) (hAB : A ≠ B) :
    ∀ v, ((graph S t).Adj (pt S t f P hP) v ∧ (graph S t).Adj (pt S t f Q hQ) v) ↔
      (v = pt S t f A hA ∨ v = pt S t f B hB) := by
  obtain ⟨x, y, hxy, hiff⟩ := hV.1 _ _ (valid_adj_of_unit hV hP hQ hPQ)
  have cA : (graph S t).Adj (pt S t f P hP) (pt S t f A hA) ∧
      (graph S t).Adj (pt S t f Q hQ) (pt S t f A hA) :=
    ⟨(valid_adj_of_unit hV hA hP hAP).symm, (valid_adj_of_unit hV hA hQ hAQ).symm⟩
  have cB : (graph S t).Adj (pt S t f P hP) (pt S t f B hB) ∧
      (graph S t).Adj (pt S t f Q hQ) (pt S t f B hB) :=
    ⟨valid_adj_of_unit hV hP hB hPB, valid_adj_of_unit hV hQ hB hQB⟩
  have nAB := valid_pt_ne hV hA hB hAB
  have eA := (hiff _).1 cA
  have eB := (hiff _).1 cB
  intro v
  rw [hiff v]
  rcases eA with eA | eA <;> rcases eB with eB | eB
  · exact absurd (eA.trans eB.symm) nAB
  · rw [eA, eB]
  · rw [eA, eB, or_comm]
  · exact absurd (eA.trans eB.symm) nAB

/-- Under the hypotheses of `valid_common_iff`, the forced continuation of the oriented
triangle `(A, P, Q)` is `B`. -/
theorem valid_next_iff (hV : Valid S t) {f : Fin S.C} {P Q A B : ℤ × ℤ}
    (hP : (S.chart f).Mem t P) (hQ : (S.chart f).Mem t Q) (hA : (S.chart f).Mem t A)
    (hB : (S.chart f).Mem t B) (hPQ : Q - P ∈ unitVec) (hAP : P - A ∈ unitVec)
    (hAQ : Q - A ∈ unitVec) (hPB : B - P ∈ unitVec) (hQB : B - Q ∈ unitVec) (hAB : A ≠ B)
    (e : Vertex S t) :
    Next (graph S t) (pt S t f A hA) (pt S t f P hP) (pt S t f Q hQ) e ↔ e = pt S t f B hB :=
  next_iff_of_common (valid_pt_ne hV hA hB hAB)
    (valid_common_iff hV hP hQ hA hB hPQ hAP hAQ hPB hQB hAB) e

/-- The two apexes of the unit edge `z, z + u` are `z + rot u` and `z + rot⁵ u`. -/
theorem apex_facts {u : ℤ × ℤ} (hu : u ∈ unitVec) :
    rot u ∈ unitVec ∧ u - rot u ∈ unitVec ∧ rotN 5 u ∈ unitVec ∧ rotN 5 u - u ∈ unitVec ∧
      rot u ≠ rotN 5 u := by
  rw [mem_unitVec_iff] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **Key lemma, edge form.** Under `Valid`, if the unit edge `z, z + u` of chart `f` has both
apexes `z + rot u` and `z + rot⁵ u` in the chart, they are exactly its common neighbours. -/
theorem valid_edge_common_iff (hV : Valid S t) {f : Fin S.C} {z u : ℤ × ℤ} (hu : u ∈ unitVec)
    (h0 : (S.chart f).Mem t z) (h1 : (S.chart f).Mem t (z + u))
    (hA : (S.chart f).Mem t (z + rot u)) (hB : (S.chart f).Mem t (z + rotN 5 u)) :
    ∀ v, ((graph S t).Adj (pt S t f z h0) v ∧ (graph S t).Adj (pt S t f (z + u) h1) v) ↔
      (v = pt S t f (z + rot u) hA ∨ v = pt S t f (z + rotN 5 u) hB) := by
  obtain ⟨a1, a2, b1, b2, ne⟩ := apex_facts hu
  refine valid_common_iff hV h0 h1 hA hB (by simpa using hu) ?_ ?_ (by simpa using b1) ?_ ?_
  · simpa using neg_mem_unitVec a1
  · simpa [add_sub_add_left_eq_sub] using a2
  · simpa [add_sub_add_left_eq_sub] using b2
  · simpa using ne

/-! ## Forced walks along a row pattern -/

/-- A lattice walk shaped like a strip of unit triangles: consecutive and distance-two points
are unit-adjacent, and points at distance three differ. -/
structure Pattern (W : ℕ → ℤ × ℤ) : Prop where
  step1 : ∀ m, W (m + 1) - W m ∈ unitVec
  step2 : ∀ m, W (m + 2) - W m ∈ unitVec
  step3 : ∀ m, W (m + 3) ≠ W m

/-- The vertex sequence of a pattern walk inside one chart is a forced walk. -/
theorem pattern_isForced (hV : Valid S t) {W : ℕ → ℤ × ℤ} (hW : Pattern W) {f : Fin S.C}
    {N : ℕ} (hmem : ∀ m, m < N → (S.chart f).Mem t (W m)) {p : ℕ → Vertex S t}
    (hp : ∀ m (hm : m < N), p m = pt S t f (W m) (hmem m hm)) : IsForced (graph S t) p N := by
  intro k hk
  rw [hp k (by omega), hp (k + 1) (by omega), hp (k + 2) (by omega), hp (k + 3) hk]
  exact (valid_next_iff hV _ _ _ _ (hW.step1 (k + 1)) (hW.step1 k) (hW.step2 k)
    (hW.step2 (k + 1)) (hW.step1 (k + 2)) (hW.step3 k).symm _).2 rfl

/-- **Forced walks follow a pattern walk inside one chart.** If a forced walk starts with the
first three vertices of a pattern walk `W` that stays in chart `f` up to index `N`, it agrees
with `W` up to index `N`. -/
theorem forced_eq_pattern (hV : Valid S t) {W : ℕ → ℤ × ℤ} (hW : Pattern W) {f : Fin S.C}
    {N : ℕ} (hmem : ∀ m, m < N → (S.chart f).Mem t (W m)) {p : ℕ → Vertex S t}
    (hp : IsForced (graph S t) p N)
    (h0 : ∀ m (hm : m < N), m < 3 → p m = pt S t f (W m) (hmem m hm)) :
    ∀ m (hm : m < N), p m = pt S t f (W m) (hmem m hm) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    match m, ih with
    | 0, _ => exact h0 0 hm (by omega)
    | 1, _ => exact h0 1 hm (by omega)
    | 2, _ => exact h0 2 hm (by omega)
    | k + 3, ih =>
      have q := hp k hm
      rw [ih k (by omega) (by omega), ih (k + 1) (by omega) (by omega),
        ih (k + 2) (by omega) (by omega)] at q
      exact (valid_next_iff hV _ _ _ _ (hW.step1 (k + 1)) (hW.step1 k) (hW.step2 k)
        (hW.step2 (k + 1)) (hW.step1 (k + 2)) (hW.step3 k).symm _).1 q

/-! ## Rows: paper eq. (rows) -/

/-- `q_i` of paper eq. (rows): `q_{2j} = (j, h)`, `q_{2j+1} = (j, h+1)`. -/
def rowPt (h i : ℤ) : ℤ × ℤ := (i / 2, h + i % 2)

theorem rowPt_even (h j : ℤ) : rowPt h (2 * j) = (j, h) := by
  simp only [rowPt, Prod.mk.injEq]; omega

theorem rowPt_odd (h j : ℤ) : rowPt h (2 * j + 1) = (j, h + 1) := by
  simp only [rowPt, Prod.mk.injEq]; omega

theorem rowPt_injective (h : ℤ) : Function.Injective (rowPt h) := by
  intro i i' e
  simp only [rowPt, Prod.mk.injEq] at e
  omega

/-- Paper eq. (rows) as integer-indexed facts: consecutive differences alternate `(0,1)`,
`(1,-1)`; distance two is `(1,0)`; distance three is nonzero. -/
theorem rowPt_step1 (h i : ℤ) : rowPt h (i + 1) - rowPt h i ∈ unitVec := by
  simp only [mem_unitVec_iff, rowPt, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]; omega

theorem rowPt_step2 (h i : ℤ) : rowPt h (i + 2) - rowPt h i = (1, 0) := by
  simp only [rowPt, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]; omega

theorem rowPt_step3 (h i : ℤ) : rowPt h (i + 3) ≠ rowPt h i := by
  simp only [rowPt, ne_eq, Prod.ext_iff]; omega

/-- The row walk started at integer index `i₀`, as a pattern walk indexed by `ℕ`. -/
theorem rowPt_pattern (h i₀ : ℤ) : Pattern (fun m : ℕ => rowPt h (i₀ + m)) where
  step1 m := by simpa [add_assoc] using rowPt_step1 h (i₀ + m)
  step2 m := by
    have := rowPt_step2 h (i₀ + m)
    simp only [Nat.cast_add, Nat.cast_ofNat, ← add_assoc, this]
    decide
  step3 m := by simpa [add_assoc] using rowPt_step3 h (i₀ + m)

/-! ## Triangle bounds: paper eqs. (triangle-bounds), (passage), (output) -/

section Bounds

variable (c : Chart) (t : ℕ) (h : ℤ)

/-- `A_e = max(L_x, L_s - h)`. -/
def Ae : ℤ := max (c.lx.eval t) (c.ls.eval t - h)
/-- `B_e = min(U_x - 1, U_s - h - 1)`. -/
def Be : ℤ := min (c.ux.eval t - 1) (c.us.eval t - h - 1)
/-- `A_o = max(L_x, L_s - h - 1)`. -/
def Ao : ℤ := max (c.lx.eval t) (c.ls.eval t - h - 1)
/-- `B_o = min(U_x - 1, U_s - h - 2)`. -/
def Bo : ℤ := min (c.ux.eval t - 1) (c.us.eval t - h - 2)
/-- `δ = A_e - A_o`. -/
def delta : ℤ := Ae c t h - Ao c t h
/-- `ε = B_o - B_e + 1`. -/
def eps : ℤ := Bo c t h - Be c t h + 1
/-- `ℓ = 2 A_e - δ`, the first triangle index of the passage. -/
def lo : ℤ := 2 * Ae c t h - delta c t h
/-- `u = 2 B_e + ε`, the last triangle index of the passage. -/
def hi : ℤ := 2 * Be c t h + eps c t h

theorem delta_mem : delta c t h = 0 ∨ delta c t h = 1 := by
  simp only [delta, Ae, Ao]; omega

theorem eps_mem : eps c t h = 0 ∨ eps c t h = 1 := by
  simp only [eps, Be, Bo]; omega

/-- The triangle `T_i = {q_i, q_{i+1}, q_{i+2}}` lies in the chart. -/
def TriIn (Q : ℤ → ℤ × ℤ) (i : ℤ) : Prop :=
  c.Mem t (Q i) ∧ c.Mem t (Q (i + 1)) ∧ c.Mem t (Q (i + 2))

variable {c t h}

theorem rowTri_rows {i : ℤ} (hT : TriIn c t (rowPt h) i) :
    c.ly.eval t ≤ h ∧ h + 1 ≤ c.uy.eval t := by
  obtain ⟨h0, h1, h2⟩ := hT
  simp only [Chart.Mem, rowPt] at h0 h1 h2
  omega

/-- Paper eq. (triangle-bounds), even indices. -/
theorem rowTri_even_iff (hh : c.ly.eval t ≤ h ∧ h + 1 ≤ c.uy.eval t) (j : ℤ) :
    TriIn c t (rowPt h) (2 * j) ↔ Ae c t h ≤ j ∧ j ≤ Be c t h := by
  simp only [TriIn, Chart.Mem, rowPt, Ae, Be]
  constructor
  · intro H; omega
  · intro H; omega

/-- Paper eq. (triangle-bounds), odd indices. -/
theorem rowTri_odd_iff (hh : c.ly.eval t ≤ h ∧ h + 1 ≤ c.uy.eval t) (j : ℤ) :
    TriIn c t (rowPt h) (2 * j + 1) ↔ Ao c t h ≤ j ∧ j ≤ Bo c t h := by
  simp only [TriIn, Chart.Mem, rowPt, Ao, Bo]
  constructor
  · intro H; omega
  · intro H; omega

/-- Paper eq. (passage): the triangle-index set is the interval `ℓ ≤ i ≤ u` (possibly empty,
including the one-odd-triangle case). -/
theorem rowTri_iff (hh : c.ly.eval t ≤ h ∧ h + 1 ≤ c.uy.eval t) (i : ℤ) :
    TriIn c t (rowPt h) i ↔ lo c t h ≤ i ∧ i ≤ hi c t h := by
  simp only [TriIn, Chart.Mem, rowPt, lo, hi, delta, eps, Ae, Be, Ao, Bo]
  constructor
  · intro H; omega
  · intro H; omega

/-- The row walk `q_{i₀}, …, q_{i₀+N-1}` (`N ≥ 3`) stays in the chart exactly when its two rows
are in the chart and its triangle indices `i₀ … i₀+N-3` lie in `[ℓ, u]`. -/
theorem rowWalk_mem_iff {N : ℕ} (hN : 3 ≤ N) (i₀ : ℤ) :
    (∀ m : ℕ, m < N → c.Mem t (rowPt h (i₀ + m))) ↔
      (c.ly.eval t ≤ h ∧ h + 1 ≤ c.uy.eval t) ∧ lo c t h ≤ i₀ ∧ i₀ + N - 3 ≤ hi c t h := by
  constructor
  · intro H
    have T0 : TriIn c t (rowPt h) i₀ := by
      refine ⟨?_, ?_, ?_⟩
      · simpa using H 0 (by omega)
      · simpa using H 1 (by omega)
      · simpa using H 2 (by omega)
    have T1 : TriIn c t (rowPt h) (i₀ + N - 3) := by
      refine ⟨?_, ?_, ?_⟩
      · have := H (N - 3) (by omega)
        rwa [show i₀ + ((N - 3 : ℕ) : ℤ) = i₀ + N - 3 by omega] at this
      · have := H (N - 2) (by omega)
        rwa [show i₀ + ((N - 2 : ℕ) : ℤ) = i₀ + N - 3 + 1 by omega] at this
      · have := H (N - 1) (by omega)
        rwa [show i₀ + ((N - 1 : ℕ) : ℤ) = i₀ + N - 3 + 2 by omega] at this
    have hh := rowTri_rows T0
    have := (rowTri_iff hh _).1 T0
    have := (rowTri_iff hh _).1 T1
    exact ⟨hh, by omega, by omega⟩
  · rintro ⟨hh, hl, hu⟩ m hm
    by_cases hm3 : m + 3 ≤ N
    · exact ((rowTri_iff hh (i₀ + m)).2 ⟨by omega, by omega⟩).1
    · have T := (rowTri_iff hh (i₀ + N - 3)).2 ⟨by omega, by omega⟩
      rcases (show m = N - 2 ∨ m = N - 1 by omega) with rfl | rfl
      · rw [show i₀ + ((N - 2 : ℕ) : ℤ) = i₀ + N - 3 + 1 by omega]; exact T.2.1
      · rw [show i₀ + ((N - 1 : ℕ) : ℤ) = i₀ + N - 3 + 2 by omega]; exact T.2.2

/-- Paper eq. (output): the new output `q_{ℓ+2}, …, q_{u+2}` of an entered passage is the lower
row `y = h, A_e+1 ≤ x ≤ B_e+1` together with the upper row `y = h+1, A_e+1-δ ≤ x ≤ B_e+ε`. -/
theorem rowOutput_iff (z : ℤ × ℤ) :
    (∃ i, lo c t h + 2 ≤ i ∧ i ≤ hi c t h + 2 ∧ rowPt h i = z) ↔
      (z.2 = h ∧ Ae c t h + 1 ≤ z.1 ∧ z.1 ≤ Be c t h + 1) ∨
        (z.2 = h + 1 ∧ Ae c t h + 1 - delta c t h ≤ z.1 ∧ z.1 ≤ Be c t h + eps c t h) := by
  have hd := delta_mem c t h
  have he := eps_mem c t h
  simp only [lo, hi] at *
  generalize delta c t h = d at *
  generalize eps c t h = e at *
  obtain ⟨x, y⟩ := z
  simp only [rowPt, Prod.mk.injEq]
  constructor
  · rintro ⟨i, h1, h2, h3, h4⟩; omega
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨2 * x, by omega, by omega, by omega, by omega⟩
    · exact ⟨2 * x + 1, by omega, by omega, by omega, by omega⟩

end Bounds

/-! ## The row lemma, direction `(1,0)` -/

/-- **Row lemma (direction `(1,0)`), paper eqs. (rows)–(passage).** Under `Valid`, let `p` be a
forced walk of length `N ≥ 3` whose first three vertices are `q_{i₀}, q_{i₀+1}, q_{i₀+2}` of
the row walk `q_i = rowPt h i` in chart `f`. If both rows are in the chart and the triangle
indices `i₀, …, i₀+N-3` lie in `[ℓ, u]` (the exact range given by the chart bounds), then
`p m = q_{i₀+m}` for all `m < N`. -/
theorem row_lemma (hV : Valid S t) {f : Fin S.C} {h i₀ : ℤ} {N : ℕ} (hN : 3 ≤ N)
    (hh : (S.chart f).ly.eval t ≤ h ∧ h + 1 ≤ (S.chart f).uy.eval t)
    (hl : lo (S.chart f) t h ≤ i₀) (hu : i₀ + N - 3 ≤ hi (S.chart f) t h)
    {p : ℕ → Vertex S t} (hp : IsForced (graph S t) p N)
    (h0 : ∀ m : ℕ, m < 3 → ∃ hz, p m = pt S t f (rowPt h (i₀ + m)) hz) :
    ∀ m : ℕ, m < N → ∃ hz, p m = pt S t f (rowPt h (i₀ + m)) hz := by
  have hmem := (rowWalk_mem_iff hN i₀).2 ⟨hh, hl, hu⟩
  have key := forced_eq_pattern hV (rowPt_pattern h i₀) hmem hp (fun m hm h3 => by
    obtain ⟨hz, e⟩ := h0 m h3
    exact e)
  exact fun m hm => ⟨hmem m hm, key m hm⟩

/-- Conversely, the row walk itself is forced, so `row_lemma` is not vacuous. -/
theorem row_isForced (hV : Valid S t) {f : Fin S.C} {h i₀ : ℤ} {N : ℕ}
    (hmem : ∀ m : ℕ, m < N → (S.chart f).Mem t (rowPt h (i₀ + m))) {p : ℕ → Vertex S t}
    (hp : ∀ m (hm : m < N), p m = pt S t f (rowPt h (i₀ + m)) (hmem m hm)) :
    IsForced (graph S t) p N :=
  pattern_isForced hV (rowPt_pattern h i₀) hmem hp

end ClaudeChallenge2.Geo
