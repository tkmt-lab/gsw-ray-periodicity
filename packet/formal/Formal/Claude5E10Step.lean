import Formal.Claude5E10Seam

/-!
# E10 model: one forced step of a literal path

Written by a Claude worker (2026-10-20, E10 bridge session).

A frame at index `i` is a unit triangle `(a, b, e)` of one chart carrying `q i, q (i+1),
q (i+2)`.  Since no edge has three common neighbours, `q (i+3)` is the other apex of the edge
`(q (i+1), q (i+2))`: either `b + e − a` in the same chart, or, when that point leaves the chart,
its image under the side isometry (`step`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

/-- A frame. -/
def Frame (p r s w : ℤ) (q : ℕ → MS p r s) (i c : ℕ) (a b e : ℤ × ℤ) : Prop :=
  InC p r s w c (q i).1 a ∧ InC p r s w c (q (i + 1)).1 b ∧ InC p r s w c (q (i + 2)).1 e ∧
    b - a ∈ unitVec ∧ e - a ∈ unitVec ∧ e - b ∈ unitVec

theorem adj_of_chart {c : ℕ} {v x : MV} {ρ ρ' : ℤ × ℤ} (h1 : InC p r s w c v ρ)
    (h2 : InC p r s w c x ρ') (hu : ρ' - ρ ∈ unitVec) (hne : v ≠ x) : AdjM p r s w v x :=
  ⟨hne, c, h1.1, ρ, ρ' - ρ, h1.2.1, by simpa using h2.2.1, hu, h1.2.2, by simpa using h2.2.2⟩

/-- Two different points of a chart that are at most two apart are different vertices. -/
theorem ne_of_chart (H : Hyp p r s w) {c : ℕ} {v x : MV} {ρ ρ' : ℤ × ℤ}
    (h1 : InC p r s w c v ρ) (h2 : InC p r s w c x ρ') (hne : ρ ≠ ρ')
    (hn1 : -3 < ρ'.1 - ρ.1) (hn2 : ρ'.1 - ρ.1 < 3) : v ≠ x := by
  by_cases hc : c < 2
  · exact fun e => hne ((inC_inj01 H hc h1 h2).1 e)
  · have : c = 2 := by have := h1.1; omega
    subst this
    exact fun e => hne ((inC_near2 H h1 h2 (by omega) (by omega)).1 e)

section path

variable {n : ℕ} {q : ℕ → MS p r s}

theorem lp_adj1 (hq : LiteralPath (GM p r s w) n q) {i : ℕ} (hi : i + 1 < n) :
    AdjM p r s w (q i).1 (q (i + 1)).1 := hq.2.2.2.1 i hi

theorem lp_adj2 (hq : LiteralPath (GM p r s w) n q) {i : ℕ} (hi : i + 2 < n) :
    AdjM p r s w (q i).1 (q (i + 2)).1 := hq.2.2.2.2.1 i hi

theorem lp_ne (hq : LiteralPath (GM p r s w) n q) {i j : ℕ} (hi : i < n) (hj : j < n)
    (hij : i ≠ j) : (q i).1 ≠ (q j).1 := fun e => hij (hq.2.2.1 i j hi hj (Subtype.ext e))

/-- The next point of a literal path is the other apex. -/
theorem forced (H : Hyp p r s w) (hq : LiteralPath (GM p r s w) n q) {i : ℕ} (hi : i + 3 < n)
    {X : MV} (h1 : AdjM p r s w (q (i + 1)).1 X) (h2 : AdjM p r s w (q (i + 2)).1 X)
    (h3 : X ≠ (q i).1) : (q (i + 3)).1 = X := by
  by_contra hne
  have a01 := lp_adj1 hq (i := i) (by omega)
  have a02 := lp_adj2 hq (i := i) (by omega)
  have a12 := lp_adj1 hq (i := i + 1) (by omega)
  have a13 := lp_adj2 hq (i := i + 1) (by omega)
  have a23 := lp_adj1 hq (i := i + 2) (by omega)
  have n03 := lp_ne hq (i := i) (j := i + 3) (by omega) hi (by omega)
  exact no_three H a12 (adjM_symm a01) (adjM_symm a02) h1 h2 a13 a23 (Ne.symm h3) n03
    (fun e => hne e.symm)

theorem sub_units {a b e : ℤ × ℤ} (h1 : b - a ∈ unitVec) (h2 : e - a ∈ unitVec)
    (h3 : e - b ∈ unitVec) : b + e - a ≠ a ∧ b + e - a ≠ b ∧ b + e - a ≠ e ∧
      b + e - a - b ∈ unitVec ∧ b + e - a - e ∈ unitVec ∧
      -3 < (b + e - a).1 - a.1 ∧ (b + e - a).1 - a.1 < 3 ∧ -3 < (b + e - a).1 - b.1 ∧
      (b + e - a).1 - b.1 < 3 ∧ -3 < (b + e - a).1 - e.1 ∧ (b + e - a).1 - e.1 < 3 := by
  have q1 : b + e - a - b = e - a := by abel
  have q2 : b + e - a - e = b - a := by abel
  obtain ⟨x1, x2, y1, y2⟩ := unit_small h1
  obtain ⟨z1, z2, t1, t2⟩ := unit_small h2
  obtain ⟨o1, o2, o3, o4⟩ := unit_small h3
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨e1, e2⟩ := e
  rw [unit_sub] at h1 h2 h3
  simp only [U2] at h1 h2 h3
  simp only [Prod.fst_sub, Prod.snd_sub] at x1 x2 y1 y2 z1 z2 t1 t2 o1 o2 o3 o4
  refine ⟨?_, ?_, ?_, by rw [q1, unit_sub]; exact h2, by rw [q2, unit_sub]; exact h1, ?_⟩
  · simp only [ne_eq, Prod.ext_iff, Prod.mk_add_mk, Prod.mk_sub_mk]; omega
  · simp only [ne_eq, Prod.ext_iff, Prod.mk_add_mk, Prod.mk_sub_mk]; omega
  · simp only [ne_eq, Prod.ext_iff, Prod.mk_add_mk, Prod.mk_sub_mk]; omega
  · simp only [Prod.mk_add_mk, Prod.mk_sub_mk]; omega

/-- Case A: the other apex lies in the same chart. -/
theorem step_in (H : Hyp p r s w) (hq : LiteralPath (GM p r s w) n q) {i c : ℕ} (hi : i + 3 < n)
    {a b e : ℤ × ℤ} (F : Frame p r s w q i c a b e) (hd : Dom p r s c (b + e - a)) :
    Frame p r s w q (i + 1) c b e (b + e - a) := by
  obtain ⟨ha, hb, he, u1, u2, u3⟩ := F
  obtain ⟨n0, nb, ne, v1, v2, k1, k2, k3, k4, k5, k6⟩ := sub_units u1 u2 u3
  have hX : InC p r s w c (ch p r s w c (b + e - a)) (b + e - a) := ⟨ha.1, hd, rfl⟩
  have x1 := ne_of_chart H hb hX (Ne.symm nb) (by omega) (by omega)
  have x2 := ne_of_chart H he hX (Ne.symm ne) (by omega) (by omega)
  have x0 := ne_of_chart H ha hX (Ne.symm n0) (by omega) (by omega)
  have := forced H hq hi (adj_of_chart hb hX v1 x1) (adj_of_chart he hX v2 x2) (Ne.symm x0)
  exact ⟨hb, he, ⟨ha.1, hd, this.symm⟩, u3, v1, v2⟩

theorem ht_ne_of {v : MV} {x : MV} (h : v.2.2 ≠ x.2.2) : v ≠ x := fun e => h (by rw [e])

theorem cross_rotN (k : ℕ) (a b : ℤ × ℤ) : cross (rotN k a) (rotN k b) = cross a b := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rotN, rot, cross] at ih ⊢; rw [← ih]; ring

/-- Case B in the lower cap: the edge is on a side, the next frame is in the tube. -/
theorem step_L (H : Hyp p r s w) (hq : LiteralPath (GM p r s w) n q) {i : ℕ} (hi : i + 3 < n)
    {a b e : ℤ × ℤ} (F : Frame p r s w q i 0 a b e) (hd : ¬ HL r s (b + e - a)) :
    ∃ j, j < 6 ∧ OnSide r s 0 j b ∧ OnSide r s 0 j e ∧ Out r s 0 j (b + e - a) ∧
      Frame p r s w q (i + 1) 2 (gmap p r s w 0 j b) (gmap p r s w 0 j e)
        (gmap p r s w 0 j (b + e - a)) := by
  obtain ⟨ha, hb, he, u1, u2, u3⟩ := F
  obtain ⟨j, hj, sb, se, so, sa⟩ := exitL ha.2.1 hb.2.1 he.2.1 u1 u2 u3 hd
  have hp := H.hp
  obtain ⟨gb, hgb⟩ := gmapL_ch H (w := w) hj hb.2.1 sb
  obtain ⟨ge, hge⟩ := gmapL_ch H (w := w) hj he.2.1 se
  have hgo := ((ht_gmapL (p := p) (w := w) hj (b + e - a)).2.1).1 so
  obtain ⟨-, -, -, v1, v2, -⟩ := sub_units u1 u2 u3
  have tb : InC p r s w 2 (q (i + 1)).1 (gmap p r s w 0 j b) :=
    ⟨by norm_num, by simp only [Dom, HT]; simp only [ht] at hgb; omega, gb.trans hb.2.2⟩
  have te : InC p r s w 2 (q (i + 2)).1 (gmap p r s w 0 j e) :=
    ⟨by norm_num, by simp only [Dom, HT]; simp only [ht] at hge; omega, ge.trans he.2.2⟩
  have tX : InC p r s w 2 (ch p r s w 2 (gmap p r s w 0 j (b + e - a)))
      (gmap p r s w 0 j (b + e - a)) :=
    ⟨by norm_num, by simp only [Dom, HT]; simp only [ht] at hgo; omega, rfl⟩
  have w1 : gmap p r s w 0 j (b + e - a) - gmap p r s w 0 j b ∈ unitVec := by
    rw [gmap_sub]; exact rotN_unit' _ v1
  have w2 : gmap p r s w 0 j (b + e - a) - gmap p r s w 0 j e ∈ unitVec := by
    rw [gmap_sub]; exact rotN_unit' _ v2
  have hX2 : (ch p r s w 2 (gmap p r s w 0 j (b + e - a))).2.2 = 1 := by
    rw [chT]; simpa [ht] using hgo
  have nb : (q (i + 1)).1 ≠ ch p r s w 2 (gmap p r s w 0 j (b + e - a)) := by
    rw [← tb.2.2, chT]; apply ht_ne_of; simp only [ht] at hgb hgo ⊢; omega
  have ne' : (q (i + 2)).1 ≠ ch p r s w 2 (gmap p r s w 0 j (b + e - a)) := by
    rw [← te.2.2, chT]; apply ht_ne_of; simp only [ht] at hge hgo ⊢; omega
  have na : ch p r s w 2 (gmap p r s w 0 j (b + e - a)) ≠ (q i).1 := by
    rw [← ha.2.2]
    by_cases hI : IL r s a
    · rw [chL_I hI, chT]; simp
    · rw [chL_B hI]; apply ht_ne_of; rw [hX2]; simp
  have := forced H hq hi (adj_of_chart tb tX w1 nb) (adj_of_chart te tX w2 ne') na
  refine ⟨j, hj, sb, se, so, tb, te, ⟨by norm_num, tX.2.1, this.symm⟩, ?_, w1, w2⟩
  rw [gmap_sub]; exact rotN_unit' _ u3

/-- Case B in the upper cap. -/
theorem step_U (H : Hyp p r s w) (hq : LiteralPath (GM p r s w) n q) {i : ℕ} (hi : i + 3 < n)
    {a b e : ℤ × ℤ} (F : Frame p r s w q i 1 a b e) (hd : ¬ HU r s (b + e - a)) :
    ∃ j, j < 6 ∧ OnSide r s 1 j b ∧ OnSide r s 1 j e ∧ Out r s 1 j (b + e - a) ∧
      Frame p r s w q (i + 1) 2 (gmap p r s w 1 j b) (gmap p r s w 1 j e)
        (gmap p r s w 1 j (b + e - a)) := by
  obtain ⟨ha, hb, he, u1, u2, u3⟩ := F
  obtain ⟨j, hj, sb, se, so, sa⟩ := exitU ha.2.1 hb.2.1 he.2.1 u1 u2 u3 hd
  have hp := H.hp
  obtain ⟨gb, hgb⟩ := gmapU_ch H hj hb.2.1 sb
  obtain ⟨ge, hge⟩ := gmapU_ch H hj he.2.1 se
  have hgo := ((ht_gmapU (p := p) (w := w) hj (b + e - a)).2.1).1 so
  obtain ⟨-, -, -, v1, v2, -⟩ := sub_units u1 u2 u3
  have tb : InC p r s w 2 (q (i + 1)).1 (gmap p r s w 1 j b) :=
    ⟨by norm_num, by simp only [Dom, HT]; simp only [ht] at hgb; omega, gb.trans hb.2.2⟩
  have te : InC p r s w 2 (q (i + 2)).1 (gmap p r s w 1 j e) :=
    ⟨by norm_num, by simp only [Dom, HT]; simp only [ht] at hge; omega, ge.trans he.2.2⟩
  have tX : InC p r s w 2 (ch p r s w 2 (gmap p r s w 1 j (b + e - a)))
      (gmap p r s w 1 j (b + e - a)) :=
    ⟨by norm_num, by simp only [Dom, HT]; simp only [ht] at hgo; omega, rfl⟩
  have w1 : gmap p r s w 1 j (b + e - a) - gmap p r s w 1 j b ∈ unitVec := by
    rw [gmap_sub]; exact rotN_unit' _ v1
  have w2 : gmap p r s w 1 j (b + e - a) - gmap p r s w 1 j e ∈ unitVec := by
    rw [gmap_sub]; exact rotN_unit' _ v2
  have hX2 : (ch p r s w 2 (gmap p r s w 1 j (b + e - a))).2.2 = 2 * p - 1 := by
    rw [chT]; simpa [ht] using hgo
  have nb : (q (i + 1)).1 ≠ ch p r s w 2 (gmap p r s w 1 j (b + e - a)) := by
    rw [← tb.2.2, chT]; apply ht_ne_of; simp only [ht] at hgb hgo ⊢; omega
  have ne' : (q (i + 2)).1 ≠ ch p r s w 2 (gmap p r s w 1 j (b + e - a)) := by
    rw [← te.2.2, chT]; apply ht_ne_of; simp only [ht] at hge hgo ⊢; omega
  have na : ch p r s w 2 (gmap p r s w 1 j (b + e - a)) ≠ (q i).1 := by
    rw [← ha.2.2]
    by_cases hI : IU r s a
    · rw [chU_I hI, chT]; simp
    · rw [chU_B hI]; apply ht_ne_of; rw [hX2]; simp
  have := forced H hq hi (adj_of_chart tb tX w1 nb) (adj_of_chart te tX w2 ne') na
  refine ⟨j, hj, sb, se, so, tb, te, ⟨by norm_num, tX.2.1, this.symm⟩, ?_, w1, w2⟩
  rw [gmap_sub]; exact rotN_unit' _ u3

end path

end Claude5E10
