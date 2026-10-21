import Formal.Claude5E10Step

/-!
# E10 model: the forced step leaving the tube

Written by a Claude worker (2026-10-20, E10 bridge session).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

theorem gmapInv_gmap (c i : ℕ) (z : ℤ × ℤ) :
    gmapInv p r s w c i (gmap p r s w c i z) = z := by
  simp only [gmap, gmapInv, add_sub_cancel_right]
  rw [rotN_add_mod]
  have := gk_lt c i
  rw [show ((6 - gk c i) % 6 + gk c i) % 6 = 0 by omega]
  simp [rotN]

theorem rotN_inv_unit (k : ℕ) {v : ℤ × ℤ} (h : rotN k v ∈ unitVec) : v ∈ unitVec := by
  have := rotN_unit' ((6 - k % 6) % 6) h
  rwa [rotN_add_mod, show ((6 - k % 6) % 6 + k) % 6 = 0 by omega] at this

theorem ht_add (z z' : ℤ × ℤ) : ht (z + z') = ht z + ht z' := by
  simp only [ht, Prod.fst_add, Prod.snd_add]; ring

theorem ht_per (t : ℤ) : ht (t • per r s) = 0 := by
  simp only [ht, per, Prod.smul_mk, smul_eq_mul]; ring

theorem ht_unit {u : ℤ × ℤ} (h : u ∈ unitVec) : -1 ≤ ht u ∧ ht u ≤ 1 := by
  rw [unit_U2] at h; simp only [U2] at h; simp only [ht]; omega

theorem ht_sub (z z' : ℤ × ℤ) : ht (z - z') = ht z - ht z' := by
  simp only [ht, Prod.fst_sub, Prod.snd_sub]; ring

/-- The inner apex of an edge on a side of the lower cap lies in the cap. -/
theorem innerL {j : ℕ} (hj : j < 6) {zb ze y : ℤ × ℤ} (hb : HL r s zb) (he : HL r s ze)
    (sb : OnSide r s 0 j zb) (se : OnSide r s 0 j ze) (u1 : y - zb ∈ unitVec)
    (u2 : y - ze ∈ unitVec) (hy : Inn1 r s 0 j y) (hr : 1 ≤ r) (hs : 1 ≤ s) : HL r s y := by
  obtain ⟨x1, x2⟩ := zb
  obtain ⟨y1, y2⟩ := ze
  obtain ⟨z1, z2⟩ := y
  rw [unit_sub] at u1 u2
  simp only [U2] at u1 u2
  simp only [HL] at hb he ⊢
  interval_cases j <;> simp only [OnSide, Inn1] at sb se hy <;> omega

theorem innerU {j : ℕ} (hj : j < 6) {zb ze y : ℤ × ℤ} (hb : HU r s zb) (he : HU r s ze)
    (sb : OnSide r s 1 j zb) (se : OnSide r s 1 j ze) (u1 : y - zb ∈ unitVec)
    (u2 : y - ze ∈ unitVec) (hy : Inn1 r s 1 j y) (hr : 1 ≤ r) (hs : 1 ≤ s) : HU r s y := by
  obtain ⟨x1, x2⟩ := zb
  obtain ⟨y1, y2⟩ := ze
  obtain ⟨z1, z2⟩ := y
  rw [unit_sub] at u1 u2
  simp only [U2] at u1 u2
  simp only [HU] at hb he ⊢
  interval_cases j <;> simp only [OnSide, Inn1] at sb se hy <;> omega

section path

variable {n : ℕ} {q : ℕ → MS p r s}

theorem ht_tri {a b e : ℤ × ℤ} (u1 : b - a ∈ unitVec) (u2 : e - a ∈ unitVec)
    (ha : HT p a) (hb : HT p b) (he : HT p e) :
    ht (b + e - a) = -1 → (ht a = 1 ∧ ht b = 0 ∧ ht e = 0) := by
  have h1 := ht_unit u1; have h2 := ht_unit u2
  rw [ht_sub] at h1 h2
  simp only [HT] at ha hb he
  simp only [ht, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at h1 h2 ⊢
  omega

theorem ht_tri' {a b e : ℤ × ℤ} (u1 : b - a ∈ unitVec) (u2 : e - a ∈ unitVec)
    (ha : HT p a) (hb : HT p b) (he : HT p e) :
    ht (b + e - a) = 2 * p + 1 → (ht a = 2 * p - 1 ∧ ht b = 2 * p ∧ ht e = 2 * p) := by
  have h1 := ht_unit u1; have h2 := ht_unit u2
  rw [ht_sub] at h1 h2
  simp only [HT] at ha hb he
  simp only [ht, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at h1 h2 ⊢
  omega

/-- Case B in the tube, lower seam: the next frame is in the lower cap. -/
theorem step_TL (H : Hyp p r s w) (hq : LiteralPath (GM p r s w) n q) {i : ℕ} (hi : i + 3 < n)
    {a b e : ℤ × ℤ} (F : Frame p r s w q i 2 a b e) (hlow : ht (b + e - a) = -1) :
    ∃ (j : ℕ) (t : ℤ) (zb ze : ℤ × ℤ), j < 6 ∧ HL r s zb ∧ HL r s ze ∧ OnSide r s 0 j zb ∧
      OnSide r s 0 j ze ∧ gmap p r s w 0 j zb = b + t • per r s ∧
      gmap p r s w 0 j ze = e + t • per r s ∧
      Inn1 r s 0 j (gmapInv p r s w 0 j (b + e - a + t • per r s)) ∧
      rotN (gk 0 j) (gmapInv p r s w 0 j (b + e - a + t • per r s) - zb) = b + e - a - b ∧
      Frame p r s w q (i + 1) 0 zb ze (gmapInv p r s w 0 j (b + e - a + t • per r s)) := by
  obtain ⟨ha, hb, he, u1, u2, u3⟩ := F
  have hr := H.hr; have hs := H.hs; have hp := H.hp
  obtain ⟨hta, htb, hte⟩ := ht_tri u1 u2 ha.2.1 hb.2.1 he.2.1 hlow
  obtain ⟨j, t, zb, ze, hj, Hb, He, sb, se, gb, ge⟩ := seamL H htb hte u3
  obtain ⟨-, -, -, v1, v2, -⟩ := sub_units u1 u2 u3
  set y := gmapInv p r s w 0 j (b + e - a + t • per r s) with hy
  have gy : gmap p r s w 0 j y = b + e - a + t • per r s := gmap_inv 0 j _
  have iy : Inn1 r s 0 j y := ((ht_gmapL (p := p) (w := w) hj y).2.2).2 (by
    rw [gy, ht_add, ht_per, hlow]; ring)
  have dy1 : rotN (gk 0 j) (y - zb) = b + e - a - b := by
    rw [← gmap_sub, gy, gb]; abel
  have dy2 : rotN (gk 0 j) (y - ze) = b + e - a - e := by
    rw [← gmap_sub, gy, ge]; abel
  have w1 : y - zb ∈ unitVec := rotN_inv_unit _ (by rw [dy1]; exact v1)
  have w2 : y - ze ∈ unitVec := rotN_inv_unit _ (by rw [dy2]; exact v2)
  have Hy := innerL hj Hb He sb se w1 w2 iy hr hs
  have cb : ch p r s w 0 zb = (q (i + 1)).1 := by
    rw [← (gmapL_ch H hj Hb sb).1, gb, chT_shift, hb.2.2]
  have ce : ch p r s w 0 ze = (q (i + 2)).1 := by
    rw [← (gmapL_ch H hj He se).1, ge, chT_shift, he.2.2]
  have tb : InC p r s w 0 (q (i + 1)).1 zb := ⟨by norm_num, Hb, cb⟩
  have te : InC p r s w 0 (q (i + 2)).1 ze := ⟨by norm_num, He, ce⟩
  have tX : InC p r s w 0 (ch p r s w 0 y) y := ⟨by norm_num, Hy, rfl⟩
  have nyb : y ≠ zb := by
    intro h; rw [h] at iy; interval_cases j <;> simp only [OnSide, Inn1] at sb iy <;> omega
  have nye : y ≠ ze := by
    intro h; rw [h] at iy; interval_cases j <;> simp only [OnSide, Inn1] at se iy <;> omega
  have nb : (q (i + 1)).1 ≠ ch p r s w 0 y := fun h =>
    nyb ((inC_inj01 H (by norm_num) tX tb).1 h.symm)
  have ne' : (q (i + 2)).1 ≠ ch p r s w 0 y := fun h =>
    nye ((inC_inj01 H (by norm_num) tX te).1 h.symm)
  have na : ch p r s w 0 y ≠ (q i).1 := by
    rw [← ha.2.2, chT]
    by_cases hI : IL r s y
    · rw [chL_I hI]; simp
    · rw [chL_B hI]; apply ht_ne_of; simp only [ht] at hta; simp only; omega
  have := forced H hq hi (adj_of_chart tb tX w1 nb) (adj_of_chart te tX w2 ne') na
  refine ⟨j, t, zb, ze, hj, Hb, He, sb, se, gb, ge, iy, dy1, tb, te, ⟨by norm_num, Hy, this.symm⟩, ?_,
    w1, w2⟩
  exact rotN_inv_unit (gk 0 j) (by rw [← gmap_sub, gb, ge]; convert u3 using 1; abel)

/-- Case B in the tube, upper seam: the next frame is in the upper cap. -/
theorem step_TU (H : Hyp p r s w) (hq : LiteralPath (GM p r s w) n q) {i : ℕ} (hi : i + 3 < n)
    {a b e : ℤ × ℤ} (F : Frame p r s w q i 2 a b e) (hup : ht (b + e - a) = 2 * p + 1) :
    ∃ (j : ℕ) (t : ℤ) (zb ze : ℤ × ℤ), j < 6 ∧ HU r s zb ∧ HU r s ze ∧ OnSide r s 1 j zb ∧
      OnSide r s 1 j ze ∧ gmap p r s w 1 j zb = b + t • per r s ∧
      gmap p r s w 1 j ze = e + t • per r s ∧
      Inn1 r s 1 j (gmapInv p r s w 1 j (b + e - a + t • per r s)) ∧
      rotN (gk 1 j) (gmapInv p r s w 1 j (b + e - a + t • per r s) - zb) = b + e - a - b ∧
      Frame p r s w q (i + 1) 1 zb ze (gmapInv p r s w 1 j (b + e - a + t • per r s)) := by
  obtain ⟨ha, hb, he, u1, u2, u3⟩ := F
  have hr := H.hr; have hs := H.hs; have hp := H.hp
  obtain ⟨hta, htb, hte⟩ := ht_tri' u1 u2 ha.2.1 hb.2.1 he.2.1 hup
  obtain ⟨j, t, zb, ze, hj, Hb, He, sb, se, gb, ge⟩ := seamU H htb hte u3
  obtain ⟨-, -, -, v1, v2, -⟩ := sub_units u1 u2 u3
  set y := gmapInv p r s w 1 j (b + e - a + t • per r s) with hy
  have gy : gmap p r s w 1 j y = b + e - a + t • per r s := gmap_inv 1 j _
  have iy : Inn1 r s 1 j y := ((ht_gmapU (p := p) (w := w) hj y).2.2).2 (by
    rw [gy, ht_add, ht_per, hup]; ring)
  have dy1 : rotN (gk 1 j) (y - zb) = b + e - a - b := by
    rw [← gmap_sub, gy, gb]; abel
  have dy2 : rotN (gk 1 j) (y - ze) = b + e - a - e := by
    rw [← gmap_sub, gy, ge]; abel
  have w1 : y - zb ∈ unitVec := rotN_inv_unit _ (by rw [dy1]; exact v1)
  have w2 : y - ze ∈ unitVec := rotN_inv_unit _ (by rw [dy2]; exact v2)
  have Hy := innerU hj Hb He sb se w1 w2 iy hr hs
  have cb : ch p r s w 1 zb = (q (i + 1)).1 := by
    rw [← (gmapU_ch H hj Hb sb).1, gb, chT_shift, hb.2.2]
  have ce : ch p r s w 1 ze = (q (i + 2)).1 := by
    rw [← (gmapU_ch H hj He se).1, ge, chT_shift, he.2.2]
  have tb : InC p r s w 1 (q (i + 1)).1 zb := ⟨by norm_num, Hb, cb⟩
  have te : InC p r s w 1 (q (i + 2)).1 ze := ⟨by norm_num, He, ce⟩
  have tX : InC p r s w 1 (ch p r s w 1 y) y := ⟨by norm_num, Hy, rfl⟩
  have nyb : y ≠ zb := by
    intro h; rw [h] at iy; interval_cases j <;> simp only [OnSide, Inn1] at sb iy <;> omega
  have nye : y ≠ ze := by
    intro h; rw [h] at iy; interval_cases j <;> simp only [OnSide, Inn1] at se iy <;> omega
  have nb : (q (i + 1)).1 ≠ ch p r s w 1 y := fun h =>
    nyb ((inC_inj01 H (by norm_num) tX tb).1 h.symm)
  have ne' : (q (i + 2)).1 ≠ ch p r s w 1 y := fun h =>
    nye ((inC_inj01 H (by norm_num) tX te).1 h.symm)
  have na : ch p r s w 1 y ≠ (q i).1 := by
    rw [← ha.2.2, chT]
    by_cases hI : IU r s y
    · rw [chU_I hI]; simp
    · rw [chU_B hI]; apply ht_ne_of; simp only [ht] at hta; simp only; omega
  have := forced H hq hi (adj_of_chart tb tX w1 nb) (adj_of_chart te tX w2 ne') na
  refine ⟨j, t, zb, ze, hj, Hb, He, sb, se, gb, ge, iy, dy1, tb, te, ⟨by norm_num, Hy, this.symm⟩, ?_,
    w1, w2⟩
  exact rotN_inv_unit (gk 1 j) (by rw [← gmap_sub, gb, ge]; convert u3 using 1; abel)

end path

end Claude5E10
