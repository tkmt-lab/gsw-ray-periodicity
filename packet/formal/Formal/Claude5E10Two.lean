import Formal.Claude5E10Deg

/-!
# E10 model: every edge has exactly two common neighbours (`two_common`)

Written by a Claude worker (2026-10-20, E10 bridge session).  The two apexes of an edge of a
chart are in the chart, or one of them leaves it and is replaced by its image under the side
isometry (as in the forced step); with `no_three` these are all the common neighbours.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

theorem apex_sum {u : ℤ × ℤ} : rotL u + rotR u = u := by
  simp only [rotL, rotR]; ext <;> simp <;> ring

theorem apex_units {u : ℤ × ℤ} (hu : u ∈ unitVec) : rotL u ∈ unitVec ∧ rotR u ∈ unitVec ∧
    rotL u - u ∈ unitVec ∧ rotR u - u ∈ unitVec ∧ rotL u ≠ rotR u := by
  rw [unit_iff] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rotL, rotR, unitVec]

/-- Two vertices of a chart frame give a common neighbour through any of its apexes. -/
theorem common_of_frame (H : Hyp p r s w) {c : ℕ} {v x y : MV} {a b e : ℤ × ℤ}
    (ha : InC p r s w c v a) (hb : InC p r s w c x b) (he : InC p r s w c y e)
    (u1 : b - a ∈ unitVec) (u2 : e - a ∈ unitVec) (u3 : e - b ∈ unitVec) :
    AdjM p r s w v y ∧ AdjM p r s w x y := by
  have s1 := unit_small u1; have s2 := unit_small u2; have s3 := unit_small u3
  have ne1 : a ≠ e := fun h => unit_ne_zero' u2 (by rw [h, sub_self])
  have ne2 : b ≠ e := fun h => unit_ne_zero' u3 (by rw [h, sub_self])
  refine ⟨adj_of_chart ha he u2 (ne_of_chart H ha he ne1 (by simp only [Prod.fst_sub] at s2; omega)
    (by simp only [Prod.fst_sub] at s2; omega)), adj_of_chart hb he u3 (ne_of_chart H hb he ne2
    (by simp only [Prod.fst_sub] at s3; omega) (by simp only [Prod.fst_sub] at s3; omega))⟩

/-- The outer apex of a chart edge whose apex leaves the chart: it lies in the neighbouring
chart. -/
theorem outer_apex (H : Hyp p r s w) {c : ℕ} {va vb ve : MV} {a b e : ℤ × ℤ}
    (ha : InC p r s w c va a) (hb : InC p r s w c vb b) (he : InC p r s w c ve e)
    (u1 : b - a ∈ unitVec) (u2 : e - a ∈ unitVec) (u3 : e - b ∈ unitVec)
    (hd : ¬ Dom p r s c (b + e - a)) :
    ∃ y, AdjM p r s w vb y ∧ AdjM p r s w ve y ∧ y ≠ va := by
  have hp := H.hp; have hr := H.hr; have hs := H.hs
  obtain ⟨-, -, -, v1, v2, -⟩ := sub_units u1 u2 u3
  rcases c_cases ha.1 with rfl | rfl | rfl
  · obtain ⟨j, hj, sb, se, so, sa⟩ := exitL ha.2.1 hb.2.1 he.2.1 u1 u2 u3 (by simpa [Dom] using hd)
    obtain ⟨gb, hgb⟩ := gmapL_ch H (w := w) hj hb.2.1 sb
    obtain ⟨ge, hge⟩ := gmapL_ch H (w := w) hj he.2.1 se
    have hgo := ((ht_gmapL (p := p) (w := w) hj (b + e - a)).2.1).1 so
    have tb : InC p r s w 2 vb (gmap p r s w 0 j b) :=
      ⟨by norm_num, by simp only [Dom, HT]; simp only [ht] at hgb; omega, gb.trans hb.2.2⟩
    have te : InC p r s w 2 ve (gmap p r s w 0 j e) :=
      ⟨by norm_num, by simp only [Dom, HT]; simp only [ht] at hge; omega, ge.trans he.2.2⟩
    have tX : InC p r s w 2 (ch p r s w 2 (gmap p r s w 0 j (b + e - a))) (gmap p r s w 0 j (b + e - a)) :=
      ⟨by norm_num, by simp only [Dom, HT]; simp only [ht] at hgo; omega, rfl⟩
    obtain ⟨c1, c2⟩ := common_of_frame H tb te tX (by rw [gmap_sub]; exact rotN_unit' _ u3)
      (by rw [gmap_sub]; exact rotN_unit' _ v1) (by rw [gmap_sub]; exact rotN_unit' _ v2)
    refine ⟨_, c1, c2, ?_⟩
    rw [← ha.2.2]
    by_cases hI : IL r s a
    · rw [chL_I hI, chT]; simp
    · rw [chL_B hI, chT]; apply ht_ne_of; simp only [ht] at hgo; simp only; omega
  · obtain ⟨j, hj, sb, se, so, sa⟩ := exitU ha.2.1 hb.2.1 he.2.1 u1 u2 u3 (by simpa [Dom] using hd)
    obtain ⟨gb, hgb⟩ := gmapU_ch H hj hb.2.1 sb
    obtain ⟨ge, hge⟩ := gmapU_ch H hj he.2.1 se
    have hgo := ((ht_gmapU (p := p) (w := w) hj (b + e - a)).2.1).1 so
    have tb : InC p r s w 2 vb (gmap p r s w 1 j b) :=
      ⟨by norm_num, by simp only [Dom, HT]; simp only [ht] at hgb; omega, gb.trans hb.2.2⟩
    have te : InC p r s w 2 ve (gmap p r s w 1 j e) :=
      ⟨by norm_num, by simp only [Dom, HT]; simp only [ht] at hge; omega, ge.trans he.2.2⟩
    have tX : InC p r s w 2 (ch p r s w 2 (gmap p r s w 1 j (b + e - a))) (gmap p r s w 1 j (b + e - a)) :=
      ⟨by norm_num, by simp only [Dom, HT]; simp only [ht] at hgo; omega, rfl⟩
    obtain ⟨c1, c2⟩ := common_of_frame H tb te tX (by rw [gmap_sub]; exact rotN_unit' _ u3)
      (by rw [gmap_sub]; exact rotN_unit' _ v1) (by rw [gmap_sub]; exact rotN_unit' _ v2)
    refine ⟨_, c1, c2, ?_⟩
    rw [← ha.2.2]
    by_cases hI : IU r s a
    · rw [chU_I hI, chT]; simp
    · rw [chU_B hI, chT]; apply ht_ne_of; simp only [ht] at hgo; simp only; omega
  · have hd' : ht (b + e - a) = -1 ∨ ht (b + e - a) = 2 * p + 1 := by
      have h1 := ht_unit u1; have h2 := ht_unit u2
      rw [ht_sub] at h1 h2
      have := ha.2.1; have := hb.2.1; have := he.2.1
      simp only [Dom, HT] at hd this
      simp only [Dom, HT, ht, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at *
      omega
    rcases hd' with hlow | hup
    · obtain ⟨hta, htb, hte⟩ := ht_tri u1 u2 ha.2.1 hb.2.1 he.2.1 hlow
      obtain ⟨j, t, zb, ze, hj, Hb, He, sb, se, gb, ge⟩ := seamL H htb hte u3
      set y := gmapInv p r s w 0 j (b + e - a + t • per r s)
      have gy : gmap p r s w 0 j y = b + e - a + t • per r s := gmap_inv 0 j _
      have iy : Inn1 r s 0 j y := ((ht_gmapL (p := p) (w := w) hj y).2.2).2 (by
        rw [gy, ht_add, ht_per, hlow]; ring)
      have w1 : y - zb ∈ unitVec := rotN_inv_unit (gk 0 j) (by rw [← gmap_sub, gy, gb]; convert v1 using 1; abel)
      have w2 : y - ze ∈ unitVec := rotN_inv_unit (gk 0 j) (by rw [← gmap_sub, gy, ge]; convert v2 using 1; abel)
      have Hy := innerL hj Hb He sb se w1 w2 iy hr hs
      have tb : InC p r s w 0 vb zb := ⟨by norm_num, Hb, by rw [← (gmapL_ch H hj Hb sb).1, gb, chT_shift, hb.2.2]⟩
      have te : InC p r s w 0 ve ze := ⟨by norm_num, He, by rw [← (gmapL_ch H hj He se).1, ge, chT_shift, he.2.2]⟩
      have tX : InC p r s w 0 (ch p r s w 0 y) y := ⟨by norm_num, Hy, rfl⟩
      obtain ⟨c1, c2⟩ := common_of_frame H tb te tX
        (rotN_inv_unit (gk 0 j) (by rw [← gmap_sub, gb, ge]; convert u3 using 1; abel)) w1 w2
      refine ⟨_, c1, c2, ?_⟩
      rw [← ha.2.2, chT]
      by_cases hI : IL r s y
      · rw [chL_I hI]; simp
      · rw [chL_B hI]; apply ht_ne_of; simp only [ht] at hta; simp only; omega
    · obtain ⟨hta, htb, hte⟩ := ht_tri' u1 u2 ha.2.1 hb.2.1 he.2.1 hup
      obtain ⟨j, t, zb, ze, hj, Hb, He, sb, se, gb, ge⟩ := seamU H htb hte u3
      set y := gmapInv p r s w 1 j (b + e - a + t • per r s)
      have gy : gmap p r s w 1 j y = b + e - a + t • per r s := gmap_inv 1 j _
      have iy : Inn1 r s 1 j y := ((ht_gmapU (p := p) (w := w) hj y).2.2).2 (by
        rw [gy, ht_add, ht_per, hup]; ring)
      have w1 : y - zb ∈ unitVec := rotN_inv_unit (gk 1 j) (by rw [← gmap_sub, gy, gb]; convert v1 using 1; abel)
      have w2 : y - ze ∈ unitVec := rotN_inv_unit (gk 1 j) (by rw [← gmap_sub, gy, ge]; convert v2 using 1; abel)
      have Hy := innerU hj Hb He sb se w1 w2 iy hr hs
      have tb : InC p r s w 1 vb zb := ⟨by norm_num, Hb, by rw [← (gmapU_ch H hj Hb sb).1, gb, chT_shift, hb.2.2]⟩
      have te : InC p r s w 1 ve ze := ⟨by norm_num, He, by rw [← (gmapU_ch H hj He se).1, ge, chT_shift, he.2.2]⟩
      have tX : InC p r s w 1 (ch p r s w 1 y) y := ⟨by norm_num, Hy, rfl⟩
      obtain ⟨c1, c2⟩ := common_of_frame H tb te tX
        (rotN_inv_unit (gk 1 j) (by rw [← gmap_sub, gb, ge]; convert u3 using 1; abel)) w1 w2
      refine ⟨_, c1, c2, ?_⟩
      rw [← ha.2.2, chT]
      by_cases hI : IU r s y
      · rw [chU_I hI]; simp
      · rw [chU_B hI]; apply ht_ne_of; simp only [ht] at hta; simp only; omega

theorem not_both_out (H : Hyp p r s w) {c : ℕ} (hc : c < 3) {ρ u : ℤ × ℤ} (h1 : Dom p r s c ρ)
    (h2 : Dom p r s c (ρ + u)) (hu : u ∈ unitVec) (hA : ¬ Dom p r s c (ρ + rotL u))
    (hB : ¬ Dom p r s c (ρ + rotR u)) : False := by
  have hp := H.hp; have hr := H.hr; have hs := H.hs
  obtain ⟨x, y⟩ := ρ
  rw [unit_iff] at hu
  rcases c_cases hc with rfl | rfl | rfl <;>
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Dom, HL, HU, HT, rotL, rotR, Prod.mk_add_mk] at h1 h2 hA hB <;> omega

/-- **Two common neighbours.** -/
theorem two_apex (H : Hyp p r s w) {v x : MV} (h : AdjM p r s w v x) :
    ∃ y z, y ≠ z ∧ AdjM p r s w v y ∧ AdjM p r s w x y ∧ AdjM p r s w v z ∧ AdjM p r s w x z := by
  obtain ⟨c, ρ, ρ', hv, hx, hu⟩ := adj_inC h
  obtain ⟨l1, l2, l3, l4, lne⟩ := apex_units hu
  have eA : ρ + rotL (ρ' - ρ) - ρ = rotL (ρ' - ρ) := by abel
  have eB : ρ + rotR (ρ' - ρ) - ρ = rotR (ρ' - ρ) := by abel
  have eA' : ρ + rotL (ρ' - ρ) - ρ' = rotL (ρ' - ρ) - (ρ' - ρ) := by abel
  have eB' : ρ + rotR (ρ' - ρ) - ρ' = rotR (ρ' - ρ) - (ρ' - ρ) := by abel
  have sm := unit_small hu
  have sA := unit_small l1; have sB := unit_small l2
  have hc := hv.1
  have hρ' : ρ' = ρ + (ρ' - ρ) := by abel
  have sumA : ρ + ρ' - (ρ + rotR (ρ' - ρ)) = ρ + rotL (ρ' - ρ) := by
    have := apex_sum (u := ρ' - ρ)
    rw [← sub_eq_iff_eq_add'.2 this.symm] ; abel
  have sumB : ρ + ρ' - (ρ + rotL (ρ' - ρ)) = ρ + rotR (ρ' - ρ) := by
    have := apex_sum (u := ρ' - ρ)
    rw [← sub_eq_iff_eq_add.2 this.symm]; abel
  by_cases dA : Dom p r s c (ρ + rotL (ρ' - ρ)) <;> by_cases dB : Dom p r s c (ρ + rotR (ρ' - ρ))
  · have iA : InC p r s w c _ (ρ + rotL (ρ' - ρ)) := ⟨hc, dA, rfl⟩
    have iB : InC p r s w c _ (ρ + rotR (ρ' - ρ)) := ⟨hc, dB, rfl⟩
    obtain ⟨a1, a2⟩ := common_of_frame H hv hx iA hu (by rw [eA]; exact l1) (by rw [eA']; exact l3)
    obtain ⟨b1, b2⟩ := common_of_frame H hv hx iB hu (by rw [eB]; exact l2) (by rw [eB']; exact l4)
    refine ⟨_, _, ne_of_chart H iA iB (fun e => lne (by simpa using e)) ?_ ?_, a1, a2, b1, b2⟩ <;>
      simp only [Prod.fst_add] <;> omega
  · -- the apex A is in, B leaves the chart
    have iA : InC p r s w c _ (ρ + rotL (ρ' - ρ)) := ⟨hc, dA, rfl⟩
    obtain ⟨a1, a2⟩ := common_of_frame H hv hx iA hu (by rw [eA]; exact l1) (by rw [eA']; exact l3)
    obtain ⟨y, y1, y2, yn⟩ := outer_apex H iA hv hx (by rw [← neg_sub, eA]; exact unit_neg l1)
      (by rw [← neg_sub, eA']; exact unit_neg l3) hu (by rw [sumB]; exact dB)
    exact ⟨_, y, Ne.symm yn, a1, a2, y1, y2⟩
  · have iB : InC p r s w c _ (ρ + rotR (ρ' - ρ)) := ⟨hc, dB, rfl⟩
    obtain ⟨b1, b2⟩ := common_of_frame H hv hx iB hu (by rw [eB]; exact l2) (by rw [eB']; exact l4)
    obtain ⟨y, y1, y2, yn⟩ := outer_apex H iB hv hx (by rw [← neg_sub, eB]; exact unit_neg l2)
      (by rw [← neg_sub, eB']; exact unit_neg l4) hu (by rw [sumA]; exact dA)
    exact ⟨_, y, Ne.symm yn, b1, b2, y1, y2⟩
  · exact (not_both_out H hc hv.2.1 (by rw [← hρ']; exact hx.2.1) hu dA dB).elim

/-- **Every edge has exactly two common neighbours.** -/
theorem two_common (H : Hyp p r s w) {v x : MV} (h : AdjM p r s w v x) :
    ∃ y z, y ≠ z ∧ ∀ u, (AdjM p r s w v u ∧ AdjM p r s w x u) ↔ (u = y ∨ u = z) := by
  obtain ⟨y, z, hyz, a1, a2, b1, b2⟩ := two_apex H h
  refine ⟨y, z, hyz, fun u => ⟨fun ⟨h1, h2⟩ => ?_, fun hu => ?_⟩⟩
  · by_contra hc
    push_neg at hc
    exact no_three H h a1 a2 b1 b2 h1 h2 hyz (Ne.symm hc.1) (fun e => hc.2 e.symm)
  · rcases hu with rfl | rfl
    exacts [⟨a1, a2⟩, ⟨b1, b2⟩]

end Claude5E10
