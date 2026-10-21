import Formal.Claude5E10Side

/-!
# E10 model: a tube edge on a seam is the image of a cap side edge

Written by a Claude worker (2026-10-20, E10 bridge session).

* `sideL_of_arcs`, `sideU_of_arcs` : two neighbouring boundary points of a cap lie on one side;
* `seamL`, `seamU` : two tube points a unit apart on a seam row are, up to one period, the images
  of two points of one cap side under its isometry.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option linter.style.maxHeartbeats false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

set_option maxHeartbeats 2000000 in
-- piecewise boundary parametrisation, six sides
theorem sideL_of_arcs (hr : 1 ≤ r) (hs : 1 ≤ s) {u u' : ℤ} (h0 : 0 ≤ u)
    (h1 : u < 3 * (2 * r + s)) (h0' : 0 ≤ u') (h1' : u' < 3 * (2 * r + s))
    (ha : ArcAdj r s u u') :
    ∃ i, i < 6 ∧ OnSide r s 0 i (PL r s u) ∧ OnSide r s 0 i (PL r s u') := by
  simp only [ArcAdj] at ha
  by_cases c5 : u ≤ r + s ∧ u' ≤ r + s ∧ ¬ (u = 0 ∧ u' = 3 * (2 * r + s) - 1) ∧
      ¬ (u' = 0 ∧ u = 3 * (2 * r + s) - 1)
  · refine ⟨5, by norm_num, ?_, ?_⟩ <;> simp only [OnSide, PL] <;> split_ifs <;> simp only <;> omega
  by_cases c4 : r + s ≤ u ∧ u ≤ 2 * r + s ∧ r + s ≤ u' ∧ u' ≤ 2 * r + s
  · refine ⟨4, by norm_num, ?_, ?_⟩ <;> simp only [OnSide, PL] <;> split_ifs <;> simp only <;> omega
  by_cases c3 : 2 * r + s ≤ u ∧ u ≤ 3 * r + 2 * s ∧ 2 * r + s ≤ u' ∧ u' ≤ 3 * r + 2 * s
  · refine ⟨3, by norm_num, ?_, ?_⟩ <;> simp only [OnSide, PL] <;> split_ifs <;> simp only <;> omega
  by_cases c2 : 3 * r + 2 * s ≤ u ∧ u ≤ 4 * r + 2 * s ∧ 3 * r + 2 * s ≤ u' ∧ u' ≤ 4 * r + 2 * s
  · refine ⟨2, by norm_num, ?_, ?_⟩ <;> simp only [OnSide, PL] <;> split_ifs <;> simp only <;> omega
  by_cases c1 : 4 * r + 2 * s ≤ u ∧ u ≤ 5 * r + 3 * s ∧ 4 * r + 2 * s ≤ u' ∧ u' ≤ 5 * r + 3 * s
  · refine ⟨1, by norm_num, ?_, ?_⟩ <;> simp only [OnSide, PL] <;> split_ifs <;> simp only <;> omega
  · refine ⟨0, by norm_num, ?_, ?_⟩ <;> simp only [OnSide, PL] <;> split_ifs <;> simp only <;> omega

set_option maxHeartbeats 2000000 in
-- piecewise boundary parametrisation, six sides
theorem sideU_of_arcs (hr : 1 ≤ r) (hs : 1 ≤ s) {u u' : ℤ} (h0 : 0 ≤ u)
    (h1 : u < 3 * (2 * r + s)) (h0' : 0 ≤ u') (h1' : u' < 3 * (2 * r + s))
    (ha : ArcAdj r s u u') :
    ∃ i, i < 6 ∧ OnSide r s 1 i (PU r s u) ∧ OnSide r s 1 i (PU r s u') := by
  simp only [ArcAdj] at ha
  by_cases c0 : u ≤ r + s ∧ u' ≤ r + s ∧ ¬ (u = 0 ∧ u' = 3 * (2 * r + s) - 1) ∧
      ¬ (u' = 0 ∧ u = 3 * (2 * r + s) - 1)
  · refine ⟨0, by norm_num, ?_, ?_⟩ <;> simp only [OnSide, PU] <;> split_ifs <;> simp only <;> omega
  by_cases c1 : r + s ≤ u ∧ u ≤ 2 * r + s ∧ r + s ≤ u' ∧ u' ≤ 2 * r + s
  · refine ⟨1, by norm_num, ?_, ?_⟩ <;> simp only [OnSide, PU] <;> split_ifs <;> simp only <;> omega
  by_cases c2 : 2 * r + s ≤ u ∧ u ≤ 3 * r + 2 * s ∧ 2 * r + s ≤ u' ∧ u' ≤ 3 * r + 2 * s
  · refine ⟨2, by norm_num, ?_, ?_⟩ <;> simp only [OnSide, PU] <;> split_ifs <;> simp only <;> omega
  by_cases c3 : 3 * r + 2 * s ≤ u ∧ u ≤ 4 * r + 2 * s ∧ 3 * r + 2 * s ≤ u' ∧ u' ≤ 4 * r + 2 * s
  · refine ⟨3, by norm_num, ?_, ?_⟩ <;> simp only [OnSide, PU] <;> split_ifs <;> simp only <;> omega
  by_cases c4 : 4 * r + 2 * s ≤ u ∧ u ≤ 5 * r + 3 * s ∧ 4 * r + 2 * s ≤ u' ∧ u' ≤ 5 * r + 3 * s
  · refine ⟨4, by norm_num, ?_, ?_⟩ <;> simp only [OnSide, PU] <;> split_ifs <;> simp only <;> omega
  · refine ⟨5, by norm_num, ?_, ?_⟩ <;> simp only [OnSide, PU] <;> split_ifs <;> simp only <;> omega

theorem small_per (H : Hyp p r s w) {t : ℤ} {u u' : ℤ × ℤ} (hu : u ∈ unitVec) (hu' : u' ∈ unitVec)
    (h : u' = u + t • per r s) : t = 0 := by
  have s1 := unit_small hu
  have s2 := unit_small hu'
  rw [h] at s2
  simp only [per, Prod.fst_add, Prod.smul_mk, smul_eq_mul] at s2
  apply per_small H.hr H.hs <;> linarith [s1.1, s1.2.1, s2.1, s2.2.1]

/-- A lower seam edge of the tube is the image of an edge of one side of the lower cap. -/
theorem seamL (H : Hyp p r s w) {b e : ℤ × ℤ} (hb : ht b = 0) (he : ht e = 0)
    (hu : e - b ∈ unitVec) : ∃ (i : ℕ) (t : ℤ) (zb ze : ℤ × ℤ), i < 6 ∧ HL r s zb ∧ HL r s ze ∧ OnSide r s 0 i zb ∧
      OnSide r s 0 i ze ∧ gmap p r s w 0 i zb = b + t • per r s ∧
        gmap p r s w 0 i ze = e + t • per r s := by
  have hr := H.hr; have hs := H.hs
  have rb := emod_range hr hs b.1
  have re := emod_range hr hs e.1
  have hA : ArcAdj r s (b.1 % (3 * (2 * r + s))) (e.1 % (3 * (2 * r + s))) :=
    tu_seam H hb he ⟨0, by simpa using hu⟩
  obtain ⟨i, hi, s1, s2⟩ := sideL_of_arcs hr hs rb.1 rb.2 re.1 re.2 hA
  obtain ⟨Hb, nb, ab⟩ := PL_spec hr hs rb.1 rb.2
  obtain ⟨He, ne, ae⟩ := PL_spec hr hs re.1 re.2
  have gb := gmapL_ch H (w := w) hi Hb s1
  have ge := gmapL_ch H (w := w) hi He s2
  have cb : ch p r s w 2 (gmap p r s w 0 i (PL r s (b.1 % (3 * (2 * r + s))))) =
      ch p r s w 2 b := by
    rw [gb.1, chL_B nb, ab, chT]; simp only [ht] at hb; rw [hb]
  have ce : ch p r s w 2 (gmap p r s w 0 i (PL r s (e.1 % (3 * (2 * r + s))))) =
      ch p r s w 2 e := by
    rw [ge.1, chL_B ne, ae, chT]; simp only [ht] at he; rw [he]
  obtain ⟨t, tb⟩ := chT_rep hr hs cb
  obtain ⟨t', te⟩ := chT_rep hr hs ce
  have u1 : PL r s (e.1 % (3 * (2 * r + s))) - PL r s (b.1 % (3 * (2 * r + s))) ∈ unitVec :=
    (unit_PL hr hs rb.1 rb.2 re.1 re.2).2 hA
  have hsub := gmap_sub (p := p) (r := r) (s := s) (w := w) 0 i
    (PL r s (e.1 % (3 * (2 * r + s)))) (PL r s (b.1 % (3 * (2 * r + s))))
  have eq : t' = t := by
    have h' : e - b = rotN (gk 0 i) (PL r s (e.1 % (3 * (2 * r + s))) -
        PL r s (b.1 % (3 * (2 * r + s)))) + (t' - t) • per r s := by
      rw [← hsub]
      generalize gmap p r s w 0 i (PL r s (b.1 % (3 * (2 * r + s)))) = Gb at tb ⊢
      generalize gmap p r s w 0 i (PL r s (e.1 % (3 * (2 * r + s)))) = Ge at te ⊢
      subst tb te
      ext <;> simp only [per, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
        Prod.smul_mk, smul_eq_mul] <;> ring
    have := small_per H (rotN_unit' (gk 0 i) u1) hu h'
    omega
  subst eq
  refine ⟨i, -t', _, _, hi, Hb, He, s1, s2, ?_, ?_⟩
  · generalize gmap p r s w 0 i (PL r s (b.1 % (3 * (2 * r + s)))) = Gb at tb ⊢
    subst tb; ext <;> simp [per, Prod.smul_mk, smul_eq_mul]
  · generalize gmap p r s w 0 i (PL r s (e.1 % (3 * (2 * r + s)))) = Ge at te ⊢
    subst te; ext <;> simp [per, Prod.smul_mk, smul_eq_mul]

/-- The arc of the upper cap carried to a tube position. -/
def unwrapU (r s w u : ℤ) : ℤ := if w ≤ u then u - w else u - w + 3 * (2 * r + s)

theorem unwrapU_spec (H : Hyp p r s w) {u : ℤ} (h0 : 0 ≤ u) (h1 : u < 3 * (2 * r + s)) :
    0 ≤ unwrapU r s w u ∧ unwrapU r s w u < 3 * (2 * r + s) ∧
      wrap r s (unwrapU r s w u + w) = u := by
  have := H.hw0; have := H.hw1
  unfold unwrapU wrap; split_ifs <;> omega

/-- An upper seam edge of the tube is the image of an edge of one side of the upper cap. -/
theorem seamU (H : Hyp p r s w) {b e : ℤ × ℤ} (hb : ht b = 2 * p) (he : ht e = 2 * p)
    (hu : e - b ∈ unitVec) : ∃ (i : ℕ) (t : ℤ) (zb ze : ℤ × ℤ), i < 6 ∧ HU r s zb ∧ HU r s ze ∧ OnSide r s 1 i zb ∧
      OnSide r s 1 i ze ∧ gmap p r s w 1 i zb = b + t • per r s ∧
        gmap p r s w 1 i ze = e + t • per r s := by
  have hr := H.hr; have hs := H.hs
  have rb := emod_range hr hs b.1
  have re := emod_range hr hs e.1
  have hA : ArcAdj r s (b.1 % (3 * (2 * r + s))) (e.1 % (3 * (2 * r + s))) :=
    tu_seam_top H hb he ⟨0, by simpa using hu⟩
  obtain ⟨xb0, xb1, xb⟩ := unwrapU_spec H rb.1 rb.2
  obtain ⟨xe0, xe1, xe⟩ := unwrapU_spec H re.1 re.2
  have hA' : ArcAdj r s (unwrapU r s w (b.1 % (3 * (2 * r + s))))
      (unwrapU r s w (e.1 % (3 * (2 * r + s)))) := by
    rw [← arcAdj_wrap H xb0 xb1 xe0 xe1, xb, xe]; exact hA
  obtain ⟨i, hi, s1, s2⟩ := sideU_of_arcs hr hs xb0 xb1 xe0 xe1 hA'
  obtain ⟨Hb, nb, ab⟩ := PU_spec hr hs xb0 xb1
  obtain ⟨He, ne, ae⟩ := PU_spec hr hs xe0 xe1
  have gb := gmapU_ch H hi Hb s1
  have ge := gmapU_ch H hi He s2
  have cb : ch p r s w 2 (gmap p r s w 1 i (PU r s (unwrapU r s w (b.1 % (3 * (2 * r + s)))))) =
      ch p r s w 2 b := by
    rw [gb.1, chU_B nb, ab, xb, chT]; simp only [ht] at hb; rw [hb]
  have ce : ch p r s w 2 (gmap p r s w 1 i (PU r s (unwrapU r s w (e.1 % (3 * (2 * r + s)))))) =
      ch p r s w 2 e := by
    rw [ge.1, chU_B ne, ae, xe, chT]; simp only [ht] at he; rw [he]
  obtain ⟨t, tb⟩ := chT_rep hr hs cb
  obtain ⟨t', te⟩ := chT_rep hr hs ce
  have u1 := (unit_PU hr hs xb0 xb1 xe0 xe1).2 hA'
  have hsub := gmap_sub (p := p) (r := r) (s := s) (w := w) 1 i
    (PU r s (unwrapU r s w (e.1 % (3 * (2 * r + s)))))
    (PU r s (unwrapU r s w (b.1 % (3 * (2 * r + s)))))
  have eq : t' = t := by
    have h' : e - b = rotN (gk 1 i) (PU r s (unwrapU r s w (e.1 % (3 * (2 * r + s)))) -
        PU r s (unwrapU r s w (b.1 % (3 * (2 * r + s))))) + (t' - t) • per r s := by
      rw [← hsub]
      generalize gmap p r s w 1 i (PU r s (unwrapU r s w (b.1 % (3 * (2 * r + s))))) = Gb at tb ⊢
      generalize gmap p r s w 1 i (PU r s (unwrapU r s w (e.1 % (3 * (2 * r + s))))) = Ge at te ⊢
      subst tb te
      ext <;> simp only [per, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
        Prod.smul_mk, smul_eq_mul] <;> ring
    have := small_per H (rotN_unit' (gk 1 i) u1) hu h'
    omega
  subst eq
  refine ⟨i, -t', _, _, hi, Hb, He, s1, s2, ?_, ?_⟩
  · generalize gmap p r s w 1 i (PU r s (unwrapU r s w (b.1 % (3 * (2 * r + s))))) = Gb at tb ⊢
    subst tb; ext <;> simp [per, Prod.smul_mk, smul_eq_mul]
  · generalize gmap p r s w 1 i (PU r s (unwrapU r s w (e.1 % (3 * (2 * r + s))))) = Ge at te ⊢
    subst te; ext <;> simp [per, Prod.smul_mk, smul_eq_mul]

end Claude5E10
