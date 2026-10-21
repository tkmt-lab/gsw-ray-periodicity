import Formal.Claude5E10Deg2

/-!
# E10 model: every vertex has degree 6, the twelve corners degree 5

Written by a Claude worker (2026-10-20, E10 bridge session).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

/-- Unit steps upwards / downwards in the tube. -/
def A6 : Finset (ℤ × ℤ) := {(1, 0), (0, 1), (-1, 1), (1, -1)}
def B6 : Finset (ℤ × ℤ) := {(-1, 0), (0, -1), (-1, 1), (1, -1)}

theorem mem_A6 {e : ℤ × ℤ} : e ∈ A6 ↔ e ∈ unitVec ∧ 0 ≤ e.1 + e.2 := by
  constructor
  · intro h; simp only [A6, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl <;> simp [unitVec]
  · rintro ⟨h, h'⟩; rw [unit_iff] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [A6] at h' ⊢

theorem mem_B6 {e : ℤ × ℤ} : e ∈ B6 ↔ e ∈ unitVec ∧ e.1 + e.2 ≤ 0 := by
  constructor
  · intro h; simp only [B6, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl <;> simp [unitVec]
  · rintro ⟨h, h'⟩; rw [unit_iff] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [B6] at h' ⊢

theorem arc_nb (H : Hyp p r s w) {u a : ℤ} (hu0 : 0 ≤ u) (hu1 : u < 3 * (2 * r + s))
    (ha0 : 0 ≤ a) (ha1 : a < 3 * (2 * r + s)) (h : ArcAdj r s u a) :
    a = (u + 1) % (3 * (2 * r + s)) ∨ a = (u + -1) % (3 * (2 * r + s)) := by
  have hP : 0 < 3 * (2 * r + s) := by have := H.hr; have := H.hs; omega
  simp only [ArcAdj] at h
  rcases h with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; rw [emod_eq_of hP (q := 0) (b := a) (by omega) ha0 ha1]
  · right; rw [emod_eq_of hP (q := 0) (b := a) (by omega) ha0 ha1]
  · right; rw [emod_eq_of hP (q := -1) (b := a) (by omega) ha0 ha1]
  · left; rw [emod_eq_of hP (q := 1) (b := a) (by omega) ha0 ha1]

theorem tube_img_inj (H : Hyp p r s w) (z : ℤ × ℤ) {e e' : ℤ × ℤ} (he : e ∈ unitVec)
    (he' : e' ∈ unitVec) (h : ch p r s w 2 (z + e) = ch p r s w 2 (z + e')) : e = e' := by
  have s1 := unit_small he; have s2 := unit_small he'
  have := chT_near H.hr H.hs h (by simp only [Prod.fst_add]; omega) (by simp only [Prod.fst_add]; omega)
  simpa using this

/-- The neighbours of a lower seam point. -/
def SL (p r s w u : ℤ) : Finset MV :=
  A6.image (fun e => ch p r s w 2 ((u, -u) + e)) ∪ (inL r s u).image (fun e => ((0 : ℤ), PL r s u + e))

def SU (p r s w u : ℤ) : Finset MV :=
  B6.image (fun e => ch p r s w 2 ((u, 2 * p - u) + e)) ∪
    (inU r s (unwrapU r s w u)).image (fun e => ((1 : ℤ), PU r s (unwrapU r s w u) + e))

theorem inC_low (H : Hyp p r s w) {u : ℤ} (hu0 : 0 ≤ u) (hu1 : u < 3 * (2 * r + s)) :
    InC p r s w 2 (2, (u, 0)) (u, -u) ∧ InC p r s w 0 (2, (u, 0)) (PL r s u) := by
  obtain ⟨a, b, c⟩ := PL_spec H.hr H.hs hu0 hu1
  have hp := H.hp
  refine ⟨⟨by norm_num, by simp only [Dom, HT]; omega, ?_⟩, ⟨by norm_num, a, ?_⟩⟩
  · rw [chT]; simp only [Prod.mk.injEq, true_and]; exact ⟨Int.emod_eq_of_lt hu0 hu1, by ring⟩
  · rw [chL_B b, c]

theorem inC_up (H : Hyp p r s w) {u : ℤ} (hu0 : 0 ≤ u) (hu1 : u < 3 * (2 * r + s)) :
    InC p r s w 2 (2, (u, 2 * p)) (u, 2 * p - u) ∧
      InC p r s w 1 (2, (u, 2 * p)) (PU r s (unwrapU r s w u)) := by
  obtain ⟨x0, x1, xw⟩ := unwrapU_spec H hu0 hu1
  obtain ⟨a, b, c⟩ := PU_spec H.hr H.hs x0 x1
  have hp := H.hp
  refine ⟨⟨by norm_num, by simp only [Dom, HT]; omega, ?_⟩, ⟨by norm_num, a, ?_⟩⟩
  · rw [chT]; simp only [Prod.mk.injEq, true_and]; exact ⟨Int.emod_eq_of_lt hu0 hu1, by ring⟩
  · rw [chU_B b, c, xw]

theorem adj_low (H : Hyp p r s w) {u : ℤ} (hu0 : 0 ≤ u) (hu1 : u < 3 * (2 * r + s))
    (x : MV) : AdjM p r s w (2, (u, 0)) x ↔ x ∈ SL p r s w u := by
  have hp := H.hp; have hr := H.hr; have hs := H.hs
  obtain ⟨iT, iL⟩ := inC_low H hu0 hu1
  constructor
  · intro h
    obtain ⟨c, ρ, e, hρ, he, hd, rfl⟩ := adj_rep h
    rcases rep_low H hu0 hu1 hρ with ⟨rfl, t, rfl⟩ | ⟨rfl, rfl⟩
    · apply Finset.mem_union_left
      refine Finset.mem_image.2 ⟨e, mem_A6.2 ⟨he, ?_⟩, ?_⟩
      · simp only [Dom, HT, per, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul] at hd
        nlinarith [hd.1]
      · rw [show (u, -u) + t • per r s + e = (u, -u) + e + t • per r s by abel, chT_shift]
    · by_cases hI : IL r s (PL r s u + e)
      · apply Finset.mem_union_right
        refine Finset.mem_image.2 ⟨e, ?_, ?_⟩
        · simp only [inL, Finset.mem_filter, mem_U6]; exact ⟨he, hI⟩
        · rw [chL_I hI]
      · apply Finset.mem_union_left
        obtain ⟨a, b, c⟩ := PL_spec hr hs hu0 hu1
        have hd' : HL r s (PL r s u + e) := by simpa [Dom] using hd
        have hA := (unit_arcL hr hs a b hd' hI).1 (by simpa using he)
        rw [c] at hA
        have r2 := aL_range hr hs hd' hI
        rw [chL_B hI]
        rcases arc_nb H hu0 hu1 r2.1 r2.2 hA with h1 | h1
        · refine Finset.mem_image.2 ⟨(1, -1), by decide, ?_⟩
          rw [chT, h1]; simp; ring
        · refine Finset.mem_image.2 ⟨(-1, 1), by decide, ?_⟩
          rw [chT, h1]; simp; ring
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
      obtain ⟨he1, he2⟩ := mem_A6.1 he
      have := unit_small he1
      exact adj_of_rep H iT he1 (by simp only [Dom, HT, Prod.fst_add, Prod.snd_add]; omega)
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
      simp only [inL, Finset.mem_filter, mem_U6] at he
      have := adj_of_rep H iL he.1 (by simp only [Dom]; simp only [IL, HL] at he ⊢; omega)
      rwa [chL_I he.2] at this

theorem adj_up (H : Hyp p r s w) {u : ℤ} (hu0 : 0 ≤ u) (hu1 : u < 3 * (2 * r + s))
    (x : MV) : AdjM p r s w (2, (u, 2 * p)) x ↔ x ∈ SU p r s w u := by
  have hp := H.hp; have hr := H.hr; have hs := H.hs
  obtain ⟨iT, iU⟩ := inC_up H hu0 hu1
  obtain ⟨x0, x1, xw⟩ := unwrapU_spec H hu0 hu1
  constructor
  · intro h
    obtain ⟨c, ρ, e, hρ, he, hd, rfl⟩ := adj_rep h
    rcases rep_up H hu0 hu1 hρ with ⟨rfl, t, rfl⟩ | ⟨rfl, rfl⟩
    · apply Finset.mem_union_left
      refine Finset.mem_image.2 ⟨e, mem_B6.2 ⟨he, ?_⟩, ?_⟩
      · simp only [Dom, HT, per, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul] at hd
        nlinarith [hd.2]
      · rw [show (u, 2 * p - u) + t • per r s + e = (u, 2 * p - u) + e + t • per r s by abel,
          chT_shift]
    · by_cases hI : IU r s (PU r s (unwrapU r s w u) + e)
      · apply Finset.mem_union_right
        refine Finset.mem_image.2 ⟨e, ?_, ?_⟩
        · simp only [inU, Finset.mem_filter, mem_U6]; exact ⟨he, hI⟩
        · rw [chU_I hI]
      · apply Finset.mem_union_left
        obtain ⟨a, b, c⟩ := PU_spec hr hs x0 x1
        have hd' : HU r s (PU r s (unwrapU r s w u) + e) := by simpa [Dom] using hd
        have hA := (unit_arcU hr hs a b hd' hI).1 (by simpa using he)
        rw [c] at hA
        have r2 := aU_range hr hs hd' hI
        rw [← arcAdj_wrap H x0 x1 r2.1 r2.2, xw] at hA
        rw [chU_B hI]
        have r3 := wrap_range hr hs (x := aU r s (PU r s (unwrapU r s w u) + e) + w)
          (by have := H.hw0; omega) (by have := H.hw1; omega)
        rcases arc_nb H hu0 hu1 r3.1 r3.2 hA with h1 | h1
        · refine Finset.mem_image.2 ⟨(1, -1), by decide, ?_⟩
          rw [chT, h1]; simp; omega
        · refine Finset.mem_image.2 ⟨(-1, 1), by decide, ?_⟩
          rw [chT, h1]; simp; omega
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
      obtain ⟨he1, he2⟩ := mem_B6.1 he
      have := unit_small he1
      exact adj_of_rep H iT he1 (by simp only [Dom, HT, Prod.fst_add, Prod.snd_add]; omega)
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 h
      simp only [inU, Finset.mem_filter, mem_U6] at he
      have := adj_of_rep H iU he.1 (by simp only [Dom]; simp only [IU, HU] at he ⊢; omega)
      rwa [chU_I he.2] at this

end Claude5E10
