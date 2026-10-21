import Formal.Claude5E10Three

/-!
# E10 model: no edge has three common neighbours (part 2)

Written by a Claude worker (2026-10-20, E10 bridge session), following `Claude5D14Three.lean`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.style.maxHeartbeats false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

/-- Left and right apex directions of a unit step. -/
def rotL (u : ℤ × ℤ) : ℤ × ℤ := (-u.2, u.1 + u.2)
def rotR (u : ℤ × ℤ) : ℤ × ℤ := (u.1 + u.2, -u.1)

theorem apex2 {ρ ρ' ξ : ℤ × ℤ} (h1 : ρ' - ρ ∈ unitVec) (h2 : ξ - ρ ∈ unitVec)
    (h3 : ξ - ρ' ∈ unitVec) : ξ = ρ + rotL (ρ' - ρ) ∨ ξ = ρ + rotR (ρ' - ρ) := by
  rw [unit_sub] at h1 h2 h3
  simp only [U2] at h1 h2 h3
  simp only [rotL, rotR, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  omega

set_option maxHeartbeats 1000000 in
theorem apex_PL (hr : 1 ≤ r) (hs : 1 ≤ s) {l l' : ℤ} (h0 : 0 ≤ l) (h1 : l < 3 * (2 * r + s))
    (h0' : 0 ≤ l') (h1' : l' < 3 * (2 * r + s)) (ha : ArcAdj r s l l')
    (hA : HL r s (PL r s l + rotL (PL r s l' - PL r s l)))
    (hB : HL r s (PL r s l + rotR (PL r s l' - PL r s l))) : False := by
  simp only [ArcAdj] at ha
  simp only [HL, rotL, rotR, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hA hB
  unfold PL at hA hB
  split_ifs at hA hB <;> simp only at hA hB <;> omega

set_option maxHeartbeats 1000000 in
theorem apex_PU (hr : 1 ≤ r) (hs : 1 ≤ s) {l l' : ℤ} (h0 : 0 ≤ l) (h1 : l < 3 * (2 * r + s))
    (h0' : 0 ≤ l') (h1' : l' < 3 * (2 * r + s)) (ha : ArcAdj r s l l')
    (hA : HU r s (PU r s l + rotL (PU r s l' - PU r s l)))
    (hB : HU r s (PU r s l + rotR (PU r s l' - PU r s l))) : False := by
  simp only [ArcAdj] at ha
  simp only [HU, rotL, rotR, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hA hB
  unfold PU at hA hB
  split_ifs at hA hB <;> simp only at hA hB <;> omega

theorem apex_T {ρ ρ' : ℤ × ℤ} (hs : ρ.1 + ρ.2 = ρ'.1 + ρ'.2) (hu : ρ' - ρ ∈ unitVec)
    (hb : ρ.1 + ρ.2 = 0 ∨ ρ.1 + ρ.2 = 2 * p)
    (hA : HT p (ρ + rotL (ρ' - ρ))) (hB : HT p (ρ + rotR (ρ' - ρ))) : False := by
  rw [unit_sub] at hu
  simp only [U2] at hu
  simp only [HT, rotL, rotR, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hA hB
  omega

/-- **An edge in two charts has at most one apex in each.** -/
theorem seam_apex (H : Hyp p r s w) {c c' : ℕ} (hne : c ≠ c') {v x : MV}
    {ρ ρ' σ σ' : ℤ × ℤ} (hv : InC p r s w c v ρ) (hx : InC p r s w c x ρ')
    (hv' : InC p r s w c' v σ) (hx' : InC p r s w c' x σ') (hu : ρ' - ρ ∈ unitVec)
    (h1 : Dom p r s c (ρ + rotL (ρ' - ρ))) (h2 : Dom p r s c (ρ + rotR (ρ' - ρ))) : False := by
  have hc := hv.1
  have hc' := hv'.1
  have hr := H.hr; have hs := H.hs
  rcases c_cases hc with rfl | rfl | rfl <;> rcases c_cases hc' with rfl | rfl | rfl
  · exact hne rfl
  · exact not_L_U H hv hv'
  · obtain ⟨a, -, -⟩ := inC_L_T H hv hv'
    obtain ⟨a', -, -⟩ := inC_L_T H hx hx'
    have l1 := aL_range hr hs hv.2.1 a
    have l2 := aL_range hr hs hx.2.1 a'
    have hA := (unit_arcL hr hs hv.2.1 a hx.2.1 a').1 hu
    rw [eq_PL hr hs hv.2.1 a, eq_PL hr hs hx.2.1 a'] at h1 h2
    exact apex_PL hr hs l1.1 l1.2 l2.1 l2.2 hA h1 h2
  · exact not_L_U H hv' hv
  · exact hne rfl
  · obtain ⟨a, -, -⟩ := inC_U_T H hv hv'
    obtain ⟨a', -, -⟩ := inC_U_T H hx hx'
    have l1 := aU_range hr hs hv.2.1 a
    have l2 := aU_range hr hs hx.2.1 a'
    have hA := (unit_arcU hr hs hv.2.1 a hx.2.1 a').1 hu
    rw [eq_PU hr hs hv.2.1 a, eq_PU hr hs hx.2.1 a'] at h1 h2
    exact apex_PU hr hs l1.1 l1.2 l2.1 l2.2 hA h1 h2
  · obtain ⟨-, b, -⟩ := inC_L_T H hv' hv
    obtain ⟨-, b', -⟩ := inC_L_T H hx' hx
    exact apex_T (by rw [b, b']) hu (Or.inl b) h1 h2
  · obtain ⟨-, b, -⟩ := inC_U_T H hv' hv
    obtain ⟨-, b', -⟩ := inC_U_T H hx' hx
    exact apex_T (by rw [b, b']) hu (Or.inr b) h1 h2
  · exact hne rfl

/-- A common neighbour of an edge, placed in a chart with the edge, at an apex. -/
theorem place (H : Hyp p r s w) {v x y : MV} (hvx : AdjM p r s w v x)
    (hvy : AdjM p r s w v y) (hxy : AdjM p r s w x y) : ∃ c a b q, InC p r s w c v a ∧
      InC p r s w c x b ∧ InC p r s w c y q ∧ b - a ∈ unitVec ∧
        (q = a + rotL (b - a) ∨ q = a + rotR (b - a)) := by
  obtain ⟨c, a, b, q, ha, hb, hq, u0, u1, u2⟩ := tri H hvx hvy hxy
  exact ⟨c, a, b, q, ha, hb, hq, u0, apex2 u0 u1 u2⟩

/-- Two placements in one chart can be aligned on the edge. -/
theorem align (H : Hyp p r s w) {c : ℕ} {v x y : MV} {a b a' b' q : ℤ × ℤ}
    (ha : InC p r s w c v a) (hb : InC p r s w c x b) (hu : b - a ∈ unitVec)
    (ha' : InC p r s w c v a') (hb' : InC p r s w c x b') (hu' : b' - a' ∈ unitVec)
    (hq : InC p r s w c y q) (hq' : q = a' + rotL (b' - a') ∨ q = a' + rotR (b' - a')) :
    ∃ q', InC p r s w c y q' ∧ (q' = a + rotL (b - a) ∨ q' = a + rotR (b - a)) := by
  by_cases hc : c < 2
  · obtain rfl := (inC_inj01 H hc ha ha').1 rfl
    obtain rfl := (inC_inj01 H hc hb hb').1 rfl
    exact ⟨q, hq, hq'⟩
  have hc2 : c = 2 := by have := ha.1; omega
  subst hc2
  obtain ⟨t, rfl⟩ := inC_rep2 H ha ha'
  have hb'' := inC_shift hb' (-t)
  have e : b' + (-t) • per r s = b := by
    have s1 := unit_small hu
    have s2 := unit_small hu'
    refine ((inC_near2 H hb'' hb ?_ ?_).1 rfl) <;>
      simp only [per, Prod.fst_add, Prod.fst_sub, Prod.smul_mk, smul_eq_mul] at s1 s2 ⊢ <;>
      linarith
  refine ⟨q + (-t) • per r s, inC_shift hq (-t), ?_⟩
  have hd : b' - (a + t • per r s) = b - a := by
    rw [← e]; simp only [per, Prod.smul_mk, smul_eq_mul, Prod.ext_iff, Prod.fst_add,
      Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; constructor <;> ring
  rw [hd] at hq'
  rcases hq' with rfl | rfl
  · left; simp only [per, Prod.smul_mk, smul_eq_mul, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
    constructor <;> ring
  · right; simp only [per, Prod.smul_mk, smul_eq_mul, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
    constructor <;> ring

theorem both_apex {c : ℕ} {y z : MV} {a b q q' : ℤ × ℤ}
    (hy : InC p r s w c y q) (hz : InC p r s w c z q')
    (hq : q = a + rotL (b - a) ∨ q = a + rotR (b - a))
    (hq' : q' = a + rotL (b - a) ∨ q' = a + rotR (b - a)) (hyz : y ≠ z) :
    Dom p r s c (a + rotL (b - a)) ∧ Dom p r s c (a + rotR (b - a)) := by
  have hne : q ≠ q' := fun e => hyz (by rw [← hy.2.2, ← hz.2.2, e])
  rcases hq with rfl | rfl <;> rcases hq' with rfl | rfl
  · exact (hne rfl).elim
  · exact ⟨hy.2.1, hz.2.1⟩
  · exact ⟨hz.2.1, hy.2.1⟩
  · exact (hne rfl).elim

/-- **No edge has three common neighbours** (`p, r, s ≥ 1`). -/
theorem no_three (H : Hyp p r s w) {v x y z t : MV} (hvx : AdjM p r s w v x)
    (hvy : AdjM p r s w v y) (hxy : AdjM p r s w x y) (hvz : AdjM p r s w v z)
    (hxz : AdjM p r s w x z) (hvt : AdjM p r s w v t) (hxt : AdjM p r s w x t) (hyz : y ≠ z)
    (hyt : y ≠ t) (hzt : z ≠ t) : False := by
  obtain ⟨cy, a, b, qy, ha, hb, hqy, hu, hy⟩ := place H hvx hvy hxy
  obtain ⟨cz, a', b', qz, ha', hb', hqz, hu', hz⟩ := place H hvx hvz hxz
  obtain ⟨ct, a'', b'', qt, ha'', hb'', hqt, hu'', ht⟩ := place H hvx hvt hxt
  by_cases e1 : cz = cy
  · subst e1
    obtain ⟨qz', hqz', hz'⟩ := align H ha hb hu ha' hb' hu' hqz hz
    have hD := both_apex hqy hqz' hy hz' hyz
    by_cases e2 : ct = cz
    · subst e2
      obtain ⟨qt', hqt', ht'⟩ := align H ha hb hu ha'' hb'' hu'' hqt ht
      have n1 : qy ≠ qz' := fun e => hyz (by rw [← hqy.2.2, ← hqz'.2.2, e])
      have n2 : qy ≠ qt' := fun e => hyt (by rw [← hqy.2.2, ← hqt'.2.2, e])
      have n3 : qz' ≠ qt' := fun e => hzt (by rw [← hqz'.2.2, ← hqt'.2.2, e])
      rcases hy with rfl | rfl <;> rcases hz' with rfl | rfl <;> rcases ht' with rfl | rfl <;>
        simp_all
    · exact seam_apex H (Ne.symm e2) ha hb ha'' hb'' hu hD.1 hD.2
  · by_cases e2 : ct = cy
    · subst e2
      obtain ⟨qt', hqt', ht'⟩ := align H ha hb hu ha'' hb'' hu'' hqt ht
      have hD := both_apex hqy hqt' hy ht' hyt
      exact seam_apex H (Ne.symm e1) ha hb ha' hb' hu hD.1 hD.2
    · by_cases e3 : ct = cz
      · subst e3
        obtain ⟨qt', hqt', ht'⟩ := align H ha' hb' hu' ha'' hb'' hu'' hqt ht
        have hD := both_apex hqz hqt' hz ht' hzt
        exact seam_apex H e1 ha' hb' ha hb hu' hD.1 hD.2
      · -- three different charts: the edge would lie in both caps
        exfalso
        have := ha.1; have := ha'.1; have := ha''.1
        rcases c_cases ha.1 with f0 | f0 | f0 <;> rcases c_cases ha'.1 with f1 | f1 | f1 <;>
          rcases c_cases ha''.1 with f2 | f2 | f2 <;> subst f0 f1 f2 <;> first
          | exact e1 rfl | exact e2 rfl | exact e3 rfl
          | exact not_L_U H ha ha' | exact not_L_U H ha' ha
          | exact not_L_U H ha ha'' | exact not_L_U H ha'' ha
          | exact not_L_U H ha' ha'' | exact not_L_U H ha'' ha'

end Claude5E10
