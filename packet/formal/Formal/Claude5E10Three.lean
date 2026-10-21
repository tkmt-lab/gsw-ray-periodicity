import Formal.Claude5E10Chart

/-!
# E10 model: no edge has three common neighbours

Written by a Claude worker (2026-10-20, E10 bridge session), following `Claude5D14Three.lean`;
the tube chart is periodic, so tube representatives are moved by periods where needed.

* `InC c v ρ` : the vertex `v` is the point `ρ` of chart `c`;
* `cd`        : unit steps are seen in every chart containing both ends (in the tube up to a
                period);
* `tri`       : three mutually adjacent vertices are a unit triangle of one chart;
* `seam_apex` : an edge in two charts has at most one apex inside each of them;
* `no_three`  : an edge has at most two common neighbours (`p, r, s ≥ 1`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

/-- The standing hypotheses. -/
structure Hyp (p r s w : ℤ) : Prop where
  hp : 1 ≤ p
  hr : 1 ≤ r
  hs : 1 ≤ s
  hw0 : 0 ≤ w
  hw1 : w < 3 * (2 * r + s)

/-- `v` is the point `ρ` of chart `c`. -/
def InC (p r s w : ℤ) (c : ℕ) (v : MV) (ρ : ℤ × ℤ) : Prop :=
  c < 3 ∧ Dom p r s c ρ ∧ ch p r s w c ρ = v

theorem adj_inC {v x : MV} (h : AdjM p r s w v x) :
    ∃ c ρ ρ', InC p r s w c v ρ ∧ InC p r s w c x ρ' ∧ ρ' - ρ ∈ unitVec := by
  obtain ⟨-, c, hc, z, u, h1, h2, hu, rfl, rfl⟩ := h
  exact ⟨c, z, z + u, ⟨hc, h1, rfl⟩, ⟨hc, h2, rfl⟩, by simpa using hu⟩

theorem inC_shift {v : MV} {ρ : ℤ × ℤ} (h : InC p r s w 2 v ρ) (t : ℤ) :
    InC p r s w 2 v (ρ + t • per r s) :=
  ⟨h.1, HT_shift t h.2.1, (chT_shift ρ t).trans h.2.2⟩

theorem inC_rep2 (H : Hyp p r s w) {v : MV} {ρ ρ' : ℤ × ℤ} (h : InC p r s w 2 v ρ)
    (h' : InC p r s w 2 v ρ') : ∃ t : ℤ, ρ' = ρ + t • per r s :=
  chT_rep H.hr H.hs (h.2.2.trans h'.2.2.symm)

theorem inC_near2 (H : Hyp p r s w) {v x : MV} {ρ ρ' : ℤ × ℤ} (h : InC p r s w 2 v ρ)
    (h' : InC p r s w 2 x ρ') (h1 : -6 < ρ'.1 - ρ.1) (h2 : ρ'.1 - ρ.1 < 6) :
    v = x ↔ ρ = ρ' := by
  constructor
  · rintro rfl; exact chT_near H.hr H.hs (h.2.2.trans h'.2.2.symm) h1 h2
  · rintro rfl; exact h.2.2.symm.trans h'.2.2

theorem inC_inj01 (H : Hyp p r s w) {c : ℕ} (hc : c < 2) {v x : MV} {ρ ρ' : ℤ × ℤ}
    (h1 : InC p r s w c v ρ) (h2 : InC p r s w c x ρ') : v = x ↔ ρ = ρ' := by
  constructor
  · rintro rfl
    have e := h1.2.2.trans h2.2.2.symm
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
    · exact chL_inj H.hr H.hs h1.2.1 h2.2.1 e
    · exact chU_inj H.hr H.hs H.hw0 H.hw1 h1.2.1 h2.2.1 e
  · rintro rfl; exact h1.2.2.symm.trans h2.2.2

/-! ## Arithmetic of positions on the tube circles -/

theorem emod_eq_of {P y q b : ℤ} (hP : 0 < P) (h : y = P * q + b) (h0 : 0 ≤ b) (h1 : b < P) :
    y % P = b := by
  rw [h, Int.mul_add_emod_self_left, Int.emod_eq_of_lt h0 h1]

theorem emod_decomp {P : ℤ} (hP : 0 < P) (x : ℤ) :
    x = P * (x / P) + x % P ∧ 0 ≤ x % P ∧ x % P < P :=
  ⟨(Int.mul_ediv_add_emod x P).symm, Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hP⟩

/-- Neighbouring residues come from neighbouring integers, up to a period. -/
theorem arcAdj_lift (H : Hyp p r s w) {x y : ℤ}
    (h : ArcAdj r s (x % (3 * (2 * r + s))) (y % (3 * (2 * r + s)))) :
    ∃ t ε : ℤ, (ε = 1 ∨ ε = -1) ∧ y = x + ε + 3 * (2 * r + s) * t := by
  have hP : 0 < 3 * (2 * r + s) := by have := H.hr; have := H.hs; omega
  obtain ⟨ex, -, -⟩ := emod_decomp hP x
  obtain ⟨ey, -, -⟩ := emod_decomp hP y
  generalize x % (3 * (2 * r + s)) = a at h ex
  generalize y % (3 * (2 * r + s)) = b at h ey
  generalize x / (3 * (2 * r + s)) = q at ex
  generalize y / (3 * (2 * r + s)) = q' at ey
  simp only [ArcAdj] at h
  rcases h with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨q' - q, 1, Or.inl rfl, by rw [ex, ey, h]; ring⟩
  · exact ⟨q' - q, -1, Or.inr rfl, by rw [ex, ey, h]; ring⟩
  · exact ⟨q' - q + 1, -1, Or.inr rfl, by rw [ex, ey, h1, h2]; ring⟩
  · exact ⟨q' - q - 1, 1, Or.inl rfl, by rw [ex, ey, h1, h2]; ring⟩

theorem arcAdj_of (H : Hyp p r s w) {x y t ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (h : y = x + ε + 3 * (2 * r + s) * t) :
    ArcAdj r s (x % (3 * (2 * r + s))) (y % (3 * (2 * r + s))) := by
  have hP : 0 < 3 * (2 * r + s) := by have := H.hr; have := H.hs; omega
  obtain ⟨ex, h0, h1⟩ := emod_decomp hP x
  generalize x % (3 * (2 * r + s)) = a at ex h0 h1
  generalize x / (3 * (2 * r + s)) = q at ex
  simp only [ArcAdj]
  rcases hε with rfl | rfl
  · by_cases ha : a + 1 < 3 * (2 * r + s)
    · rw [emod_eq_of hP (q := q + t) (b := a + 1) (by rw [h, ex]; ring) (by omega) ha]; omega
    · rw [emod_eq_of hP (q := q + t + 1) (b := 0) (by rw [h, ex]; nlinarith) (by omega) hP]
      omega
  · by_cases ha : 0 ≤ a - 1
    · rw [emod_eq_of hP (q := q + t) (b := a - 1) (by rw [h, ex]; ring) ha (by omega)]; omega
    · rw [emod_eq_of hP (q := q + t - 1) (b := 3 * (2 * r + s) - 1) (by rw [h, ex]; nlinarith)
        (by omega) (by omega)]
      omega

theorem arcAdj_wrap (H : Hyp p r s w) {a b : ℤ} (ha0 : 0 ≤ a) (ha1 : a < 3 * (2 * r + s))
    (hb0 : 0 ≤ b) (hb1 : b < 3 * (2 * r + s)) :
    ArcAdj r s (wrap r s (a + w)) (wrap r s (b + w)) ↔ ArcAdj r s a b := by
  have := H.hw0; have := H.hw1
  simp only [ArcAdj, wrap]
  split_ifs <;> omega

/-! ## Unit steps in every chart -/

/-- A unit step in the tube up to a period. -/
def TU (r s : ℤ) (ρ ρ' : ℤ × ℤ) : Prop := ∃ t : ℤ, ρ' + t • per r s - ρ ∈ unitVec

/-- The relation "unit step" seen in chart `c`. -/
def CU (r s : ℤ) (c : ℕ) (ρ ρ' : ℤ × ℤ) : Prop := if c = 2 then TU r s ρ ρ' else ρ' - ρ ∈ unitVec

theorem cu_of_unit {c : ℕ} {ρ ρ' : ℤ × ℤ} (h : ρ' - ρ ∈ unitVec) : CU r s c ρ ρ' := by
  unfold CU; split_ifs
  · exact ⟨0, by simpa using h⟩
  · exact h

/-- A lower seam step seen in the tube. -/
theorem tu_seam (H : Hyp p r s w) {σ σ' : ℤ × ℤ} (h0 : σ.1 + σ.2 = 0) (h0' : σ'.1 + σ'.2 = 0)
    (hu : TU r s σ σ') : ArcAdj r s (σ.1 % (3 * (2 * r + s))) (σ'.1 % (3 * (2 * r + s))) := by
  obtain ⟨t, ht⟩ := hu
  rw [unit_sub] at ht
  simp only [per, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, U2] at ht
  have hε : (σ'.1 + t * (3 * (2 * r + s)) - σ.1 = 1) ∨ (σ'.1 + t * (3 * (2 * r + s)) - σ.1 = -1) := by
    rcases ht with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> first
      | (left; linarith) | (right; linarith) | (exfalso; linarith)
  rcases hε with e | e
  · exact arcAdj_of H (t := -t) (ε := 1) (Or.inl rfl) (by linarith)
  · exact arcAdj_of H (t := -t) (ε := -1) (Or.inr rfl) (by linarith)

theorem tu_seam_top (H : Hyp p r s w) {σ σ' : ℤ × ℤ} (h0 : σ.1 + σ.2 = 2 * p)
    (h0' : σ'.1 + σ'.2 = 2 * p) (hu : TU r s σ σ') :
    ArcAdj r s (σ.1 % (3 * (2 * r + s))) (σ'.1 % (3 * (2 * r + s))) := by
  obtain ⟨t, ht⟩ := hu
  rw [unit_sub] at ht
  simp only [per, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, U2] at ht
  have hε : (σ'.1 + t * (3 * (2 * r + s)) - σ.1 = 1) ∨ (σ'.1 + t * (3 * (2 * r + s)) - σ.1 = -1) := by
    rcases ht with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> first
      | (left; linarith) | (right; linarith) | (exfalso; linarith)
  rcases hε with e | e
  · exact arcAdj_of H (t := -t) (ε := 1) (Or.inl rfl) (by linarith)
  · exact arcAdj_of H (t := -t) (ε := -1) (Or.inr rfl) (by linarith)

theorem seam_tu (H : Hyp p r s w) {σ σ' : ℤ × ℤ} (h0 : σ.1 + σ.2 = σ'.1 + σ'.2)
    (ha : ArcAdj r s (σ.1 % (3 * (2 * r + s))) (σ'.1 % (3 * (2 * r + s)))) : TU r s σ σ' := by
  obtain ⟨t, ε, hε, e⟩ := arcAdj_lift H ha
  refine ⟨-t, ?_⟩
  rw [unit_sub]
  simp only [per, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, U2]
  rcases hε with rfl | rfl
  · right; right; right; right; right; constructor <;> linarith
  · right; right; left; constructor <;> linarith

theorem inC_L_T (H : Hyp p r s w) {v : MV} {ρ σ : ℤ × ℤ} (h1 : InC p r s w 0 v ρ)
    (h2 : InC p r s w 2 v σ) :
    ¬ IL r s ρ ∧ σ.1 + σ.2 = 0 ∧ σ.1 % (3 * (2 * r + s)) = aL r s ρ :=
  chLT (h1.2.2.trans h2.2.2.symm)

theorem inC_U_T (H : Hyp p r s w) {v : MV} {ρ σ : ℤ × ℤ} (h1 : InC p r s w 1 v ρ)
    (h2 : InC p r s w 2 v σ) :
    ¬ IU r s ρ ∧ σ.1 + σ.2 = 2 * p ∧ σ.1 % (3 * (2 * r + s)) = wrap r s (aU r s ρ + w) :=
  chUT (h1.2.2.trans h2.2.2.symm)

theorem not_L_U (H : Hyp p r s w) {v : MV} {ρ σ : ℤ × ℤ} (h1 : InC p r s w 0 v ρ)
    (h2 : InC p r s w 1 v σ) : False :=
  chL_ne_U H.hp (h1.2.2.trans h2.2.2.symm)

theorem tu_of_tu (H : Hyp p r s w) {ρ ρ' σ σ' : ℤ × ℤ} (hρ : ∃ t : ℤ, σ = ρ + t • per r s)
    (hρ' : ∃ t : ℤ, σ' = ρ' + t • per r s) (h : TU r s σ σ') : TU r s ρ ρ' := by
  obtain ⟨t, rfl⟩ := hρ
  obtain ⟨t', rfl⟩ := hρ'
  obtain ⟨t'', h⟩ := h
  refine ⟨t' + t'' - t, ?_⟩
  convert h using 1
  simp only [per, Prod.smul_mk, smul_eq_mul, Prod.ext_iff, Prod.fst_add, Prod.snd_add,
    Prod.fst_sub, Prod.snd_sub]
  constructor <;> ring

/-- **Unit steps are chart independent.** -/
theorem cd (H : Hyp p r s w) {c c' : ℕ} {v x : MV} {ρ ρ' σ σ' : ℤ × ℤ}
    (h1 : InC p r s w c v ρ) (h2 : InC p r s w c x ρ') (h3 : InC p r s w c' v σ)
    (h4 : InC p r s w c' x σ') (hu : CU r s c' σ σ') : CU r s c ρ ρ' := by
  have hc := h1.1
  have hc' := h3.1
  have hr := H.hr; have hs := H.hs
  rcases c_cases hc with rfl | rfl | rfl <;> rcases c_cases hc' with rfl | rfl | rfl
  · obtain rfl := (inC_inj01 H (by norm_num) h1 h3).1 rfl
    obtain rfl := (inC_inj01 H (by norm_num) h2 h4).1 rfl
    exact hu
  · exact (not_L_U H h1 h3).elim
  · simp only [CU, if_pos rfl] at hu
    obtain ⟨a, b, e⟩ := inC_L_T H h1 h3
    obtain ⟨a', b', e'⟩ := inC_L_T H h2 h4
    simp only [CU, if_neg (show (0 : ℕ) ≠ 2 by norm_num)]
    rw [unit_arcL hr hs h1.2.1 a h2.2.1 a', ← e, ← e']
    exact tu_seam H b b' hu
  · exact (not_L_U H h3 h1).elim
  · obtain rfl := (inC_inj01 H (by norm_num) h1 h3).1 rfl
    obtain rfl := (inC_inj01 H (by norm_num) h2 h4).1 rfl
    exact hu
  · simp only [CU, if_pos rfl] at hu
    obtain ⟨a, b, e⟩ := inC_U_T H h1 h3
    obtain ⟨a', b', e'⟩ := inC_U_T H h2 h4
    simp only [CU, if_neg (show (1 : ℕ) ≠ 2 by norm_num)]
    have l1 := aU_range hr hs h1.2.1 a
    have l2 := aU_range hr hs h2.2.1 a'
    rw [unit_arcU hr hs h1.2.1 a h2.2.1 a', ← arcAdj_wrap H l1.1 l1.2 l2.1 l2.2, ← e, ← e']
    exact tu_seam_top H b b' hu
  · simp only [CU, if_neg (show (0 : ℕ) ≠ 2 by norm_num)] at hu
    obtain ⟨a, b, e⟩ := inC_L_T H h3 h1
    obtain ⟨a', b', e'⟩ := inC_L_T H h4 h2
    simp only [CU, if_pos rfl]
    rw [unit_arcL hr hs h3.2.1 a h4.2.1 a', ← e, ← e'] at hu
    exact seam_tu H (by rw [b, b']) hu
  · simp only [CU, if_neg (show (1 : ℕ) ≠ 2 by norm_num)] at hu
    obtain ⟨a, b, e⟩ := inC_U_T H h3 h1
    obtain ⟨a', b', e'⟩ := inC_U_T H h4 h2
    simp only [CU, if_pos rfl]
    have l1 := aU_range hr hs h3.2.1 a
    have l2 := aU_range hr hs h4.2.1 a'
    rw [unit_arcU hr hs h3.2.1 a h4.2.1 a', ← arcAdj_wrap H l1.1 l1.2 l2.1 l2.2, ← e, ← e']
      at hu
    exact seam_tu H (by rw [b, b']) hu
  · simp only [CU, if_pos rfl] at hu ⊢
    exact tu_of_tu H (inC_rep2 H h1 h3) (inC_rep2 H h2 h4) hu

/-! ## Triangles -/

theorem unit_small {u : ℤ × ℤ} (h : u ∈ unitVec) : -1 ≤ u.1 ∧ u.1 ≤ 1 ∧ -1 ≤ u.2 ∧ u.2 ≤ 1 := by
  rw [unit_U2] at h; simp only [U2] at h; omega

/-- A tube step up to a period is a unit step after moving the second point. -/
theorem tu_move (H : Hyp p r s w) {x : MV} {ρ ρ' : ℤ × ℤ} (h : InC p r s w 2 x ρ')
    (hu : TU r s ρ ρ') : ∃ ρ'', InC p r s w 2 x ρ'' ∧ ρ'' - ρ ∈ unitVec := by
  obtain ⟨t, ht⟩ := hu
  exact ⟨ρ' + t • per r s, inC_shift h t, ht⟩

/-- Three points of the tube chart pairwise a unit apart up to periods: an honest triangle. -/
theorem tri_T (H : Hyp p r s w) {v x y : MV} {a b e : ℤ × ℤ} (ha : InC p r s w 2 v a)
    (hb : InC p r s w 2 x b) (he : InC p r s w 2 y e) (h1 : TU r s a b) (h2 : TU r s a e)
    (h3 : TU r s b e) : ∃ b' e', InC p r s w 2 x b' ∧ InC p r s w 2 y e' ∧ b' - a ∈ unitVec ∧
      e' - a ∈ unitVec ∧ e' - b' ∈ unitVec := by
  obtain ⟨b', hb', u1⟩ := tu_move H hb h1
  obtain ⟨e', he', u2⟩ := tu_move H he h2
  refine ⟨b', e', hb', he', u1, u2, ?_⟩
  have h3' := tu_of_tu H (inC_rep2 H hb' hb) (inC_rep2 H he' he) h3
  obtain ⟨t, ht⟩ := h3'
  have s1 := unit_small u1
  have s2 := unit_small u2
  have s3 := unit_small ht
  have : t = 0 := by
    apply per_small H.hr H.hs <;>
      simp only [per, Prod.fst_add, Prod.fst_sub, Prod.smul_mk, smul_eq_mul] at s1 s2 s3 <;>
      linarith
  subst this
  simpa using ht

/-- **Triangles lie in one chart.** -/
theorem tri (H : Hyp p r s w) {v x y : MV} (hvx : AdjM p r s w v x) (hvy : AdjM p r s w v y)
    (hxy : AdjM p r s w x y) : ∃ c a b e, InC p r s w c v a ∧ InC p r s w c x b ∧
      InC p r s w c y e ∧ b - a ∈ unitVec ∧ e - a ∈ unitVec ∧ e - b ∈ unitVec := by
  obtain ⟨c0, a, b, ha, hb, u0⟩ := adj_inC hvx
  obtain ⟨c1, a', e, ha', he, u1⟩ := adj_inC hvy
  obtain ⟨c2, b', e', hb', he', u2⟩ := adj_inC hxy
  -- a chart containing all three
  have key : ∃ c A B E, InC p r s w c v A ∧ InC p r s w c x B ∧ InC p r s w c y E := by
    by_cases h01 : c0 = c1
    · subst h01; exact ⟨c0, a, b, e, ha, hb, he⟩
    by_cases h02 : c0 = c2
    · subst h02; exact ⟨c0, a, b, e', ha, hb, he'⟩
    by_cases h12 : c1 = c2
    · subst h12; exact ⟨c1, a', b', e, ha', hb', he⟩
    exfalso
    have := ha.1; have := ha'.1; have := hb'.1
    rcases c_cases ha.1 with e0 | e0 | e0 <;> rcases c_cases ha'.1 with e1 | e1 | e1 <;>
      rcases c_cases hb'.1 with e2 | e2 | e2 <;> subst e0 e1 e2 <;> first
      | exact h01 rfl | exact h02 rfl | exact h12 rfl
      | exact not_L_U H ha ha' | exact not_L_U H ha' ha
      | exact not_L_U H hb hb' | exact not_L_U H hb' hb
      | exact not_L_U H he he' | exact not_L_U H he' he
  obtain ⟨c, A, B, E, hA, hB, hE⟩ := key
  have w1 := cd H hA hB ha hb (cu_of_unit u0)
  have w2 := cd H hA hE ha' he (cu_of_unit u1)
  have w3 := cd H hB hE hb' he' (cu_of_unit u2)
  by_cases hc2 : c = 2
  · subst hc2
    simp only [CU, ite_true] at w1 w2 w3
    obtain ⟨B', E', hB', hE', z1, z2, z3⟩ := tri_T H hA hB hE w1 w2 w3
    exact ⟨2, A, B', E', hA, hB', hE', z1, z2, z3⟩
  · simp only [CU, if_neg hc2] at w1 w2 w3
    exact ⟨c, A, B, E, hA, hB, hE, w1, w2, w3⟩

end Claude5E10
