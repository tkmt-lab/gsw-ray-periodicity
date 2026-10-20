import Formal.Claude5O2Chart
import Mathlib.Tactic.Ring

/-!
# O2 model: no edge has three common neighbours (`t, d ≥ 2`)

Written by a Claude worker (2026-10-20, O2 bridge session).

* `InC c v ρ`  : the vertex `v` is the point `ρ` of chart `c`;
* `cd`         : unit steps are seen in every chart containing both ends (`tr_unit` on seams);
* `tri`        : three mutually adjacent vertices lie in one chart;
* `seam_apex`  : an edge in two charts has at most one apex inside each of them;
* `three_charts` : no edge lies in three charts;
* `no_three`   : an edge has at most two common neighbours.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

variable {t d : ℤ}

/-- `v` is the point `ρ` of chart `c`. -/
def InC (t d : ℤ) (c : ℕ) (v : MV) (ρ : ℤ × ℤ) : Prop := c < 5 ∧ Dom t d c ρ ∧ ch t d c ρ = v

/-- Unit vectors by components. -/
def U2 (a b : ℤ) : Prop :=
  (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = -1 ∧ b = 1) ∨ (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = -1) ∨
    (a = 1 ∧ b = -1)

theorem unit_U2 {u : ℤ × ℤ} : u ∈ unitVec ↔ U2 u.1 u.2 := by
  obtain ⟨a, b⟩ := u
  simp [unit_iff, U2]

theorem unit_sub {ρ ρ' : ℤ × ℤ} : ρ' - ρ ∈ unitVec ↔ U2 (ρ'.1 - ρ.1) (ρ'.2 - ρ.2) := by
  rw [unit_U2]; rfl

theorem adj_inC {v w : MV} (h : AdjM t d v w) :
    ∃ c ρ ρ', InC t d c v ρ ∧ InC t d c w ρ' ∧ ρ' - ρ ∈ unitVec := by
  obtain ⟨-, c, hc, z, u, h1, h2, hu, rfl, rfl⟩ := h
  exact ⟨c, z, z + u, ⟨hc, h1, rfl⟩, ⟨hc, h2, rfl⟩, by simpa using hu⟩

theorem tr_self {c : ℕ} {z z' : ℤ × ℤ} : ¬ Tr t d c c z z' := by
  rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩ <;> simp [Tr]

theorem tr_both {c c' : ℕ} {z z' w w' : ℤ × ℤ} (h1 : Tr t d c c' z z') (h2 : Tr t d c' c w w') :
    False := by
  rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩ <;>
    rcases c_cases (c := c') with rfl | rfl | ⟨j, rfl⟩ <;> simp [Tr] at h1 h2

/-- The chart index of a seam relation. -/
theorem tr_lt {c c' : ℕ} (hc' : c' < 5) {z z' : ℤ × ℤ} (h : Tr t d c c' z z') :
    c < 2 ∧ c < c' := by
  rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩ <;>
    rcases c_cases (c := c') with rfl | rfl | ⟨j, rfl⟩ <;> simp [Tr] at h <;> omega

theorem sp_unit {j : ℕ} (hj : j < 3) {l l' : ℤ} :
    sp t d j l' - sp t d j l ∈ unitVec ↔ (l' = l + 1 ∨ l' = l - 1) := by
  rw [unit_sub]
  interval_cases j <;> simp only [sp, U2] <;> constructor <;> intro h <;> omega

theorem rp0_unit {l l' : ℤ} (h0 : 0 ≤ l) (h1 : l ≤ 2 * t) (h0' : 0 ≤ l') (h1' : l' ≤ 2 * t) :
    ((max (l' - t) 0, min l' t) : ℤ × ℤ) - (max (l - t) 0, min l t) ∈ unitVec ↔
      (l' = l + 1 ∨ l' = l - 1) := by
  rw [unit_sub]; simp only [U2]; constructor <;> intro h <;> omega

theorem rp1_unit {l l' : ℤ} (h0 : 0 ≤ l) (h1 : l ≤ 2 * t) (h0' : 0 ≤ l') (h1' : l' ≤ 2 * t) :
    ((min l' t, max (l' - t) 0) : ℤ × ℤ) - (min l t, max (l - t) 0) ∈ unitVec ↔
      (l' = l + 1 ∨ l' = l - 1) := by
  rw [unit_sub]; simp only [U2]; constructor <;> intro h <;> omega

theorem tr_unit (ht : 1 ≤ t) (hd : 1 ≤ d) {c c' : ℕ} (hc' : c' < 5) {ρ σ ρ' σ' : ℤ × ℤ}
    (h1 : Tr t d c c' ρ σ) (h2 : Tr t d c c' ρ' σ') :
    (ρ' - ρ ∈ unitVec ↔ σ' - σ ∈ unitVec) := by
  rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩ <;>
    rcases c_cases (c := c') with rfl | rfl | ⟨j, rfl⟩ <;> simp only [Tr] at h1 h2
  · obtain ⟨rfl, -⟩ := h1; obtain ⟨rfl, -⟩ := h2; rfl
  · obtain ⟨l, a0, a1, rfl, rfl⟩ := h1; obtain ⟨l', b0, b1, rfl, rfl⟩ := h2
    rw [sp_unit (by omega), rp0_unit a0 a1 b0 b1]
  · obtain ⟨l, a0, a1, rfl, rfl⟩ := h1; obtain ⟨l', b0, b1, rfl, rfl⟩ := h2
    rw [sp_unit (by omega), rp1_unit a0 a1 b0 b1]

/-- **Unit steps are chart independent.** -/
theorem cd (ht : 1 ≤ t) (hd : 1 ≤ d) {c c' : ℕ} {v w : MV} {ρ ρ' σ σ' : ℤ × ℤ}
    (h1 : InC t d c v ρ) (h2 : InC t d c w ρ') (h3 : InC t d c' v σ) (h4 : InC t d c' w σ')
    (hu : σ' - σ ∈ unitVec) : ρ' - ρ ∈ unitVec := by
  obtain ⟨hc, hρ, e1⟩ := h1
  obtain ⟨-, hρ', e2⟩ := h2
  obtain ⟨hc', hσ, e3⟩ := h3
  obtain ⟨-, hσ', e4⟩ := h4
  have ev := ch_eq ht hd hc hc' hρ hσ (e1.trans e3.symm)
  have ew := ch_eq ht hd hc hc' hρ' hσ' (e2.trans e4.symm)
  rcases ev with ⟨rfl, rfl⟩ | ev | ev <;> rcases ew with ⟨hcc, rfl⟩ | ew | ew
  · exact hu
  · exact (tr_self ew).elim
  · exact (tr_self ew).elim
  · exact (tr_self (hcc ▸ ev)).elim
  · exact (tr_unit ht hd hc' ev ew).2 hu
  · exact (tr_both ev ew).elim
  · exact (tr_self (hcc ▸ ev)).elim
  · exact (tr_both ew ev).elim
  · exact (tr_unit ht hd hc ev ew).1 hu

theorem inC_inj (ht : 1 ≤ t) {c : ℕ} {v w : MV} {ρ ρ' : ℤ × ℤ} (h1 : InC t d c v ρ)
    (h2 : InC t d c w ρ') : v = w ↔ ρ = ρ' := by
  constructor
  · rintro rfl; exact ch_inj ht h1.1 h1.2.1 h2.2.1 (h1.2.2.trans h2.2.2.symm)
  · rintro rfl; exact h1.2.2.symm.trans h2.2.2

theorem ex_tr (ht : 1 ≤ t) (hd : 1 ≤ d) {c c' : ℕ} {v : MV} {ρ σ : ℤ × ℤ} (h1 : InC t d c v ρ)
    (h2 : InC t d c' v σ) (hne : c ≠ c') : Tr t d c c' ρ σ ∨ Tr t d c' c σ ρ := by
  rcases ch_eq ht hd h1.1 h2.1 h1.2.1 h2.2.1 (h1.2.2.trans h2.2.2.symm) with ⟨h, -⟩ | h | h
  · exact (hne h).elim
  · exact Or.inl h
  · exact Or.inr h

theorem rr_eq (ht : 1 ≤ t) (hd : 1 ≤ d) {i j : ℕ} {v : MV} {ρ σ : ℤ × ℤ}
    (h1 : InC t d (i + 2) v ρ) (h2 : InC t d (j + 2) v σ) : i = j := by
  by_contra hne
  rcases ex_tr ht hd h1 h2 (by omega) with h | h <;> simp [Tr] at h

/-- The parameter of a sheet-0 and a sheet-1 point of side `j` that are rhombus neighbours. -/
theorem rp01_unit {l l' : ℤ} (h0 : 0 ≤ l) (h1 : l ≤ 2 * t) (h0' : 0 ≤ l') (h1' : l' ≤ 2 * t)
    (hu : ((min l' t, max (l' - t) 0) : ℤ × ℤ) - (max (l - t) 0, min l t) ∈ unitVec) :
    (l = 1 ∧ l' = 1) ∨ (l = 2 * t - 1 ∧ l' = 2 * t - 1) ∨ l = 0 ∨ l = 2 * t ∨ l' = 0 ∨
      l' = 2 * t := by
  rw [unit_sub] at hu; simp only [U2] at hu; omega

theorem near_corner (ht : 2 ≤ t) (hd : 1 ≤ d) {j : ℕ} (hj : j < 3) {p : ℤ × ℤ}
    (hp : Hx t d p) (hD : OnD t d p) {l : ℤ} (hl : l = 1 ∨ l = 2 * t - 1)
    (hu : sp t d j l - p ∈ unitVec) : p = sp t d j 0 ∨ p = sp t d j (2 * t) := by
  rw [unit_sub] at hu
  obtain ⟨p1, p2⟩ := p
  simp only [Hx, OnD] at hp hD
  interval_cases j <;> simp only [sp, U2, Prod.mk.injEq] at hu ⊢ <;> omega

/-- The core of `tri`: `P` on a `d`-side, `Q` on side `j` (sheet 0), `R` on side `j` (sheet 1). -/
theorem tri_core (ht : 2 ≤ t) (hd : 2 ≤ d) {j : ℕ} (hj : j < 3) {P Q R : MV}
    {p p1 q qr r1 rr : ℤ × ℤ} (hP0 : InC t d 0 P p) (hP1 : InC t d 1 P p1)
    (hQ0 : InC t d 0 Q q) (hQR : InC t d (j + 2) Q qr) (hR1 : InC t d 1 R r1)
    (hRR : InC t d (j + 2) R rr) (hPQ : q - p ∈ unitVec) (hPR : r1 - p1 ∈ unitVec)
    (hQRu : rr - qr ∈ unitVec) :
    ∃ c ρP ρQ ρR, InC t d c P ρP ∧ InC t d c Q ρQ ∧ InC t d c R ρR := by
  have t1 := ex_tr (by omega) (by omega) hP0 hP1 (by norm_num)
  have t2 := ex_tr (by omega) (by omega) hQ0 hQR (by omega)
  have t3 := ex_tr (by omega) (by omega) hR1 hRR (by omega)
  simp only [Tr, or_false, false_or] at t1 t2 t3
  obtain ⟨rfl, hD⟩ := t1
  obtain ⟨l, a0, a1, rfl, rfl⟩ := t2
  obtain ⟨l', b0, b1, rfl, rfl⟩ := t3
  rcases rp01_unit a0 a1 b0 b1 hQRu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h | h | h | h
  · -- `P` is the corner `A_j`
    rcases near_corner ht (by omega) hj hP0.2.1 hD (Or.inl rfl) hPQ with rfl | rfl
    · refine ⟨j + 2, (0, 0), _, _, ⟨by omega, by simp [Dom, Rh]; omega, ?_⟩, hQR, hRR⟩
      rw [chR_AB (z := (0, 0)) (by omega) j rfl]; exact hP0.2.2
    · refine ⟨j + 2, (t, t), _, _, ⟨by omega, by simp [Dom, Rh]; omega, ?_⟩, hQR, hRR⟩
      rw [chR_BC (z := (t, t)) (by omega) j rfl (by simp; omega)]
      rw [show t + (t, t).1 = 2 * t by simp; ring]; exact hP0.2.2
  · rcases near_corner ht (by omega) hj hP0.2.1 hD (Or.inr rfl) hPQ with rfl | rfl
    · refine ⟨j + 2, (0, 0), _, _, ⟨by omega, by simp [Dom, Rh]; omega, ?_⟩, hQR, hRR⟩
      rw [chR_AB (z := (0, 0)) (by omega) j rfl]; exact hP0.2.2
    · refine ⟨j + 2, (t, t), _, _, ⟨by omega, by simp [Dom, Rh]; omega, ?_⟩, hQR, hRR⟩
      rw [chR_BC (z := (t, t)) (by omega) j rfl (by simp; omega)]
      rw [show t + (t, t).1 = 2 * t by simp; ring]; exact hP0.2.2
  all_goals first
    | (-- `Q` is a corner: it lies in chart 1
      have hQD : OnD t d (sp t d j l) := (sp_onD (by omega) (by omega) hj a0 a1).2 (by omega)
      exact ⟨1, _, sp t d j l, _, hP1, ⟨by norm_num, hQ0.2.1, by rw [ch1_onD hQD]; exact hQ0.2.2⟩,
        hR1⟩)
    | (-- `R` is a corner: it lies in chart 0
      have hRD : OnD t d (sp t d j l') := (sp_onD (by omega) (by omega) hj b0 b1).2 (by omega)
      exact ⟨0, _, _, sp t d j l', hP0, hQ0, ⟨by norm_num, hR1.2.1, by rw [ch0, ← ch1_onD hRD]; exact hR1.2.2⟩⟩)

theorem neg_unit {a b : ℤ × ℤ} (h : b - a ∈ unitVec) : a - b ∈ unitVec := by
  simpa using unit_neg h

/-- **Triangles lie in one chart.** -/
theorem tri (ht : 2 ≤ t) (hd : 2 ≤ d) {v w x : MV} (hvw : AdjM t d v w) (hvx : AdjM t d v x)
    (hwx : AdjM t d w x) : ∃ c ρv ρw ρx, InC t d c v ρv ∧ InC t d c w ρw ∧ InC t d c x ρx := by
  obtain ⟨c0, a, b, ha, hb, hu0⟩ := adj_inC hvw
  obtain ⟨c1, a', e, ha', he, hu1⟩ := adj_inC hvx
  obtain ⟨c2, b', e', hb', he', hu2⟩ := adj_inC hwx
  by_cases h01 : c0 = c1
  · subst h01; exact ⟨c0, a, b, e, ha, hb, he⟩
  by_cases h02 : c0 = c2
  · subst h02; exact ⟨c0, a, b, e', ha, hb, he'⟩
  by_cases h12 : c1 = c2
  · subst h12; exact ⟨c1, a', b', e, ha', hb', he⟩
  have ht1 : (1 : ℤ) ≤ t := by omega
  have hd1 : (1 : ℤ) ≤ d := by omega
  have l0 := ha.1; have l1 := ha'.1; have l2 := hb'.1
  rcases c_cases (c := c0) with rfl | rfl | ⟨i, rfl⟩ <;>
    rcases c_cases (c := c1) with rfl | rfl | ⟨j, rfl⟩ <;>
    rcases c_cases (c := c2) with rfl | rfl | ⟨k, rfl⟩ <;>
    first
    | (exfalso; omega)
    | (exfalso; have := rr_eq ht1 hd1 ha ha'; omega)
    | (exfalso; have := rr_eq ht1 hd1 hb hb'; omega)
    | (exfalso; have := rr_eq ht1 hd1 he he'; omega)
    | skip
  · -- (0, 1, R)
    exact tri_core ht hd (by omega) ha ha' hb hb' he he' hu0 hu1 hu2
  · -- (0, R, 1)
    obtain ⟨c, p, q, r, h1, h2, h3⟩ :=
      tri_core ht hd (by omega) hb hb' ha ha' he' he (neg_unit hu0) hu2 hu1
    exact ⟨c, q, p, r, h2, h1, h3⟩
  · -- (1, 0, R)
    obtain ⟨c, p, q, r, h1, h2, h3⟩ :=
      tri_core ht hd (by omega) ha' ha he he' hb hb' hu1 hu0 (neg_unit hu2)
    exact ⟨c, p, r, q, h1, h3, h2⟩
  · -- (1, R, 0)
    obtain ⟨c, p, q, r, h1, h2, h3⟩ :=
      tri_core ht hd (by omega) hb' hb he' he ha ha' hu2 (neg_unit hu0) (neg_unit hu1)
    exact ⟨c, r, p, q, h3, h1, h2⟩
  · -- (R, 0, 1)
    obtain ⟨c, p, q, r, h1, h2, h3⟩ :=
      tri_core ht hd (by omega) he he' ha' ha hb' hb (neg_unit hu1) (neg_unit hu2) hu0
    exact ⟨c, q, r, p, h2, h3, h1⟩
  · -- (R, 1, 0)
    obtain ⟨c, p, q, r, h1, h2, h3⟩ :=
      tri_core ht hd (by omega) he' he hb' hb ha' ha (neg_unit hu2) (neg_unit hu1) (neg_unit hu0)
    exact ⟨c, r, q, p, h3, h2, h1⟩

/-- Left and right apex directions of a unit step. -/
def rotL (u : ℤ × ℤ) : ℤ × ℤ := (-u.2, u.1 + u.2)
def rotR (u : ℤ × ℤ) : ℤ × ℤ := (u.1 + u.2, -u.1)

theorem apex2 {ρ ρ' ξ : ℤ × ℤ} (h1 : ρ' - ρ ∈ unitVec) (h2 : ξ - ρ ∈ unitVec)
    (h3 : ξ - ρ' ∈ unitVec) : ξ = ρ + rotL (ρ' - ρ) ∨ ξ = ρ + rotR (ρ' - ρ) := by
  rw [unit_sub] at h1 h2 h3
  simp only [U2] at h1 h2 h3
  simp only [rotL, rotR, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  omega

theorem seam_D {ρ ρ' : ℤ × ℤ} (ht : 2 ≤ t) (hd : 2 ≤ d) (h0 : Hx t d ρ) (h0' : Hx t d ρ')
    (hD : OnD t d ρ) (hD' : OnD t d ρ') (hu : ρ' - ρ ∈ unitVec)
    (h1 : Hx t d (ρ + rotL (ρ' - ρ))) (h2 : Hx t d (ρ + rotR (ρ' - ρ))) : False := by
  obtain ⟨a, b⟩ := ρ
  obtain ⟨a', b'⟩ := ρ'
  rw [unit_sub] at hu
  simp only [Hx, OnD, U2, rotL, rotR, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
    Prod.snd_sub] at *
  omega

theorem seam_S {j : ℕ} (hj : j < 3) {l l' : ℤ} (ht : 2 ≤ t) (hd : 2 ≤ d)
    (hl : l' = l + 1 ∨ l' = l - 1)
    (h1 : Hx t d (sp t d j l + rotL (sp t d j l' - sp t d j l)))
    (h2 : Hx t d (sp t d j l + rotR (sp t d j l' - sp t d j l))) : False := by
  interval_cases j <;>
    simp only [Hx, sp, rotL, rotR, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub] at h1 h2 <;> omega

theorem seam_R0 {l l' : ℤ} (ht : 2 ≤ t) (h0 : 0 ≤ l) (h1 : l ≤ 2 * t) (hl : l' = l + 1 ∨ l' = l - 1)
    (hA : Rh t (((max (l - t) 0, min l t) : ℤ × ℤ) +
      rotL ((max (l' - t) 0, min l' t) - (max (l - t) 0, min l t))))
    (hB : Rh t (((max (l - t) 0, min l t) : ℤ × ℤ) +
      rotR ((max (l' - t) 0, min l' t) - (max (l - t) 0, min l t)))) : False := by
  simp only [Rh, rotL, rotR, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hA hB
  omega

theorem seam_R1 {l l' : ℤ} (ht : 2 ≤ t) (h0 : 0 ≤ l) (h1 : l ≤ 2 * t) (hl : l' = l + 1 ∨ l' = l - 1)
    (hA : Rh t (((min l t, max (l - t) 0) : ℤ × ℤ) +
      rotL ((min l' t, max (l' - t) 0) - (min l t, max (l - t) 0))))
    (hB : Rh t (((min l t, max (l - t) 0) : ℤ × ℤ) +
      rotR ((min l' t, max (l' - t) 0) - (min l t, max (l - t) 0)))) : False := by
  simp only [Rh, rotL, rotR, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hA hB
  omega

/-- **An edge on a seam has at most one apex in each chart.** -/
theorem seam_apex (ht : 2 ≤ t) (hd : 2 ≤ d) {c c' : ℕ} (hne : c ≠ c') {v w : MV}
    {ρ ρ' σ σ' : ℤ × ℤ} (hv : InC t d c v ρ) (hw : InC t d c w ρ') (hv' : InC t d c' v σ)
    (hw' : InC t d c' w σ') (hu : ρ' - ρ ∈ unitVec) (h1 : Dom t d c (ρ + rotL (ρ' - ρ)))
    (h2 : Dom t d c (ρ + rotR (ρ' - ρ))) : False := by
  have ht1 : (1 : ℤ) ≤ t := by omega
  have hd1 : (1 : ℤ) ≤ d := by omega
  have hc := hv.1; have hc' := hv'.1
  have h0 := hv.2.1; have h0' := hw.2.1
  rcases ex_tr ht1 hd1 hv hv' hne with tv | tv <;> rcases ex_tr ht1 hd1 hw hw' hne with tw | tw
  · rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩ <;>
      rcases c_cases (c := c') with rfl | rfl | ⟨j, rfl⟩ <;> simp only [Tr] at tv tw
    · exact seam_D ht hd h0 h0' tv.2 tw.2 hu h1 h2
    · obtain ⟨l, a0, a1, rfl, rfl⟩ := tv; obtain ⟨l', b0, b1, rfl, rfl⟩ := tw
      exact seam_S (by omega) ht hd ((sp_unit (by omega)).1 hu) h1 h2
    · obtain ⟨l, a0, a1, rfl, rfl⟩ := tv; obtain ⟨l', b0, b1, rfl, rfl⟩ := tw
      exact seam_S (by omega) ht hd ((sp_unit (by omega)).1 hu) h1 h2
  · exact tr_both tv tw
  · exact tr_both tw tv
  · rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩ <;>
      rcases c_cases (c := c') with rfl | rfl | ⟨j, rfl⟩ <;> simp only [Tr] at tv tw
    · obtain ⟨rfl, hD⟩ := tv; obtain ⟨rfl, hD'⟩ := tw
      exact seam_D ht hd h0 h0' hD hD' hu h1 h2
    · obtain ⟨l, a0, a1, rfl, rfl⟩ := tv; obtain ⟨l', b0, b1, rfl, rfl⟩ := tw
      exact seam_R0 ht a0 a1 ((rp0_unit a0 a1 b0 b1).1 hu) h1 h2
    · obtain ⟨l, a0, a1, rfl, rfl⟩ := tv; obtain ⟨l', b0, b1, rfl, rfl⟩ := tw
      exact seam_R1 ht a0 a1 ((rp1_unit a0 a1 b0 b1).1 hu) h1 h2

theorem three_core (ht : 2 ≤ t) (hd : 2 ≤ d) {j : ℕ} (hj : j < 3) {v w : MV}
    {p0 p1 pr q0 q1 qr : ℤ × ℤ} (hv0 : InC t d 0 v p0) (hv1 : InC t d 1 v p1)
    (hvR : InC t d (j + 2) v pr) (hw0 : InC t d 0 w q0) (hw1 : InC t d 1 w q1)
    (hwR : InC t d (j + 2) w qr) (hu : q0 - p0 ∈ unitVec) : False := by
  have ht1 : (1 : ℤ) ≤ t := by omega
  have hd1 : (1 : ℤ) ≤ d := by omega
  have a1 := ex_tr ht1 hd1 hv0 hv1 (by norm_num)
  have a2 := ex_tr ht1 hd1 hv0 hvR (by omega)
  have b1 := ex_tr ht1 hd1 hw0 hw1 (by norm_num)
  have b2 := ex_tr ht1 hd1 hw0 hwR (by omega)
  simp only [Tr, or_false, false_or] at a1 a2 b1 b2
  obtain ⟨l, x0, x1, rfl, -⟩ := a2
  obtain ⟨l', y0, y1, rfl, -⟩ := b2
  have e1 := (sp_onD ht1 hd1 hj x0 x1).1 a1.2
  have e2 := (sp_onD ht1 hd1 hj y0 y1).1 b1.2
  have e3 := (sp_unit hj).1 hu
  omega

/-- **No edge lies in three charts.** -/
theorem three_charts (ht : 2 ≤ t) (hd : 2 ≤ d) {c1 c2 c3 : ℕ} (h12 : c1 ≠ c2) (h13 : c1 ≠ c3)
    (h23 : c2 ≠ c3) {v w : MV} {ρ1 ρ2 ρ3 σ1 σ2 σ3 : ℤ × ℤ} (hv1 : InC t d c1 v ρ1)
    (hv2 : InC t d c2 v ρ2) (hv3 : InC t d c3 v ρ3) (hw1 : InC t d c1 w σ1)
    (hw2 : InC t d c2 w σ2) (hw3 : InC t d c3 w σ3) (hu : σ1 - ρ1 ∈ unitVec) : False := by
  have ht1 : (1 : ℤ) ≤ t := by omega
  have hd1 : (1 : ℤ) ≤ d := by omega
  have hu2 := cd ht1 hd1 hv2 hw2 hv1 hw1 hu
  have hu3 := cd ht1 hd1 hv3 hw3 hv1 hw1 hu
  have l1 := hv1.1; have l2 := hv2.1; have l3 := hv3.1
  rcases c_cases (c := c1) with rfl | rfl | ⟨i, rfl⟩ <;>
    rcases c_cases (c := c2) with rfl | rfl | ⟨j, rfl⟩ <;>
    rcases c_cases (c := c3) with rfl | rfl | ⟨k, rfl⟩ <;>
    first
    | (exfalso; omega)
    | (exfalso; have := rr_eq ht1 hd1 hv1 hv2; omega)
    | (exfalso; have := rr_eq ht1 hd1 hv1 hv3; omega)
    | (exfalso; have := rr_eq ht1 hd1 hv2 hv3; omega)
    | skip
  · exact three_core ht hd (by omega) hv1 hv2 hv3 hw1 hw2 hw3 hu
  · exact three_core ht hd (by omega) hv1 hv3 hv2 hw1 hw3 hw2 hu
  · exact three_core ht hd (by omega) hv2 hv1 hv3 hw2 hw1 hw3 hu2
  · exact three_core ht hd (by omega) hv3 hv1 hv2 hw3 hw1 hw2 hu3
  · exact three_core ht hd (by omega) hv2 hv3 hv1 hw2 hw3 hw1 hu2
  · exact three_core ht hd (by omega) hv3 hv2 hv1 hw3 hw2 hw1 hu3

/-- A common neighbour of an edge, placed in a chart with the edge, at an apex. -/
theorem place (ht : 2 ≤ t) (hd : 2 ≤ d) {v w x : MV} (hvw : AdjM t d v w) (hvx : AdjM t d v x)
    (hwx : AdjM t d w x) : ∃ c a b p, InC t d c v a ∧ InC t d c w b ∧ InC t d c x p ∧
      b - a ∈ unitVec ∧ (p = a + rotL (b - a) ∨ p = a + rotR (b - a)) := by
  have ht1 : (1 : ℤ) ≤ t := by omega
  have hd1 : (1 : ℤ) ≤ d := by omega
  obtain ⟨c, a, b, p, ha, hb, hp⟩ := tri ht hd hvw hvx hwx
  obtain ⟨c0, a0, b0, ha0, hb0, hu0⟩ := adj_inC hvw
  obtain ⟨c1, a1, p1, ha1, hp1, hu1⟩ := adj_inC hvx
  obtain ⟨c2, b2, p2, hb2, hp2, hu2⟩ := adj_inC hwx
  have u0 := cd ht1 hd1 ha hb ha0 hb0 hu0
  have u1 := cd ht1 hd1 ha hp ha1 hp1 hu1
  have u2 := cd ht1 hd1 hb hp hb2 hp2 hu2
  exact ⟨c, a, b, p, ha, hb, hp, u0, apex2 u0 u1 u2⟩

theorem both_apex (ht : 1 ≤ t) {c : ℕ} {x y : MV} {a b p q : ℤ × ℤ} (hx : InC t d c x p)
    (hy : InC t d c y q) (hp : p = a + rotL (b - a) ∨ p = a + rotR (b - a))
    (hq : q = a + rotL (b - a) ∨ q = a + rotR (b - a)) (hxy : x ≠ y) :
    Dom t d c (a + rotL (b - a)) ∧ Dom t d c (a + rotR (b - a)) := by
  have hne : p ≠ q := fun e => hxy ((inC_inj ht hx hy).2 e)
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact (hne rfl).elim
  · exact ⟨hx.2.1, hy.2.1⟩
  · exact ⟨hy.2.1, hx.2.1⟩
  · exact (hne rfl).elim

/-- **No edge has three common neighbours** (`t, d ≥ 2`). -/
theorem no_three (ht : 2 ≤ t) (hd : 2 ≤ d) {v w x y z : MV} (hvw : AdjM t d v w)
    (hvx : AdjM t d v x) (hwx : AdjM t d w x) (hvy : AdjM t d v y) (hwy : AdjM t d w y)
    (hvz : AdjM t d v z) (hwz : AdjM t d w z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    False := by
  have ht1 : (1 : ℤ) ≤ t := by omega
  obtain ⟨cx, a, b, px, ha, hb, hpx, hu, hx⟩ := place ht hd hvw hvx hwx
  obtain ⟨cy, a', b', py, ha', hb', hpy, -, hy⟩ := place ht hd hvw hvy hwy
  obtain ⟨cz, a'', b'', pz, ha'', hb'', hpz, -, hz⟩ := place ht hd hvw hvz hwz
  by_cases e1 : cy = cx
  · subst e1
    obtain rfl := (inC_inj ht1 ha ha').1 rfl
    obtain rfl := (inC_inj ht1 hb hb').1 rfl
    have hD := both_apex ht1 hpx hpy hx hy hxy
    by_cases e2 : cz = cy
    · subst e2
      obtain rfl := (inC_inj ht1 ha ha'').1 rfl
      obtain rfl := (inC_inj ht1 hb hb'').1 rfl
      have h1 := both_apex ht1 hpx hpz hx hz hxz
      have h2 := both_apex ht1 hpy hpz hy hz hyz
      have nxz : px ≠ pz := fun e => hxz ((inC_inj ht1 hpx hpz).2 e)
      have nyz : py ≠ pz := fun e => hyz ((inC_inj ht1 hpy hpz).2 e)
      have nxy : px ≠ py := fun e => hxy ((inC_inj ht1 hpx hpy).2 e)
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
        simp_all
    · exact seam_apex ht hd (Ne.symm e2) ha hb ha'' hb'' hu hD.1 hD.2
  · by_cases e2 : cz = cx
    · subst e2
      obtain rfl := (inC_inj ht1 ha ha'').1 rfl
      obtain rfl := (inC_inj ht1 hb hb'').1 rfl
      have hD := both_apex ht1 hpx hpz hx hz hxz
      exact seam_apex ht hd (Ne.symm e1) ha hb ha' hb' hu hD.1 hD.2
    · by_cases e3 : cz = cy
      · subst e3
        obtain rfl := (inC_inj ht1 ha' ha'').1 rfl
        obtain rfl := (inC_inj ht1 hb' hb'').1 rfl
        have hu' := cd ht1 (by omega) ha' hb' ha hb hu
        have hD := both_apex ht1 hpy hpz hy hz hyz
        exact seam_apex ht hd e1 ha' hb' ha hb hu' hD.1 hD.2
      · exact three_charts ht hd (Ne.symm e1) (Ne.symm e2) (Ne.symm e3) ha ha' ha'' hb hb' hb'' hu

end Claude5O2
