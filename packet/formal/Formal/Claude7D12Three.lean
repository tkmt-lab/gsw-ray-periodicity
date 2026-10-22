import Formal.Claude7D12Chart
import Mathlib.Tactic.Ring

/-!
# D12 model: no edge has three common neighbours

Written by a Claude worker (2026-10-22, D12 bridge session), adapting `Claude5D12Three.lean`, adapting `Claude5O2Three.lean`.

* `InC c v ρ`  : the vertex `v` is the point `ρ` of chart `c`;
* `cd`         : unit steps are seen in every chart containing both ends (on the seam via the
                 arclength, `unit_arc0`, `unit_arc1`);
* `tri`        : three mutually adjacent vertices lie in one chart (there are two charts);
* `seam_apex`  : an edge in both charts has at most one apex inside each of them;
* `no_three`   : an edge has at most two common neighbours.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Claude7D12

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

/-- `v` is the point `ρ` of chart `c`. -/
def InC (r s : ℤ) (c : ℕ) (v : MV) (ρ : ℤ × ℤ) : Prop := c < 2 ∧ Dom r s c ρ ∧ ch r s c ρ = v

theorem adj_inC {v w : MV} (h : AdjM r s v w) :
    ∃ c ρ ρ', InC r s c v ρ ∧ InC r s c w ρ' ∧ ρ' - ρ ∈ unitVec := by
  obtain ⟨-, c, hc, z, u, h1, h2, hu, rfl, rfl⟩ := h
  exact ⟨c, z, z + u, ⟨hc, h1, rfl⟩, ⟨hc, h2, rfl⟩, by simpa using hu⟩

theorem inC_inj (hr : 1 ≤ r) (hs : 1 ≤ s) {c : ℕ} {v w : MV} {ρ ρ' : ℤ × ℤ}
    (h1 : InC r s c v ρ) (h2 : InC r s c w ρ') : v = w ↔ ρ = ρ' := by
  constructor
  · rintro rfl; exact ch_inj hr hs h1.1 h1.2.1 h2.2.1 (h1.2.2.trans h2.2.2.symm)
  · rintro rfl; exact h1.2.2.symm.trans h2.2.2

theorem inC_seam {v : MV} {ρ σ : ℤ × ℤ} (h1 : InC r s 0 v ρ) (h2 : InC r s 1 v σ) :
    ¬ I0 r s ρ ∧ ¬ I1 r s σ ∧ a0 r s ρ = a1 r s σ :=
  ch_eq01 (h1.2.2.trans h2.2.2.symm)

/-- **Unit steps are chart independent.** -/
theorem cd (hr : 1 ≤ r) (hs : 1 ≤ s) {c c' : ℕ} {v w : MV} {ρ ρ' σ σ' : ℤ × ℤ}
    (h1 : InC r s c v ρ) (h2 : InC r s c w ρ') (h3 : InC r s c' v σ) (h4 : InC r s c' w σ')
    (hu : σ' - σ ∈ unitVec) : ρ' - ρ ∈ unitVec := by
  have hc := h1.1
  have hc' := h3.1
  rcases c_cases hc with rfl | rfl <;> rcases c_cases hc' with rfl | rfl
  · obtain rfl := (inC_inj hr hs h1 h3).1 rfl
    obtain rfl := (inC_inj hr hs h2 h4).1 rfl
    exact hu
  · obtain ⟨a, b, e⟩ := inC_seam h1 h3
    obtain ⟨a', b', e'⟩ := inC_seam h2 h4
    rw [unit_arc0 hr hs h1.2.1 a h2.2.1 a', e, e']
    exact (unit_arc1 hr hs h3.2.1 b h4.2.1 b').1 hu
  · obtain ⟨a, b, e⟩ := inC_seam h3 h1
    obtain ⟨a', b', e'⟩ := inC_seam h4 h2
    rw [unit_arc1 hr hs h1.2.1 b h2.2.1 b', ← e, ← e']
    exact (unit_arc0 hr hs h3.2.1 a h4.2.1 a').1 hu
  · obtain rfl := (inC_inj hr hs h1 h3).1 rfl
    obtain rfl := (inC_inj hr hs h2 h4).1 rfl
    exact hu

/-- **Triangles lie in one chart.** -/
theorem tri {v w x : MV} (hvw : AdjM r s v w) (hvx : AdjM r s v x) (hwx : AdjM r s w x) :
    ∃ c ρv ρw ρx, InC r s c v ρv ∧ InC r s c w ρw ∧ InC r s c x ρx := by
  obtain ⟨c0, a, b, ha, hb, -⟩ := adj_inC hvw
  obtain ⟨c1, a', e, ha', he, -⟩ := adj_inC hvx
  obtain ⟨c2, b', e', hb', he', -⟩ := adj_inC hwx
  by_cases h01 : c0 = c1
  · subst h01; exact ⟨c0, a, b, e, ha, hb, he⟩
  by_cases h02 : c0 = c2
  · subst h02; exact ⟨c0, a, b, e', ha, hb, he'⟩
  have : c1 = c2 := by have := ha.1; have := ha'.1; have := hb'.1; omega
  subst this; exact ⟨c1, a', b', e, ha', hb', he⟩

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
theorem apex_P0 (hr : 1 ≤ r) (hs : 1 ≤ s) {l l' : ℤ} (h0 : 0 ≤ l) (h1 : l < 6 * r + 12 * s)
    (h0' : 0 ≤ l') (h1' : l' < 6 * r + 12 * s) (ha : ArcAdj r s l l')
    (hA : H0 r s (P0 r s l + rotL (P0 r s l' - P0 r s l)))
    (hB : H0 r s (P0 r s l + rotR (P0 r s l' - P0 r s l))) : False := by
  simp only [ArcAdj] at ha
  simp only [H0, rotL, rotR, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hA hB
  unfold P0 at hA hB
  split_ifs at hA hB <;> simp only at hA hB <;> omega

set_option maxHeartbeats 1000000 in
theorem apex_P1 (hr : 1 ≤ r) (hs : 1 ≤ s) {l l' : ℤ} (h0 : 0 ≤ l) (h1 : l < 6 * r + 12 * s)
    (h0' : 0 ≤ l') (h1' : l' < 6 * r + 12 * s) (ha : ArcAdj r s l l')
    (hA : H1 r s (P1 r s l + rotL (P1 r s l' - P1 r s l)))
    (hB : H1 r s (P1 r s l + rotR (P1 r s l' - P1 r s l))) : False := by
  simp only [ArcAdj] at ha
  simp only [H1, rotL, rotR, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at hA hB
  unfold P1 at hA hB
  split_ifs at hA hB <;> simp only at hA hB <;> omega

/-- **An edge on the seam has at most one apex in each chart.** -/
theorem seam_apex (hr : 1 ≤ r) (hs : 1 ≤ s) {c c' : ℕ} (hne : c ≠ c') {v w : MV}
    {ρ ρ' σ σ' : ℤ × ℤ} (hv : InC r s c v ρ) (hw : InC r s c w ρ') (hv' : InC r s c' v σ)
    (hw' : InC r s c' w σ') (hu : ρ' - ρ ∈ unitVec) (h1 : Dom r s c (ρ + rotL (ρ' - ρ)))
    (h2 : Dom r s c (ρ + rotR (ρ' - ρ))) : False := by
  have hc := hv.1
  have hc' := hv'.1
  rcases c_cases hc with rfl | rfl <;> rcases c_cases hc' with rfl | rfl
  · exact hne rfl
  · obtain ⟨a, -, -⟩ := inC_seam hv hv'
    obtain ⟨a', -, -⟩ := inC_seam hw hw'
    have l1 := a0_range hr hs hv.2.1 a
    have l2 := a0_range hr hs hw.2.1 a'
    have hA := (unit_arc0 hr hs hv.2.1 a hw.2.1 a').1 hu
    rw [eq_P0 hr hs hv.2.1 a, eq_P0 hr hs hw.2.1 a'] at h1 h2
    exact apex_P0 hr hs l1.1 l1.2 l2.1 l2.2 hA h1 h2
  · obtain ⟨-, a, -⟩ := inC_seam hv' hv
    obtain ⟨-, a', -⟩ := inC_seam hw' hw
    have l1 := a1_range hr hs hv.2.1 a
    have l2 := a1_range hr hs hw.2.1 a'
    have hA := (unit_arc1 hr hs hv.2.1 a hw.2.1 a').1 hu
    rw [eq_P1 hr hs hv.2.1 a, eq_P1 hr hs hw.2.1 a'] at h1 h2
    exact apex_P1 hr hs l1.1 l1.2 l2.1 l2.2 hA h1 h2
  · exact hne rfl

/-- A common neighbour of an edge, placed in a chart with the edge, at an apex. -/
theorem place (hr : 1 ≤ r) (hs : 1 ≤ s) {v w x : MV} (hvw : AdjM r s v w)
    (hvx : AdjM r s v x) (hwx : AdjM r s w x) : ∃ c a b p, InC r s c v a ∧ InC r s c w b ∧
      InC r s c x p ∧ b - a ∈ unitVec ∧ (p = a + rotL (b - a) ∨ p = a + rotR (b - a)) := by
  obtain ⟨c, a, b, p, ha, hb, hp⟩ := tri hvw hvx hwx
  obtain ⟨c0, a0, b0, ha0, hb0, hu0⟩ := adj_inC hvw
  obtain ⟨c1, a1, p1, ha1, hp1, hu1⟩ := adj_inC hvx
  obtain ⟨c2, b2, p2, hb2, hp2, hu2⟩ := adj_inC hwx
  have u0 := cd hr hs ha hb ha0 hb0 hu0
  have u1 := cd hr hs ha hp ha1 hp1 hu1
  have u2 := cd hr hs hb hp hb2 hp2 hu2
  exact ⟨c, a, b, p, ha, hb, hp, u0, apex2 u0 u1 u2⟩

theorem both_apex (hr : 1 ≤ r) (hs : 1 ≤ s) {c : ℕ} {x y : MV} {a b p q : ℤ × ℤ}
    (hx : InC r s c x p) (hy : InC r s c y q) (hp : p = a + rotL (b - a) ∨ p = a + rotR (b - a))
    (hq : q = a + rotL (b - a) ∨ q = a + rotR (b - a)) (hxy : x ≠ y) :
    Dom r s c (a + rotL (b - a)) ∧ Dom r s c (a + rotR (b - a)) := by
  have hne : p ≠ q := fun e => hxy ((inC_inj hr hs hx hy).2 e)
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact (hne rfl).elim
  · exact ⟨hx.2.1, hy.2.1⟩
  · exact ⟨hy.2.1, hx.2.1⟩
  · exact (hne rfl).elim

/-- **No edge has three common neighbours.** -/
theorem no_three (hr : 1 ≤ r) (hs : 1 ≤ s) {v w x y z : MV} (hvw : AdjM r s v w)
    (hvx : AdjM r s v x) (hwx : AdjM r s w x) (hvy : AdjM r s v y) (hwy : AdjM r s w y)
    (hvz : AdjM r s v z) (hwz : AdjM r s w z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    False := by
  obtain ⟨cx, a, b, px, ha, hb, hpx, hu, hx⟩ := place hr hs hvw hvx hwx
  obtain ⟨cy, a', b', py, ha', hb', hpy, -, hy⟩ := place hr hs hvw hvy hwy
  obtain ⟨cz, a'', b'', pz, ha'', hb'', hpz, -, hz⟩ := place hr hs hvw hvz hwz
  by_cases e1 : cy = cx
  · subst e1
    obtain rfl := (inC_inj hr hs ha ha').1 rfl
    obtain rfl := (inC_inj hr hs hb hb').1 rfl
    have hD := both_apex hr hs hpx hpy hx hy hxy
    by_cases e2 : cz = cy
    · subst e2
      obtain rfl := (inC_inj hr hs ha ha'').1 rfl
      obtain rfl := (inC_inj hr hs hb hb'').1 rfl
      have nxz : px ≠ pz := fun e => hxz ((inC_inj hr hs hpx hpz).2 e)
      have nyz : py ≠ pz := fun e => hyz ((inC_inj hr hs hpy hpz).2 e)
      have nxy : px ≠ py := fun e => hxy ((inC_inj hr hs hpx hpy).2 e)
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
        simp_all
    · exact seam_apex hr hs (Ne.symm e2) ha hb ha'' hb'' hu hD.1 hD.2
  · by_cases e2 : cz = cx
    · subst e2
      obtain rfl := (inC_inj hr hs ha ha'').1 rfl
      obtain rfl := (inC_inj hr hs hb hb'').1 rfl
      have hD := both_apex hr hs hpx hpz hx hz hxz
      exact seam_apex hr hs (Ne.symm e1) ha hb ha' hb' hu hD.1 hD.2
    · have : cz = cy := by have := ha.1; have := ha'.1; have := ha''.1; omega
      subst this
      obtain rfl := (inC_inj hr hs ha' ha'').1 rfl
      obtain rfl := (inC_inj hr hs hb' hb'').1 rfl
      have hu' := cd hr hs ha' hb' ha hb hu
      have hD := both_apex hr hs hpy hpz hy hz hyz
      exact seam_apex hr hs e1 ha' hb' ha hb hu' hD.1 hD.2

end Claude7D12
