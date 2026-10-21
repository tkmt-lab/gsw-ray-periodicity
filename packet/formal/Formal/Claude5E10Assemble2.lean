import Formal.Claude5E10Assemble
import Mathlib.Tactic.LinearCombination

/-!
# E10 model: iterated rotations, and the transitions of the assembled invariant

Written by a Claude worker (2026-10-20, E10 bridge session).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w k : ℤ}

/-- Iterated rotations. -/
def Zi (r s : ℤ) (c t : ℕ) (z : ℤ × ℤ) : ℤ × ℤ := (ρz r s c)^[t] z
def Ri (t : ℕ) (d : ℤ × ℤ) : ℤ × ℤ := (rotN 2)^[t] d

theorem Zi_succ (c t : ℕ) (z : ℤ × ℤ) : Zi r s c (t + 1) z = Zi r s c t (ρz r s c z) := by
  simp only [Zi, Function.iterate_succ_apply]

theorem Ri_succ (t : ℕ) (d : ℤ × ℤ) : Ri (t + 1) d = Ri t (rotN 2 d) := by
  simp only [Ri, Function.iterate_succ_apply]

theorem Zi_sub (c t : ℕ) (z z' : ℤ × ℤ) : Zi r s c t z - Zi r s c t z' = Ri t (z - z') := by
  induction t generalizing z z' with
  | zero => rfl
  | succ t ih => rw [Zi_succ, Zi_succ, ih, ρz_sub, Ri_succ]

theorem Zi_add (c t : ℕ) (z d : ℤ × ℤ) : Zi r s c t (z + d) = Zi r s c t z + Ri t d := by
  have := Zi_sub (r := r) (s := s) c t (z + d) z
  rw [add_sub_cancel_left] at this
  rw [← this]; abel

theorem cross_Ri (t : ℕ) (a b : ℤ × ℤ) : cross (Ri t a) (Ri t b) = cross a b := by
  induction t generalizing a b with
  | zero => rfl
  | succ t ih => rw [Ri_succ, Ri_succ, ih, cross_rotN]

theorem unit_Ri (t : ℕ) {u : ℤ × ℤ} (h : u ∈ unitVec) : Ri t u ∈ unitVec := by
  induction t generalizing u with
  | zero => exact h
  | succ t ih => rw [Ri_succ]; exact ih (rotN_unit' 2 h)

theorem state_iter (c t : ℕ) (d z : ℤ × ℤ) :
    (ρS r s c)^[t] (d, cross d z) = (Ri t d, cross (Ri t d) (Zi r s c t z)) := by
  induction t generalizing d z with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply, ρS_state, ih, Ri_succ, Zi_succ]

theorem iter_fst (c t : ℕ) (d : ℤ × ℤ) (E : ℤ) : ((ρS r s c)^[t] (d, E)).1 = Ri t d := by
  induction t generalizing d E with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply, Ri_succ]; exact ih _ _

theorem capDom_Zi {c : ℕ} (hc : c < 2) (t : ℕ) (z : ℤ × ℤ) :
    CapDom r s c (Zi r s c t z) ↔ CapDom r s c z := by
  induction t generalizing z with
  | zero => rfl
  | succ t ih => rw [Zi_succ, ih, capDom_ρ hc]

theorem side_Zi {c j : ℕ} (hc : c < 2) (hj : j < 6) (t : ℕ) (z : ℤ × ℤ) :
    (OnSide r s c ((j + 2 * t) % 6) (Zi r s c t z) ↔ OnSide r s c j z) ∧
      (Out r s c ((j + 2 * t) % 6) (Zi r s c t z) ↔ Out r s c j z) ∧
      (Inn1 r s c ((j + 2 * t) % 6) (Zi r s c t z) ↔ Inn1 r s c j z) := by
  induction t generalizing z j with
  | zero => simp [Zi, Nat.mod_eq_of_lt hj]
  | succ t ih =>
    rw [Zi_succ]
    have e : (j + 2 * (t + 1)) % 6 = ((j + 2) % 6 + 2 * t) % 6 := by omega
    rw [e]
    obtain ⟨a, b, c'⟩ := ih (j := (j + 2) % 6) (by omega) (ρz r s c z)
    exact ⟨a.trans (onSide_ρ hc hj z), b.trans (out_ρ hc hj z), c'.trans (inn1_ρ hc hj z)⟩

theorem corner_Zi {c : ℕ} (hc : c < 2) (t : ℕ) (z : ℤ × ℤ) :
    CornerPos p r s w c (Zi r s c t z) ↔ CornerPos p r s w c z := by
  induction t generalizing z with
  | zero => rfl
  | succ t ih => rw [Zi_succ, ih, corner_ρ hc]

theorem Zi3 (c : ℕ) (z : ℤ × ℤ) : Zi r s c 3 z = z := by
  simp only [Zi, Function.iterate_succ_apply, Function.iterate_zero_apply]; exact ρz3 c z

theorem Zi_comp (c t t' : ℕ) (z : ℤ × ℤ) : Zi r s c t (Zi r s c t' z) = Zi r s c (t + t') z := by
  simp only [Zi, ← Function.iterate_add_apply]

theorem ρS_iter_mod' (c t : ℕ) (x : (ℤ × ℤ) × ℤ) :
    (ρS r s c)^[t] x = (ρS r s c)^[t % 3] x := by
  conv_lhs => rw [← Nat.mod_add_div t 3]
  rw [Function.iterate_add_apply]
  congr 1
  induction t / 3 with
  | zero => rfl
  | succ q ih =>
    rw [show 3 * (q + 1) = 3 + 3 * q by ring, Function.iterate_add_apply, ih]
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
    exact ρS3 c x

theorem gmap_Zi {c j : ℕ} (hc : c < 2) (hj : j < 6) (t : ℕ) (z : ℤ × ℤ) :
    ∃ l : ℤ, gmap p r s w c ((j + 2 * t) % 6) (Zi r s c t z) =
      gmap p r s w c j z + (l * (2 * r + s), -(l * (2 * r + s))) := by
  induction t generalizing j z with
  | zero => exact ⟨0, by simp [Zi, Nat.mod_eq_of_lt hj]⟩
  | succ t ih =>
    obtain ⟨l, hl⟩ := ih (j := (j + 2) % 6) (by omega) (ρz r s c z)
    refine ⟨l + lam c j, ?_⟩
    rw [Zi_succ, show (j + 2 * (t + 1)) % 6 = ((j + 2) % 6 + 2 * t) % 6 by omega, hl,
      gmap_ρ hc hj]
    ext <;> simp <;> ring

theorem gk_Ri {c j : ℕ} (hc : c < 2) (hj : j < 6) (t : ℕ) (d : ℤ × ℤ) :
    rotN (gk c ((j + 2 * t) % 6)) (Ri t d) = rotN (gk c j) d := by
  induction t generalizing j d with
  | zero => simp [Ri, Nat.mod_eq_of_lt hj]
  | succ t ih =>
    rw [Ri_succ, show (j + 2 * (t + 1)) % 6 = ((j + 2) % 6 + 2 * t) % 6 by omega,
      ih (by omega), gk_ρ hc hj]

theorem cap_iter {T : Tabs} {c t : ℕ} {x : (ℤ × ℤ) × ℤ} {ε : ℤ}
    (h : T.cap r s c ((ρS r s c)^[t] x).1 ((ρS r s c)^[t] x).2 ε) : T.cap r s c x.1 x.2 ε := by
  obtain ⟨t1, -, hk⟩ := h
  refine ⟨(t1 + t) % 3, Nat.mod_lt _ (by norm_num), ?_⟩
  have e : (ρS r s c)^[t1] ((ρS r s c)^[t] x) = (ρS r s c)^[t1 + t] x := by
    rw [Function.iterate_add_apply]
  have hx : ((ρS r s c)^[t] x).1 = ((ρS r s c)^[t] x).1 := rfl
  rw [show (((ρS r s c)^[t] x).1, ((ρS r s c)^[t] x).2) = (ρS r s c)^[t] x from rfl, e] at hk
  have hm := ρS_iter_mod' (r := r) (s := s) c (t1 + t) x
  rw [hm] at hk
  exact hk

/-! ## The cap → tube transition for all rotations -/

theorem capT_full {T : Tabs} (R : RedOK p r s w k T) {c : ℕ} (hc : c < 2) :
    ∀ t : ℕ, ∀ j, j < 6 → ∀ d E ε zE zO,
      T.red c ((ρS r s c)^[t] (d, E)).1 ((ρS r s c)^[t] (d, E)).2 ε → CapDom r s c zE →
      CapDom r s c zO → OnSide r s c j zE → OnSide r s c j zO → zO - zE ∈ unitVec →
      cross d zE = E → cross d (zO - zE) = ε → (Out r s c j (zE + d) ∨ Out r s c j (zO + d)) →
      T.tube r s (rotN (gk c j) d) (E + cross (rotN (gk c j) d) (gτ p r s w c j)) ε := by
  intro t
  induction t with
  | zero => intro j hj d E ε zE zO h; exact R.capT c hc j hj d E ε zE zO h
  | succ t ih =>
    intro j hj d E ε zE zO h h1 h2 h3 h4 h5 h6 h7 h8
    rw [Function.iterate_succ_apply] at h
    have hj' : (j + 2) % 6 < 6 := by omega
    have key := ih ((j + 2) % 6) hj' (rotN 2 d) (E + cross (rotN 2 d) (ρτ r s c))
      ε (ρz r s c zE) (ρz r s c zO) h ((capDom_ρ hc _).2 h1) ((capDom_ρ hc _).2 h2)
      ((onSide_ρ hc hj _).2 h3) ((onSide_ρ hc hj _).2 h4)
      (by rw [ρz_sub]; exact rotN_unit' 2 h5) (by rw [cross_ρz, h6])
      (by rw [ρz_sub, cross_rotN, h7])
      (by rw [← ρz_add, ← ρz_add, out_ρ hc hj, out_ρ hc hj]; exact h8)
    rw [gk_ρ hc hj] at key
    refine tube_eq key (lam c j * ((rotN (gk c j) d).1 + (rotN (gk c j) d).2)) ?_
    have e1 : cross (rotN 2 d) (ρτ r s c) =
        cross (rotN (gk c j) d) (rotN (gk c ((j + 2) % 6)) (ρτ r s c)) := by
      rw [← gk_ρ hc hj d, cross_rotN]
    rw [e1]
    have e2 := congrArg (cross (rotN (gk c j) d)) (gτ_ρ (p := p) (r := r) (s := s) (w := w) hc hj)
    rw [cross_add', cross_add', cross_shift] at e2
    linarith

/-- The cap → tube field of `InvOK`. -/
theorem capT_GG {T : Tabs} (R : RedOK p r s w k T) {c : ℕ} (hc : c < 2) {j : ℕ} (hj : j < 6)
    {d : ℤ × ℤ} {E ε : ℤ} {zE zO : ℤ × ℤ} (h : T.GG p r s c d E ε) (h1 : CapDom r s c zE)
    (h2 : CapDom r s c zO) (h3 : OnSide r s c j zE) (h4 : OnSide r s c j zO)
    (h5 : zO - zE ∈ unitVec) (h6 : cross d zE = E) (h7 : cross d (zO - zE) = ε)
    (h8 : Out r s c j (zE + d) ∨ Out r s c j (zO + d)) :
    T.GG p r s 2 (rotN (gk c j) d) (E + cross (rotN (gk c j) d) (gτ p r s w c j)) ε := by
  have hcap : T.cap r s c d E ε := by
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> simpa [Tabs.GG] using h
  obtain ⟨t, -, ht⟩ := hcap
  have := capT_full R hc t j hj d E ε zE zO ht h1 h2 h3 h4 h5 h6 h7 h8
  simp only [Tabs.GG, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, ite_false]
  exact Or.inl this

/-! ## The tube → cap transition -/

theorem cross_per (D : ℤ × ℤ) : cross D (per r s) = (2 * r + s) * (-3 * (D.1 + D.2)) := by
  simp only [cross, per]; ring

/-- A horizontal tube state never enters a cap. -/
theorem hz_no_cap {c j : ℕ} (hc : c < 2) (hj : j < 6) {d' y : ℤ × ℤ}
    (hh : (rotN (gk c j) d').1 + (rotN (gk c j) d').2 = 0) (hy : OnSide r s c j y) :
    ¬ Inn1 r s c j (y + d') := by
  obtain ⟨a, b⟩ := d'
  obtain ⟨x, z⟩ := y
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> interval_cases j <;>
    simp only [gk, rotN, rot, OnSide, Inn1, Prod.mk_add_mk] at hh hy ⊢ <;> omega

theorem Tcap_GG {T : Tabs} (R : RedOK p r s w k T) {c : ℕ} (hc : c < 2) {j : ℕ} (hj : j < 6)
    {d' : ℤ × ℤ} {E ε : ℤ} {yE yO : ℤ × ℤ} {t : ℤ}
    (h : T.GG p r s 2 (rotN (gk c j) d') E ε) (h1 : CapDom r s c yE) (h2 : CapDom r s c yO)
    (h3 : OnSide r s c j yE) (h4 : OnSide r s c j yO) (h5 : yO - yE ∈ unitVec)
    (h6 : E = cross (rotN (gk c j) d') (gmap p r s w c j yE - t • per r s))
    (h7 : cross d' (yO - yE) = ε) (h8 : Inn1 r s c j (yE + d') ∨ Inn1 r s c j (yO + d')) :
    T.GG p r s c d' (cross d' yE) ε := by
  simp only [Tabs.GG, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num,
    ite_false] at h
  rcases h with ⟨f, Q, h0, hE⟩ | hz
  · have key : cross d' yE = f - cross (rotN (gk c j) d') (gτ p r s w c j) +
        (2 * r + s) * (Q - 3 * t * ((rotN (gk c j) d').1 + (rotN (gk c j) d').2)) := by
      have e1 := cross_gmap (p := p) (r := r) (s := s) (w := w) c j d' yE
      rw [cross_sub', show cross (rotN (gk c j) d') (t • per r s) =
        t * cross (rotN (gk c j) d') (per r s) by
        simp [cross, per, Prod.smul_mk, smul_eq_mul]; ring, cross_per] at h6
      rw [hE] at h6
      linear_combination -e1 - h6
    -- rotate the cap so that the side becomes a base side
    have hr := R
    set t' := (3 - j / 2) % 3 with ht'
    have hj0 : (j + 2 * t') % 6 < 2 := by omega
    obtain ⟨l, hl⟩ := gmap_Zi (p := p) (w := w) hc hj t' yE
    have hD := gk_Ri hc hj t' d'
    have e1 := cross_gmap (p := p) (r := r) (s := s) (w := w) c ((j + 2 * t') % 6) (Ri t' d')
      (Zi r s c t' yE)
    have e2 := cross_gmap (p := p) (r := r) (s := s) (w := w) c j d' yE
    rw [hD, hl, cross_add', cross_shift] at e1
    have key1 : cross (Ri t' d') (Zi r s c t' yE) = f -
        cross (rotN (gk c ((j + 2 * t') % 6)) (Ri t' d')) (gτ p r s w c ((j + 2 * t') % 6)) +
        (2 * r + s) * (Q - 3 * t * ((rotN (gk c j) d').1 + (rotN (gk c j) d').2) -
          l * ((rotN (gk c j) d').1 + (rotN (gk c j) d').2)) := by
      rw [hD]; linear_combination key + e2 - e1
    obtain ⟨s1, -, s3⟩ := side_Zi (r := r) (s := s) hc hj t' yE
    obtain ⟨s1', -, s3'⟩ := side_Zi (r := r) (s := s) hc hj t' yO
    have := R.Tcap c hc ((j + 2 * t') % 6) hj0 (Ri t' d') f ε (Zi r s c t' yE) (Zi r s c t' yO)
      _ (by rw [hD]; exact h0) ((capDom_Zi hc t' yE).2 h1) ((capDom_Zi hc t' yO).2 h2)
      (s1.2 h3) (s1'.2 h4) (by rw [Zi_sub]; exact unit_Ri _ h5) key1
      (by rw [Zi_sub, cross_Ri, h7])
      (by rw [← Zi_add, ← Zi_add, (side_Zi (r := r) (s := s) hc hj t' (yE + d')).2.2,
        (side_Zi (r := r) (s := s) hc hj t' (yO + d')).2.2]; exact h8)
    have := cap_iter (x := (d', cross d' yE)) (t := t') (by rw [state_iter]; exact this)
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> simpa [Tabs.GG] using this
  · exfalso
    have hh : (rotN (gk c j) d').1 + (rotN (gk c j) d').2 = 0 := by
      simp only [Hz] at hz
      rcases hz with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> norm_num
    rcases h8 with h8 | h8
    · exact hz_no_cap hc hj hh h3 h8
    · exact hz_no_cap hc hj hh h4 h8

end Claude5E10
