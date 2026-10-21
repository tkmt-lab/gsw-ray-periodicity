import Formal.Claude5E10Assemble2

/-!
# E10 model: the assembled invariant satisfies `InvOK` (`assemble`)

Written by a Claude worker (2026-10-20, E10 bridge session).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w k : ℤ}

/-- Every cap corner is a rotation of a base corner. -/
theorem corner_orbit {c : ℕ} (hc : c < 2) {a : ℤ × ℤ} (h : CornerPos p r s w c a) :
    ∃ t i, t < 3 ∧ i < 2 ∧ a = Zi r s c t (bc r s c i) := by
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> simp only [CornerPos] at h <;>
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 0, by norm_num, by norm_num, rfl⟩
  · exact ⟨0, 1, by norm_num, by norm_num, rfl⟩
  · exact ⟨1, 0, by norm_num, by norm_num, by ext <;> simp [Zi, ρz, ρτ, bc, rotN, rot] <;> ring⟩
  · exact ⟨1, 1, by norm_num, by norm_num, by ext <;> simp [Zi, ρz, ρτ, bc, rotN, rot] <;> ring⟩
  · exact ⟨2, 0, by norm_num, by norm_num, by ext <;> simp [Zi, ρz, ρτ, bc, rotN, rot] <;> ring⟩
  · exact ⟨2, 1, by norm_num, by norm_num, by ext <;> simp [Zi, ρz, ρτ, bc, rotN, rot] <;> ring⟩
  · exact ⟨0, 0, by norm_num, by norm_num, rfl⟩
  · exact ⟨0, 1, by norm_num, by norm_num, rfl⟩
  · exact ⟨1, 0, by norm_num, by norm_num, by ext <;> simp [Zi, ρz, ρτ, bc, rotN, rot] <;> ring⟩
  · exact ⟨1, 1, by norm_num, by norm_num, by ext <;> simp [Zi, ρz, ρτ, bc, rotN, rot] <;> ring⟩
  · exact ⟨2, 0, by norm_num, by norm_num, by ext <;> simp [Zi, ρz, ρτ, bc, rotN, rot] <;> ring⟩
  · exact ⟨2, 1, by norm_num, by norm_num, by ext <;> simp [Zi, ρz, ρτ, bc, rotN, rot] <;> ring⟩

/-- Tube corners, modulo `m`. -/
theorem tube_corner (H : Hyp p r s w) (TW : Tw p r s w k) {z : ℤ × ℤ}
    (h : CornerPos p r s w 2 z) :
    (z.1 + z.2 = 0 ∧ ∃ cc X, (cc = 0 ∨ cc = r + s) ∧ z.1 = cc + (2 * r + s) * X) ∨
      (z.1 + z.2 = 2 * p ∧ ∃ cc X, (cc = 0 ∨ cc = r + s) ∧ z.1 = cc + k + (2 * r + s) * X) := by
  have hr := H.hr; have hs := H.hs; have hw0 := H.hw0; have hw1 := H.hw1
  have hP : 0 < 3 * (2 * r + s) := by omega
  obtain ⟨ex, -, -⟩ := emod_decomp hP z.1
  simp only [CornerPos, ht] at h
  rcases h with ⟨h0, ha⟩ | ⟨h0, a, ha, hw⟩
  · refine Or.inl ⟨h0, ?_⟩
    generalize z.1 % (3 * (2 * r + s)) = u at ex ha
    generalize z.1 / (3 * (2 * r + s)) = q at ex
    simp only [IsArc] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, 3 * q, Or.inl rfl, by rw [ex]; ring⟩
    · exact ⟨r + s, 3 * q, Or.inr rfl, by rw [ex]; ring⟩
    · exact ⟨0, 3 * q + 1, Or.inl rfl, by rw [ex]; ring⟩
    · exact ⟨r + s, 3 * q + 1, Or.inr rfl, by rw [ex]; ring⟩
    · exact ⟨0, 3 * q + 2, Or.inl rfl, by rw [ex]; ring⟩
    · exact ⟨r + s, 3 * q + 2, Or.inr rfl, by rw [ex]; ring⟩
  · refine Or.inr ⟨h0, ?_⟩
    obtain ⟨qw, hqw⟩ := TW.qw
    generalize z.1 % (3 * (2 * r + s)) = u at ex hw
    generalize z.1 / (3 * (2 * r + s)) = q at ex
    have hwr : wrap r s (a + w) = a + w ∨ wrap r s (a + w) = a + w - 3 * (2 * r + s) := by
      unfold wrap; split_ifs <;> simp
    simp only [IsArc] at ha
    rcases hwr with e | e <;> rw [e] at hw <;> subst hw <;> rw [hqw] at ex <;>
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, 3 * q + qw, Or.inl rfl, by rw [ex]; ring⟩
    · exact ⟨r + s, 3 * q + qw, Or.inr rfl, by rw [ex]; ring⟩
    · exact ⟨0, 3 * q + qw + 1, Or.inl rfl, by rw [ex]; ring⟩
    · exact ⟨r + s, 3 * q + qw + 1, Or.inr rfl, by rw [ex]; ring⟩
    · exact ⟨0, 3 * q + qw + 2, Or.inl rfl, by rw [ex]; ring⟩
    · exact ⟨r + s, 3 * q + qw + 2, Or.inr rfl, by rw [ex]; ring⟩
    · exact ⟨0, 3 * q + qw - 3, Or.inl rfl, by rw [ex]; ring⟩
    · exact ⟨r + s, 3 * q + qw - 3, Or.inr rfl, by rw [ex]; ring⟩
    · exact ⟨0, 3 * q + qw - 2, Or.inl rfl, by rw [ex]; ring⟩
    · exact ⟨r + s, 3 * q + qw - 2, Or.inr rfl, by rw [ex]; ring⟩
    · exact ⟨0, 3 * q + qw - 1, Or.inl rfl, by rw [ex]; ring⟩
    · exact ⟨r + s, 3 * q + qw - 1, Or.inr rfl, by rw [ex]; ring⟩

theorem ρS_iter_mod (c t : ℕ) (x : (ℤ × ℤ) × ℤ) :
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

/-! ## Start -/

theorem start_cap {T : Tabs} (R : RedOK p r s w k T) {c : ℕ} (hc : c < 2) {a b e : ℤ × ℤ}
    (ha : CornerPos p r s w c a) (hb : CapDom r s c b) (he : CapDom r s c e)
    (u1 : b - a ∈ unitVec) (u2 : e - a ∈ unitVec) (u3 : e - b ∈ unitVec) :
    T.cap r s c (e - a) (cross (e - a) a) (cross (e - a) (b - a)) := by
  obtain ⟨t, i, ht, hi, rfl⟩ := corner_orbit hc ha
  set t' := (3 - t) % 3
  have back : Zi r s c t' (Zi r s c t (bc r s c i)) = bc r s c i := by
    rw [Zi_comp]
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
    · rfl
    · exact Zi3 c _
    · exact Zi3 c _
  have key := R.startC c hc i hi (Zi r s c t' b) (Zi r s c t' e) ((capDom_Zi hc t' b).2 hb)
    ((capDom_Zi hc t' e).2 he) (by rw [← back, Zi_sub]; exact unit_Ri _ u1)
    (by rw [← back, Zi_sub]; exact unit_Ri _ u2) (by rw [Zi_sub]; exact unit_Ri _ u3)
  rw [← back, Zi_sub, Zi_sub, cross_Ri] at key
  obtain ⟨t1, ht1, hk⟩ := key
  rw [← state_iter] at hk
  refine ⟨(t1 + t') % 3, Nat.mod_lt _ (by norm_num), ?_⟩
  rw [← Function.iterate_add_apply, ρS_iter_mod] at hk
  exact hk

set_option maxHeartbeats 1000000 in
-- 36 unit cases
/-- A horizontal start along a seam. -/
theorem hz_start {a b e : ℤ × ℤ} (hp : 1 ≤ p) (u1 : b - a ∈ unitVec) (u2 : e - a ∈ unitVec)
    (u3 : e - b ∈ unitVec) (hh : (e - a).1 + (e - a).2 = 0) (hb : HT p b)
    (ha : a.1 + a.2 = 0 ∨ a.1 + a.2 = 2 * p) :
    Hz p (e - a) (cross (e - a) a) (cross (e - a) (b - a)) := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨e1, e2⟩ := e
  rw [unit_sub] at u1 u2 u3
  simp only [U2] at u1 u2 u3
  simp only [HT] at hb
  simp only [Prod.mk_sub_mk] at hh ⊢
  simp only at u1 u2 u3 hh hb ha
  have : (e1 - a1 = 1 ∧ e2 - a2 = -1) ∨ (e1 - a1 = -1 ∧ e2 - a2 = 1) := by omega
  clear u2 hh
  rcases this with ⟨x1, x2⟩ | ⟨x1, x2⟩ <;>
    simp only [Hz, cross, Prod.mk.injEq, x1, x2, true_and, and_true, true_or, or_true,
      show (1 : ℤ) ≠ -1 by norm_num, show (-1 : ℤ) ≠ 1 by norm_num, false_and, and_false,
      false_or, or_false] <;> omega

theorem start_tube {T : Tabs} (H : Hyp p r s w) (TW : Tw p r s w k) (R : RedOK p r s w k T)
    {a b e : ℤ × ℤ} (ha : CornerPos p r s w 2 a) (hb : HT p b) (he : HT p e)
    (u1 : b - a ∈ unitVec) (u2 : e - a ∈ unitVec) (u3 : e - b ∈ unitVec) :
    T.tube r s (e - a) (cross (e - a) a) (cross (e - a) (b - a)) ∨
      Hz p (e - a) (cross (e - a) a) (cross (e - a) (b - a)) := by
  have hp := H.hp
  have v3 : (e - a) - (b - a) ∈ unitVec := by rw [sub_sub_sub_cancel_right]; exact u3
  simp only [HT] at hb he
  rcases tube_corner H TW ha with ⟨h0, cc, X, hcc, hx⟩ | ⟨h0, cc, X, hcc, hx⟩
  · by_cases hh : (e - a).1 + (e - a).2 = 0
    · exact Or.inr (hz_start hp u1 u2 u3 hh hb (Or.inl h0))
    · left
      have hl := (R.startT cc hcc (b - a) (e - a) u1 u2 v3 hh).1 (by
        simp only [Prod.fst_sub, Prod.snd_sub]; omega)
      refine tube_eq hl (-((e - a).1 + (e - a).2) * X) ?_
      simp only [cross]
      have : a.2 = -a.1 := by omega
      rw [this, hx]; ring
  · obtain ⟨qp, hqp⟩ := TW.qp
    by_cases hh : (e - a).1 + (e - a).2 = 0
    · exact Or.inr (hz_start hp u1 u2 u3 hh hb (Or.inr h0))
    · left
      have hl := (R.startT cc hcc (b - a) (e - a) u1 u2 v3 hh).2 (by
        simp only [Prod.fst_sub, Prod.snd_sub]; omega)
      refine tube_eq hl ((e - a).1 * (2 * qp - X) - (e - a).2 * X) ?_
      simp only [cross]
      have : a.2 = 2 * p - a.1 := by omega
      rw [this, hx, hqp]; ring

end Claude5E10
