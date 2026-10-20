import Formal.Claude4K3PieceArith

/-!
# K3 pieces: arithmetic of the top seam

Written by a Claude worker (2026-10-20, K3 bridge).  See `Claude4K3PieceArith.lean`.
-/


namespace Claude4K3

variable {r s : ℤ}

/-! ## The top seam -/

theorem topB_cases (hr : 0 < r) {t : ℤ × ℤ} (h : TopB r t) :
    (0 ≤ t.2 ∧ t.2 ≤ r ∧ t.1 = -t.2 ∧ (bT r t.2).1 = 0 ∧ (bT r t.2).2 = t.2) ∨
    (r < t.2 ∧ t.2 ≤ 2 * r ∧ t.1 = t.2 - 2 * r ∧ (bT r t.2).1 = 0 ∧ (bT r t.2).2 = t.2) ∨
    (2 * r < t.2 ∧ t.2 ≤ 3 * r ∧ t.1 = 2 * r - t.2 ∧ (bT r t.2).1 = t.2 - 2 * r ∧
      (bT r t.2).2 = 4 * r - t.2) ∨
    (3 * r < t.2 ∧ t.2 ≤ 4 * r ∧ t.1 = t.2 - 4 * r ∧ (bT r t.2).1 = t.2 - 2 * r ∧
      (bT r t.2).2 = 4 * r - t.2) ∨
    (4 * r < t.2 ∧ t.2 ≤ 5 * r ∧ t.1 = 4 * r - t.2 ∧ (bT r t.2).1 = 6 * r - t.2 ∧
      (bT r t.2).2 = 0) ∨
    (5 * r < t.2 ∧ t.2 < 6 * r ∧ t.1 = t.2 - 6 * r ∧ (bT r t.2).1 = 6 * r - t.2 ∧
      (bT r t.2).2 = 0) := by
  obtain ⟨⟨h0, h6⟩, he⟩ := h
  simp only [zz, bT] at he ⊢
  split_ifs at he ⊢ <;> omega

theorem zz_cases (r a : ℤ) :
    (a ≤ r ∧ zz r a = a) ∨ (r < a ∧ a ≤ 2 * r ∧ zz r a = 2 * r - a) ∨
    (2 * r < a ∧ a ≤ 3 * r ∧ zz r a = a - 2 * r) ∨ (3 * r < a ∧ a ≤ 4 * r ∧ zz r a = 4 * r - a) ∨
    (4 * r < a ∧ a ≤ 5 * r ∧ zz r a = a - 4 * r) ∨ (5 * r < a ∧ zz r a = 6 * r - a) := by
  simp only [zz]
  split_ifs <;> omega

theorem zz_eq_of {x b : ℤ × ℤ} (hx : AR r x) (hb : AR r b) (h : AE r x.2 b.2) :
    zz r x.2 = zz r b.2 := by
  have : x.2 = b.2 := by simp only [AR, AE] at *; omega
  rw [this]

set_option maxHeartbeats 4000000 in
theorem seam_inner_aux (hr : 2 ≤ r) (b1 b2 c1 c2 x1 x2 e1 e2 f1 f2 : ℤ)
    (hb0 : 0 ≤ b2) (hb6 : b2 < 6 * r) (hc0 : 0 ≤ c2) (hc6 : c2 < 6 * r) (hx0 : 0 ≤ x2)
    (hx6 : x2 < 6 * r) (zb zc zx : ℤ) (hzb : b1 = -zb) (hzc : c1 = -zc) (hzx : -zx ≤ x1)
    (ebc : c2 = b2 → zc = zb) (ebx : x2 = b2 → zx = zb) (ecx : x2 = c2 → zx = zc)
    (he : Unit (e1, e2)) (hc1 : c1 = b1 + (e2 - e1)) (hc2 : AE r c2 (b2 + (e1 + e2)))
    (hx1 : x1 = b1 + (f2 - f1)) (hx2 : AE r x2 (b2 + (f1 + f2)))
    (hf : (f1 = -e2 ∧ f2 = e1 + e2) ∨ (f1 = e1 + e2 ∧ f2 = -e1)) :
    (e1 = 1 ∧ e2 = 0 ∧ f1 = 0 ∧ f2 = 1) ∨ (e1 = 0 ∧ e2 = 1 ∧ f1 = -1 ∧ f2 = 1) ∨
    (e1 = -1 ∧ e2 = 0 ∧ f1 = -1 ∧ f2 = 1) ∨ (e1 = 0 ∧ e2 = -1 ∧ f1 = -1 ∧ f2 = 0) := by
  simp only [Unit, AE] at he hc2 hx2
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num <;> omega

/-- Only one tube triangle on a seam edge lies in the tube region. -/
theorem top_tube_apex (hr : 2 ≤ r) {b c x y : ℤ × ℤ} (hb : TopB r b) (hc : TopB r c)
    (h : TA r b c) (hx : RM r s x) (hy : RM r s y) (hbx : TA r b x) (hcx : TA r c x)
    (hby : TA r b y) (hcy : TA r c y) : x = y := by
  obtain ⟨e, he, he1, he2⟩ := ta_lift h
  obtain ⟨f, hf, hf1, hf2⟩ := ta_lift hbx
  obtain ⟨g, hg, hg1, hg2⟩ := ta_lift hby
  have u1 := ta_unlift hr he hf he1 he2 hf1 hf2 hcx
  have u2 := ta_unlift hr he hg he1 he2 hg1 hg2 hcy
  have h0 : ∀ v : ℤ × ℤ, v - 0 = v := fun v => sub_zero v
  have af := planar_apex (P := 0) (Q := e) (by rwa [h0]) (by rwa [h0]) u1
  have ag := planar_apex (P := 0) (Q := e) (by rwa [h0]) (by rwa [h0]) u2
  obtain ⟨e1, e2⟩ := e; obtain ⟨f1, f2⟩ := f; obtain ⟨g1, g2⟩ := g
  obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c; obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
  simp only [Prod.fst_zero, Prod.snd_zero, zero_sub, zero_add, sub_zero] at af ag
  obtain ⟨⟨hb0, hb6⟩, hb1⟩ := hb
  obtain ⟨⟨hc0, hc6⟩, hc1⟩ := hc
  obtain ⟨⟨hx0, hx6⟩, hx1, -⟩ := hx
  obtain ⟨⟨hy0, hy6⟩, hy1, -⟩ := hy
  dsimp only at *
  have k1 := seam_inner_aux hr b1 b2 c1 c2 x1 x2 e1 e2 f1 f2 hb0 hb6 hc0 hc6 hx0 hx6 _ _ _
    hb1 hc1 hx1 (fun h => by rw [h]) (fun h => by rw [h]) (fun h => by rw [h]) he he1 he2 hf1 hf2
    (by omega)
  have k2 := seam_inner_aux hr b1 b2 c1 c2 y1 y2 e1 e2 g1 g2 hb0 hb6 hc0 hc6 hy0 hy6 _ _ _
    hb1 hc1 hy1 (fun h => by rw [h]) (fun h => by rw [h]) (fun h => by rw [h]) he he1 he2 hg1 hg2
    (by omega)
  have hfg : f1 = g1 ∧ f2 = g2 := by omega
  obtain ⟨rfl, rfl⟩ := hfg
  exact ta_eq_of_lift (b := (b1, b2)) (e := (f1, f2)) ⟨hx0, hx6⟩ ⟨hy0, hy6⟩ hf1 hf2 hg1 hg2

end Claude4K3
