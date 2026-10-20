import Formal.Claude4K3Seam

/-!
# K3 pieces: chords across the cap corners, and the bottom seam by reflection

Written by a Claude worker (2026-10-20, K3 bridge).  Pure arithmetic.

At a corner `A` of a cap (angle `a0 ∈ {0, 2r, 4r}`) the two seam points next to `A` are adjacent
through the cap (a *chord*), but not through the tube; their only common tube neighbour inside the
tube region is `A` itself.  The bottom seam `h = 2s + zz a` is the image of the top seam under the
reflection `τ (h, a) = (2s - h, a)`, which preserves tube adjacency and the tube region.
-/

namespace Claude4K3

variable {r s : ℤ}

/-- The two neighbours on the top seam of a top corner. -/
def ChordT (r : ℤ) (b c : ℤ × ℤ) : Prop :=
  b.1 = -1 ∧ c.1 = -1 ∧ ((b.2 = 6 * r - 1 ∧ c.2 = 1) ∨ (b.2 = 1 ∧ c.2 = 6 * r - 1) ∨
    (b.2 = 2 * r - 1 ∧ c.2 = 2 * r + 1) ∨ (b.2 = 2 * r + 1 ∧ c.2 = 2 * r - 1) ∨
    (b.2 = 4 * r - 1 ∧ c.2 = 4 * r + 1) ∨ (b.2 = 4 * r + 1 ∧ c.2 = 4 * r - 1))

theorem chordT_not_TA (hr : 2 ≤ r) {b c : ℤ × ℤ} (h : ChordT r b c) : ¬ TA r b c := by
  obtain ⟨h1, h2, h3⟩ := h
  intro ht
  simp only [TA, AE] at ht
  rcases h3 with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> omega

theorem zz_corner (hr : 2 ≤ r) {a : ℤ} (h : a = 0 ∨ a = 2 * r ∨ a = 4 * r) : zz r a = 0 := by
  simp only [zz]; split_ifs <;> omega

set_option maxHeartbeats 2000000 in
theorem chordT_pos (hr : 2 ≤ r) {b c x : ℤ × ℤ} (h : ChordT r b c) (hx : AR r x)
    (h1 : TA r b x) (h2 : TA r c x) :
    (x.2 = 0 ∨ x.2 = 2 * r ∨ x.2 = 4 * r) ∧ (x.1 = 0 ∨ x.1 = -2) := by
  obtain ⟨e1, e2, h3⟩ := h
  obtain ⟨x1, x2⟩ := x
  simp only [AR] at hx
  simp only [TA, AE] at h1 h2
  dsimp only at *
  rcases h3 with ⟨e3, e4⟩ | ⟨e3, e4⟩ | ⟨e3, e4⟩ | ⟨e3, e4⟩ | ⟨e3, e4⟩ | ⟨e3, e4⟩ <;>
  refine ⟨?_, ?_⟩ <;> omega

/-- The only common tube neighbour of a chord inside the tube region is the corner. -/
theorem chordT_apex (hr : 2 ≤ r) {b c x : ℤ × ℤ} (h : ChordT r b c) (hx : RM r s x)
    (h1 : TA r b x) (h2 : TA r c x) : TopB r x := by
  obtain ⟨ha, hlo, -⟩ := hx
  obtain ⟨k1, k2⟩ := chordT_pos hr h ha h1 h2
  have hz := zz_corner hr k1
  refine ⟨ha, ?_⟩
  omega

/-! ## Reflection -/

/-- The reflection exchanging the two seams. -/
def tau (s : ℤ) (t : ℤ × ℤ) : ℤ × ℤ := (2 * s - t.1, t.2)

theorem TA_tau {t u : ℤ × ℤ} (h : TA r t u) : TA r (tau s t) (tau s u) := by
  simp only [TA, tau] at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, h2⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, h2⟩))
  · exact Or.inr (Or.inl ⟨by omega, h2⟩)
  · exact Or.inl ⟨by omega, h2⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, h2⟩))))

theorem RM_tau {t : ℤ × ℤ} (h : RM r s t) : RM r s (tau s t) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, by simp only [tau]; omega, by simp only [tau]; omega⟩

theorem tau_inj {t u : ℤ × ℤ} (h : tau s t = tau s u) : t = u := by
  obtain ⟨t1, t2⟩ := t; obtain ⟨u1, u2⟩ := u
  simp only [tau, Prod.mk.injEq] at h
  ext <;> simp <;> omega

/-- On the bottom seam (same as `BotB` of the seam-site file). -/
def BotS (r s : ℤ) (t : ℤ × ℤ) : Prop := AR r t ∧ t.1 = 2 * s + zz r t.2

theorem TopB_tau {t : ℤ × ℤ} (h : BotS r s t) : TopB r (tau s t) := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, by simp only [tau]; omega⟩

theorem BotS_of_tau {t : ℤ × ℤ} (h : TopB r (tau s t)) : BotS r s t := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, by simp only [tau] at h2; omega⟩

/-- The two neighbours on the bottom seam of a bottom corner. -/
def ChordB (r s : ℤ) (b c : ℤ × ℤ) : Prop := ChordT r (tau s b) (tau s c)

theorem chordB_not_TA (hr : 2 ≤ r) {b c : ℤ × ℤ} (h : ChordB r s b c) : ¬ TA r b c :=
  fun ht => chordT_not_TA hr h (TA_tau ht)

theorem chordB_apex (hr : 2 ≤ r) {b c x : ℤ × ℤ} (h : ChordB r s b c) (hx : RM r s x)
    (h1 : TA r b x) (h2 : TA r c x) : BotS r s x :=
  BotS_of_tau (chordT_apex hr h (RM_tau hx) (TA_tau h1) (TA_tau h2))

theorem bot_tube_apex (hr : 2 ≤ r) {b c x y : ℤ × ℤ} (hb : BotS r s b) (hc : BotS r s c)
    (h : TA r b c) (hx : RM r s x) (hy : RM r s y) (hbx : TA r b x) (hcx : TA r c x)
    (hby : TA r b y) (hcy : TA r c y) : x = y :=
  tau_inj (top_tube_apex hr (TopB_tau hb) (TopB_tau hc) (TA_tau h) (RM_tau hx) (RM_tau hy)
    (TA_tau hbx) (TA_tau hcx) (TA_tau hby) (TA_tau hcy))

end Claude4K3
