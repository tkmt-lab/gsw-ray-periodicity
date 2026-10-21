import Formal.Claude5E10Step2

/-!
# E10 model: line-state invariants kill literal paths

Written by a Claude worker (2026-10-20, E10 bridge session).

Along a literal path, the triangle at index `i` is a frame `(c, a, b, e)`; its *line state* is
the chart `c`, the direction `d = e − a`, the offset `E = cross d (even point)` of the line of
the even-indexed points and `ε = cross d (odd point − even point)`.  A predicate `G` on line
states that contains the states at the corners (`start`), is carried along by the side
isometries (`capT`, `Tcap`), and never has a corner on the odd line (`avoid`), forbids literal
paths: the last point of a path is a corner at an odd index (`no_path_of_inv`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

namespace Claude5E10

open ClaudeChallenge Claude2Aligned

variable {p r s w : ℤ}

/-- The six corner arclengths (the same set for both caps). -/
def IsArc (r s a : ℤ) : Prop :=
  a = 0 ∨ a = r + s ∨ a = 2 * r + s ∨ a = 3 * r + 2 * s ∨ a = 4 * r + 2 * s ∨ a = 5 * r + 3 * s

/-- The twelve corner vertices. -/
def IsCornerV (p r s w : ℤ) (v : MV) : Prop :=
  (∃ a, IsArc r s a ∧ v = (2, (a, 0))) ∨ (∃ a, IsArc r s a ∧ v = (2, (wrap r s (a + w), 2 * p)))

/-- Corner positions in the charts. -/
def CornerPos (p r s w : ℤ) : ℕ → ℤ × ℤ → Prop
  | 0, z => z = (0, 0) ∨ z = (r, 0) ∨ z = (r, r + s) ∨ z = (0, 2 * r + s) ∨
      z = (-(r + s), 2 * r + s) ∨ z = (-(r + s), r + s)
  | 1, z => z = (0, 0) ∨ z = (r + s, 0) ∨ z = (r + s, r) ∨ z = (0, 2 * r + s) ∨
      z = (-r, 2 * r + s) ∨ z = (-r, r)
  | _, z => (ht z = 0 ∧ IsArc r s (z.1 % (3 * (2 * r + s)))) ∨
      (ht z = 2 * p ∧ ∃ a, IsArc r s a ∧ z.1 % (3 * (2 * r + s)) = wrap r s (a + w))

theorem PL_arc (hr : 1 ≤ r) (hs : 1 ≤ s) {a : ℤ} (h : IsArc r s a) :
    CornerPos p r s w 0 (PL r s a) := by
  simp only [IsArc] at h
  simp only [CornerPos, PL]
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> split_ifs <;>
    simp only [Prod.mk.injEq] <;> e10om

theorem PU_arc (hr : 1 ≤ r) (hs : 1 ≤ s) {a : ℤ} (h : IsArc r s a) :
    CornerPos p r s w 1 (PU r s a) := by
  simp only [IsArc] at h
  simp only [CornerPos, PU]
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> split_ifs <;>
    simp only [Prod.mk.injEq] <;> e10om

theorem arc_range (hr : 1 ≤ r) (hs : 1 ≤ s) {a : ℤ} (h : IsArc r s a) :
    0 ≤ a ∧ a < 3 * (2 * r + s) := by
  simp only [IsArc] at h; omega

/-- A corner seen in a chart sits at a corner position. -/
theorem corner_pos (H : Hyp p r s w) {c : ℕ} {v : MV} {z : ℤ × ℤ} (hz : InC p r s w c v z)
    (hv : IsCornerV p r s w v) : CornerPos p r s w c z := by
  obtain ⟨hc, hd, rfl⟩ := hz
  have hr := H.hr; have hs := H.hs; have hp := H.hp
  rcases c_cases hc with rfl | rfl | rfl
  · simp only [Dom] at hd
    by_cases hI : IL r s z
    · rw [chL_I hI] at hv
      rcases hv with ⟨a, -, h⟩ | ⟨a, -, h⟩ <;> simp at h
    · rw [chL_B hI] at hv
      rcases hv with ⟨a, ha, h⟩ | ⟨a, ha, h⟩
      · simp only [Prod.mk.injEq, true_and, and_true] at h
        rw [eq_PL hr hs hd hI, h]; exact PL_arc hr hs ha
      · simp only [Prod.mk.injEq, true_and] at h; omega
  · simp only [Dom] at hd
    by_cases hI : IU r s z
    · rw [chU_I hI] at hv
      rcases hv with ⟨a, -, h⟩ | ⟨a, -, h⟩ <;> simp at h
    · rw [chU_B hI] at hv
      rcases hv with ⟨a, ha, h⟩ | ⟨a, ha, h⟩
      · simp only [Prod.mk.injEq, true_and] at h; omega
      · simp only [Prod.mk.injEq, true_and] at h
        have l1 := aU_range hr hs hd hI
        have l2 := arc_range hr hs ha
        have hw0 := H.hw0; have hw1 := H.hw1
        have : aU r s z = a := by
          have h1 := h.1; unfold wrap at h1; split_ifs at h1 <;> omega
        rw [eq_PU hr hs hd hI, this]; exact PU_arc hr hs ha
  · simp only [Dom, HT] at hd
    rw [chT] at hv
    rcases hv with ⟨a, ha, h⟩ | ⟨a, ha, h⟩
    · simp only [Prod.mk.injEq, true_and] at h
      exact Or.inl ⟨by simp only [ht]; exact h.2, by rw [h.1]; exact ha⟩
    · simp only [Prod.mk.injEq, true_and] at h
      exact Or.inr ⟨by simp only [ht]; exact h.2, a, ha, h.1⟩

/-! ## The invariant -/

/-- The even- and odd-indexed points of the frame `(a, b, ·)` at index `i`. -/
def ev (i : ℕ) (a b : ℤ × ℤ) : ℤ × ℤ := if i % 2 = 0 then a else b
def od (i : ℕ) (a b : ℤ × ℤ) : ℤ × ℤ := if i % 2 = 0 then b else a

/-- What a line-state predicate must satisfy. -/
structure InvOK (p r s w : ℤ) (G : ℕ → ℤ × ℤ → ℤ → ℤ → Prop) : Prop where
  start : ∀ c a b e, c < 3 → CornerPos p r s w c a → Dom p r s c a → Dom p r s c b →
    Dom p r s c e → b - a ∈ unitVec → e - a ∈ unitVec → e - b ∈ unitVec →
    G c (e - a) (cross (e - a) a) (cross (e - a) (b - a))
  avoid : ∀ c d E ε z, c < 3 → G c d E ε → CornerPos p r s w c z → cross d z ≠ E + ε
  capT : ∀ c j, c < 2 → j < 6 → ∀ d E ε zE zO, G c d E ε → CapDom r s c zE →
    CapDom r s c zO → OnSide r s c j zE → OnSide r s c j zO → zO - zE ∈ unitVec →
    cross d zE = E → cross d (zO - zE) = ε → (Out r s c j (zE + d) ∨ Out r s c j (zO + d)) →
    G 2 (rotN (gk c j) d) (E + cross (rotN (gk c j) d) (gτ p r s w c j)) ε
  Tcap : ∀ c j, c < 2 → j < 6 → ∀ d' E ε yE yO (t : ℤ), G 2 (rotN (gk c j) d') E ε →
    CapDom r s c yE → CapDom r s c yO → OnSide r s c j yE → OnSide r s c j yO →
    yO - yE ∈ unitVec → E = cross (rotN (gk c j) d') (gmap p r s w c j yE - t • per r s) →
    cross d' (yO - yE) = ε → (Inn1 r s c j (yE + d') ∨ Inn1 r s c j (yO + d')) →
    G c d' (cross d' yE) ε

section path

variable {n : ℕ} {q : ℕ → MS p r s}

/-- The invariant at index `i`. -/
def GoodAt (p r s w : ℤ) (G : ℕ → ℤ × ℤ → ℤ → ℤ → Prop) (q : ℕ → MS p r s) (i : ℕ) : Prop :=
  ∃ c a b e, Frame p r s w q i c a b e ∧
    G c (e - a) (cross (e - a) (ev i a b)) (cross (e - a) (od i a b - ev i a b))

theorem cross_self (d : ℤ × ℤ) : cross d d = 0 := by simp [cross]; ring

theorem cross_add' (d x y : ℤ × ℤ) : cross d (x + y) = cross d x + cross d y := by
  simp [cross]; ring

theorem cross_sub' (d x y : ℤ × ℤ) : cross d (x - y) = cross d x - cross d y := by
  simp [cross]; ring

/-- The even point of the next frame lies on the same line. -/
theorem ev_next (i : ℕ) (a b e : ℤ × ℤ) :
    cross (e - a) (ev (i + 1) b e) = cross (e - a) (ev i a b) ∧
      cross (e - a) (od (i + 1) b e - ev (i + 1) b e) =
        cross (e - a) (od i a b - ev i a b) := by
  simp only [ev, od]
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · have h' : (i + 1) % 2 = 1 := by omega
    simp only [h, h', ite_true, show (1 : ℕ) ≠ 0 by norm_num, ite_false, cross, Prod.fst_sub,
      Prod.snd_sub]
    try constructor
    all_goals first | trivial | ring
  · have h' : (i + 1) % 2 = 0 := by omega
    simp only [h, h', ite_true, show (1 : ℕ) ≠ 0 by norm_num, ite_false, cross, Prod.fst_sub,
      Prod.snd_sub]
    try constructor
    all_goals first | trivial | ring

/-- Exit points: the even and odd points among `b, e`. -/
theorem ev_od_next (i : ℕ) (b e : ℤ × ℤ) :
    (ev (i + 1) b e = b ∧ od (i + 1) b e = e) ∨ (ev (i + 1) b e = e ∧ od (i + 1) b e = b) := by
  simp only [ev, od]; split_ifs <;> simp

end path

end Claude5E10
