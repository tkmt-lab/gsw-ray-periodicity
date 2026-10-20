import Formal.Claude3GeoRows

/-!
# Theorem 1a, geometric foundation (3): the row lemma in all six directions

Written by a Claude worker (2026-10-20, Theorem 1a geometric session).

* `rotPre`, `mem_rot_iff` : `z ↦ rot z` pulls a chart back to a chart (the three normals
  are permuted with signs); `rotPreN`, `mem_rotN_iff` : the same for `rotN k`.
* `Pattern.rotN` : rotating a pattern walk gives a pattern walk.
* `row_lemma_rot` : the row lemma for direction `rotN k (1,0)`, with the exact index range given
  by the bounds of the pulled-back chart `rotPreN k (S.chart f)`.
* `unitTri_cover` : every oriented unit triangle `(a, b, c)` is the first triangle
  `(q_{i₀}, q_{i₀+1}, q_{i₀+2})` of a rotated row walk `rotN k ∘ rowPt h` with `k < 6`.
* `forced_walk_in_chart` : hence, under `Valid`, every forced walk started on a unit triangle of
  a chart is a rotated row walk for as long as that row walk stays in the chart.
-/

namespace ClaudeChallenge2.Geo

open ClaudeChallenge2

variable {S : Sig} {t : ℕ}

/-! ## Pulling charts back along rotations -/

/-- The negated affine function. -/
def negAff (A : Aff) : Aff := ⟨-A.a, -A.b⟩

@[simp] theorem negAff_eval (A : Aff) (t : ℕ) : (negAff A).eval t = -A.eval t := by
  simp only [negAff, Aff.eval]; ring

/-- The chart `{z | rot z ∈ c}`: `x' = -y`, `y' = x + y`, `x' + y' = x`. -/
def rotPre (c : Chart) : Chart where
  lx := c.ls
  ux := c.us
  ly := negAff c.ux
  uy := negAff c.lx
  ls := c.ly
  us := c.uy

theorem mem_rot_iff (c : Chart) (t : ℕ) (z : ℤ × ℤ) :
    c.Mem t (rot z) ↔ (rotPre c).Mem t z := by
  obtain ⟨x, y⟩ := z
  simp only [Chart.Mem, rot, rotPre, negAff_eval]
  constructor
  · intro H; omega
  · intro H; omega

/-- The chart `{z | rotN k z ∈ c}`. -/
def rotPreN : ℕ → Chart → Chart
  | 0, c => c
  | k + 1, c => rotPreN k (rotPre c)

theorem mem_rotN_iff (k : ℕ) (c : Chart) (t : ℕ) (z : ℤ × ℤ) :
    c.Mem t (rotN k z) ↔ (rotPreN k c).Mem t z := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih => rw [rotN, mem_rot_iff, ih]; rfl

theorem rotN_add_exp (m n : ℕ) (z : ℤ × ℤ) : rotN (m + n) z = rotN m (rotN n z) := by
  induction m with
  | zero => simp [rotN]
  | succ m ih => rw [Nat.add_right_comm, rotN, ih, rotN]

theorem rotN_rotN_inv {k : ℕ} (hk : k < 6) (z : ℤ × ℤ) : rotN k (rotN (6 - k) z) = z := by
  rw [← rotN_add_exp, show k + (6 - k) = 6 by omega, rotN_six]

/-! ## Rotated pattern walks -/

theorem Pattern.rotN {W : ℕ → ℤ × ℤ} (hW : Pattern W) (k : ℕ) :
    Pattern (fun m => ClaudeChallenge2.rotN k (W m)) where
  step1 m := by rw [← rotN_sub]; exact rotN_mem_unitVec k (hW.step1 m)
  step2 m := by rw [← rotN_sub]; exact rotN_mem_unitVec k (hW.step2 m)
  step3 m := fun e => hW.step3 m (rotN_injective k e)

theorem IsForced.mono {V : Type} {G : SimpleGraph V} {p : ℕ → V} {N N' : ℕ}
    (hp : IsForced G p N) (hN : N' ≤ N) : IsForced G p N' :=
  fun k hk => hp k (by omega)

/-- **Row lemma, direction `rotN k (1,0)`.** As `row_lemma`, for the rotated row walk
`rotN k (q_i)`; the hypotheses on `h` and on the index range are stated for the pulled-back chart
`c' = rotPreN k (S.chart f)`, whose six bounds are the original bounds permuted with signs. -/
theorem row_lemma_rot (hV : Valid S t) {f : Fin S.C} (k : ℕ) {h i₀ : ℤ} {N : ℕ} (hN : 3 ≤ N)
    (hh : (rotPreN k (S.chart f)).ly.eval t ≤ h ∧ h + 1 ≤ (rotPreN k (S.chart f)).uy.eval t)
    (hl : lo (rotPreN k (S.chart f)) t h ≤ i₀)
    (hu : i₀ + N - 3 ≤ hi (rotPreN k (S.chart f)) t h)
    {p : ℕ → Vertex S t} (hp : IsForced (graph S t) p N)
    (h0 : ∀ m : ℕ, m < 3 → ∃ hz, p m = pt S t f (rotN k (rowPt h (i₀ + m))) hz) :
    ∀ m : ℕ, m < N → ∃ hz, p m = pt S t f (rotN k (rowPt h (i₀ + m))) hz := by
  have hmem : ∀ m : ℕ, m < N → (S.chart f).Mem t (rotN k (rowPt h (i₀ + m))) := fun m hm =>
    (mem_rotN_iff k _ t _).2 ((rowWalk_mem_iff hN i₀).2 ⟨hh, hl, hu⟩ m hm)
  have key := forced_eq_pattern hV ((rowPt_pattern h i₀).rotN k) hmem hp (fun m hm h3 => by
    obtain ⟨hz, e⟩ := h0 m h3
    exact e)
  exact fun m hm => ⟨hmem m hm, key m hm⟩

/-! ## Every oriented unit triangle starts a rotated row walk -/

theorem dir_cover {u₁ u₂ : ℤ × ℤ} (h₁ : u₁ ∈ unitVec) (h₂ : u₂ ∈ unitVec)
    (h₃ : u₂ - u₁ ∈ unitVec) : ∃ k, k < 6 ∧
      ((u₁ = rotN k (0, 1) ∧ u₂ = rotN k (1, 0)) ∨
        (u₁ = rotN k (1, -1) ∧ u₂ = rotN k (1, 0))) := by
  rw [mem_unitVec_iff] at h₁ h₂
  rcases h₁ with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases h₂ with rfl | rfl | rfl | rfl | rfl | rfl <;>
  first
  | exact absurd h₃ (by decide)
  | exact ⟨0, by decide, by decide⟩
  | exact ⟨1, by decide, by decide⟩
  | exact ⟨2, by decide, by decide⟩
  | exact ⟨3, by decide, by decide⟩
  | exact ⟨4, by decide, by decide⟩
  | exact ⟨5, by decide, by decide⟩

/-- Every oriented unit triangle is the first triangle of a rotated row walk. -/
theorem unitTri_cover {a b c : ℤ × ℤ} (hab : b - a ∈ unitVec) (hac : c - a ∈ unitVec)
    (hbc : c - b ∈ unitVec) : ∃ k, k < 6 ∧ ∃ h i₀ : ℤ,
      a = rotN k (rowPt h i₀) ∧ b = rotN k (rowPt h (i₀ + 1)) ∧
        c = rotN k (rowPt h (i₀ + 2)) := by
  have h₃ : (c - a) - (b - a) ∈ unitVec := by simpa using hbc
  obtain ⟨k, hk, H⟩ := dir_cover hab hac h₃
  set w := rotN (6 - k) a with hw
  have ha : rotN k w = a := rotN_rotN_inv hk a
  refine ⟨k, hk, ?_⟩
  rcases H with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · refine ⟨w.2, 2 * w.1, ?_, ?_, ?_⟩
    · rw [rowPt_even, ha]
    · rw [show rowPt w.2 (2 * w.1 + 1) = w + (0, 1) by
          simp only [rowPt, Prod.ext_iff, Prod.fst_add, Prod.snd_add]; omega,
        rotN_add, ha, ← e₁]; abel
    · rw [show rowPt w.2 (2 * w.1 + 2) = w + (1, 0) by
          simp only [rowPt, Prod.ext_iff, Prod.fst_add, Prod.snd_add]; omega,
        rotN_add, ha, ← e₂]; abel
  · refine ⟨w.2 - 1, 2 * w.1 + 1, ?_, ?_, ?_⟩
    · rw [show rowPt (w.2 - 1) (2 * w.1 + 1) = w by
          simp only [rowPt, Prod.ext_iff]; omega, ha]
    · rw [show rowPt (w.2 - 1) (2 * w.1 + 1 + 1) = w + (1, -1) by
          simp only [rowPt, Prod.ext_iff, Prod.fst_add, Prod.snd_add]; omega,
        rotN_add, ha, ← e₁]; abel
    · rw [show rowPt (w.2 - 1) (2 * w.1 + 1 + 2) = w + (1, 0) by
          simp only [rowPt, Prod.ext_iff, Prod.fst_add, Prod.snd_add]; omega,
        rotN_add, ha, ← e₂]; abel

/-- **Forced walks inside a chart are rotated row walks.** Under `Valid`, a forced walk whose
first three vertices form a unit triangle `(a, b, c)` of chart `f` is, for some `k < 6`, `h`,
`i₀` (determined by the triangle alone), the rotated row walk `rotN k (q_{i₀+m})` for every
index `m` up to which that row walk stays in the chart. -/
theorem forced_walk_in_chart (hV : Valid S t) {f : Fin S.C} {a b c : ℤ × ℤ}
    (ha : (S.chart f).Mem t a) (hb : (S.chart f).Mem t b) (hc : (S.chart f).Mem t c)
    (hab : b - a ∈ unitVec) (hac : c - a ∈ unitVec) (hbc : c - b ∈ unitVec)
    {p : ℕ → Vertex S t} {N : ℕ} (hN : 3 ≤ N) (hp : IsForced (graph S t) p N)
    (h0 : p 0 = pt S t f a ha) (h1 : p 1 = pt S t f b hb) (h2 : p 2 = pt S t f c hc) :
    ∃ k, k < 6 ∧ ∃ h i₀ : ℤ,
      a = rotN k (rowPt h i₀) ∧ b = rotN k (rowPt h (i₀ + 1)) ∧
        c = rotN k (rowPt h (i₀ + 2)) ∧
      ∀ m : ℕ, m < N → (∀ m' : ℕ, m' ≤ m → (S.chart f).Mem t (rotN k (rowPt h (i₀ + m')))) →
        ∃ hz, p m = pt S t f (rotN k (rowPt h (i₀ + m))) hz := by
  obtain ⟨k, hk, h, i₀, ea, eb, ec⟩ := unitTri_cover hab hac hbc
  refine ⟨k, hk, h, i₀, ea, eb, ec, ?_⟩
  intro m hm hin
  -- the membership window: the first triangle together with the indices up to `m`
  have hmem : ∀ m' : ℕ, m' < max (m + 1) 3 →
      (S.chart f).Mem t (rotN k (rowPt h (i₀ + m'))) := by
    intro m' hm'
    by_cases hle : m' ≤ m
    · exact hin m' hle
    · rcases (show m' = 0 ∨ m' = 1 ∨ m' = 2 by omega) with rfl | rfl | rfl
      · simpa [← ea] using ha
      · simpa [← eb] using hb
      · simpa [← ec] using hc
  have key := forced_eq_pattern hV ((rowPt_pattern h i₀).rotN k) hmem
    (hp.mono (by omega)) (by
      intro m' hm' h3
      rcases (show m' = 0 ∨ m' = 1 ∨ m' = 2 by omega) with rfl | rfl | rfl
      · rw [h0]; exact pt_congr _ _ (by simpa using ea)
      · rw [h1]; exact pt_congr _ _ (by simpa using eb)
      · rw [h2]; exact pt_congr _ _ (by simpa using ec))
  exact ⟨hmem m (by omega), key m (by omega)⟩

end ClaudeChallenge2.Geo
