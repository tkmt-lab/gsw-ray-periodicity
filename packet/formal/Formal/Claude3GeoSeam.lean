import Formal.Claude3GeoDeg
import Formal.Claude3GeoPassage

/-!
# Theorem 1a, geometric foundation (7): seam transitions have identity linear part

Written by a Claude worker (2026-10-20, Theorem 1a geometric session).

* `recMap S t r z = rot^{j_r} z + d_r(t)` and `pt_recMap` : a record identifies a site with its
  image whenever both lie in their charts.
* `rotN_mod`, `rotN_rotN_inv'` : `rotN` has period 6; explicit inverse exponent.
* `rotN_aff` : rotations of integer-affine vectors are integer-affine.
* `recMap_rowPt` : (paper: "in direction-aligned coordinates the linear part of this transition
  is the identity") the image of the rotated row walk `rotN k (q_i)` under a record is the rotated
  row walk `rotN (j_r + k) (q'_{i + 2δ₁})` with `h' = h + δ₂`, where `δ = rot^{-(j_r+k)} d_r(t)`
  is integer-affine in `t` and independent of `h` and `i`.
* `seam_passage` : the forced walk crosses a seam glued by one record `r` (from chart `f` to
  chart `f'`): if the walk is the row walk `W` of `f` up to index `M`, the record images
  `Φ (W m)` lie in `f'` for `M-1 ≤ m ≤ M'`, and the apex `W (M-2)` of `f` is not identified with
  the apex `Φ (W (M+1))` of `f'` (**stated hypothesis**), then the walk equals `Φ ∘ W` on
  `[M-1, M']`, a rotated row walk of `f'` with row `h' = h + δ₂`;
  `seam_passage_overlap` : the same without the distinctness hypothesis when `Φ (W (M-2))` also
  lies in `f'`.
* `passage_injective` : the vertices of one passage are pairwise distinct.
-/

namespace ClaudeChallenge2.Geo

open ClaudeChallenge2

variable {S : Sig} {t : ℕ}

/-! ## Records -/

/-- The map of record `r`. -/
def recMap (S : Sig) (t : ℕ) (r : Fin S.R) (z : ℤ × ℤ) : ℤ × ℤ :=
  rotN (S.rotj r) z + ((S.dx r).eval t, (S.dy r).eval t)

/-- A record identifies a site with its image when both lie in their charts. -/
theorem pt_recMap {r : Fin S.R} {f f' : Fin S.C} (hf : S.src r = f) (hf' : S.tgt r = f')
    {z : ℤ × ℤ} (hz : (S.chart f).Mem t z) (hz' : (S.chart f').Mem t (recMap S t r z)) :
    pt S t f' (recMap S t r z) hz' = pt S t f z hz :=
  (Quot.sound (Relation.EqvGen.rel _ _ ⟨r, hf.symm, hf'.symm, rfl⟩)).symm

/-! ## Rotation arithmetic -/

theorem rotN_mod (n : ℕ) (z : ℤ × ℤ) : rotN n z = rotN (n % 6) z := by
  conv_lhs => rw [← Nat.mod_add_div n 6]
  rw [rotN_add_exp]
  congr 1
  induction n / 6 with
  | zero => rfl
  | succ q ih => rw [Nat.mul_succ, rotN_add_exp, rotN_six, ih]

/-- An explicit inverse of `rotN n`. -/
theorem rotN_rotN_inv' (n : ℕ) (z : ℤ × ℤ) : rotN n (rotN (6 - n % 6) z) = z := by
  rw [rotN_mod n, rotN_rotN_inv (Nat.mod_lt n (by norm_num))]

/-- Sum of affine functions. -/
def addAff (A B : Aff) : Aff := ⟨A.a + B.a, A.b + B.b⟩

@[simp] theorem addAff_eval (A B : Aff) (t : ℕ) : (addAff A B).eval t = A.eval t + B.eval t := by
  simp only [addAff, Aff.eval]; ring

/-- Rotations of integer-affine vectors are integer-affine. -/
theorem rotN_aff (m : ℕ) (A B : Aff) :
    ∃ A' B' : Aff, ∀ t : ℕ, rotN m (A.eval t, B.eval t) = (A'.eval t, B'.eval t) := by
  induction m with
  | zero => exact ⟨A, B, fun _ => rfl⟩
  | succ m ih =>
    obtain ⟨A', B', h⟩ := ih
    refine ⟨negAff B', addAff A' B', fun t => ?_⟩
    rw [rotN, h t]
    simp [rot]

/-- Translating a row walk by `d` is a row walk: `q_i + d = q'_{i + 2 d₁}` with `h' = h + d₂`. -/
theorem rowPt_add (h i : ℤ) (d : ℤ × ℤ) : rowPt h i + d = rowPt (h + d.2) (i + 2 * d.1) := by
  obtain ⟨d1, d2⟩ := d
  simp only [rowPt, Prod.mk_add_mk, Prod.mk.injEq]
  omega

/-- **Identity linear part.** The image of the rotated row walk `rotN k (q_i)` under record `r`
is the rotated row walk in direction `j_r + k`, with the same index shifted by `2δ₁` and the
row shifted by `δ₂`, where `δ` depends only on `r`, `k` and `t`. -/
theorem recMap_rowPt (r : Fin S.R) (k : ℕ) (h i : ℤ) :
    recMap S t r (rotN k (rowPt h i)) =
      rotN (S.rotj r + k) (rowPt (h + (rotN (6 - (S.rotj r + k) % 6)
        ((S.dx r).eval t, (S.dy r).eval t)).2)
        (i + 2 * (rotN (6 - (S.rotj r + k) % 6) ((S.dx r).eval t, (S.dy r).eval t)).1)) := by
  rw [← rowPt_add, rotN_add, rotN_rotN_inv', recMap, rotN_add_exp]

/-! ## Crossing a seam -/

theorem Pattern.shift {W : ℕ → ℤ × ℤ} (hW : Pattern W) (j : ℕ) :
    Pattern (fun m => W (j + m)) where
  step1 m := hW.step1 (j + m)
  step2 m := hW.step2 (j + m)
  step3 m := hW.step3 (j + m)

theorem Pattern.recMap {W : ℕ → ℤ × ℤ} (hW : Pattern W) (r : Fin S.R) :
    Pattern (fun m => Geo.recMap S t r (W m)) where
  step1 m := by
    simp only [Geo.recMap, add_sub_add_right_eq_sub, ← rotN_sub]
    exact rotN_mem_unitVec _ (hW.step1 m)
  step2 m := by
    simp only [Geo.recMap, add_sub_add_right_eq_sub, ← rotN_sub]
    exact rotN_mem_unitVec _ (hW.step2 m)
  step3 m := fun e => hW.step3 m (rotN_injective _ (add_right_cancel e))

/-- **Seam passage.** Under `Valid`, let a forced walk `p` follow the pattern walk `W` of chart
`f` at indices `M-2, M-1, M`, and let record `r` (from `f` to `f'`) carry `W m` into `f'` for
`M-1 ≤ m ≤ M'` (`M < M' < N`). If the apex `W (M-2)` (in `f`) and the apex `Φ (W (M+1))` (in
`f'`) are distinct vertices, then `p m` is the vertex of `Φ (W m)` in `f'` for
`M-1 ≤ m ≤ M'`. -/
theorem seam_passage (hV : Valid S t) {W : ℕ → ℤ × ℤ} (hW : Pattern W) {r : Fin S.R}
    {f f' : Fin S.C} (hf : S.src r = f) (hf' : S.tgt r = f') {p : ℕ → Vertex S t} {N M M' : ℕ}
    (hp : IsForced (graph S t) p N) (hM : 2 ≤ M) (hMM : M < M') (hMN : M' < N)
    (hW2 : (S.chart f).Mem t (W (M - 2))) (hW1 : (S.chart f).Mem t (W (M - 1)))
    (hW0 : (S.chart f).Mem t (W M))
    (e2 : p (M - 2) = pt S t f _ hW2) (e1 : p (M - 1) = pt S t f _ hW1)
    (e0 : p M = pt S t f _ hW0)
    (himg : ∀ m, M - 1 ≤ m → m ≤ M' → (S.chart f').Mem t (recMap S t r (W m)))
    (hne : pt S t f _ hW2 ≠ pt S t f' _ (himg (M + 1) (by omega) (by omega))) :
    ∀ m (hm1 : M - 1 ≤ m) (hm2 : m ≤ M'), p m = pt S t f' _ (himg m hm1 hm2) := by
  -- the continuation at index `M + 1`
  have hstep := hp (M - 2) (by omega)
  rw [show M - 2 + 1 = M - 1 by omega, show M - 2 + 2 = M by omega,
    show M - 2 + 3 = M + 1 by omega, e2, e1, e0] at hstep
  have u1 := hW.step1 (M - 1)
  have u2 := hW.step1 (M - 2)
  have u3 := hW.step2 (M - 2)
  have u4 := (hW.recMap (S := S) (t := t) r).step2 (M - 1)
  have u5 := (hW.recMap (S := S) (t := t) r).step1 M
  rw [show M - 1 + 1 = M by omega] at u1
  rw [show M - 2 + 1 = M - 1 by omega] at u2
  rw [show M - 2 + 2 = M by omega] at u3
  rw [show M - 1 + 2 = M + 1 by omega] at u4
  have eP := pt_recMap hf hf' hW1 (himg (M - 1) le_rfl (by omega))
  have eQ := pt_recMap hf hf' hW0 (himg M (by omega) (by omega))
  have hnext := (valid_seam_next_iff hV hW1 hW0 hW2 _ _ (himg (M + 1) (by omega) (by omega))
    u1 u2 u3 (by simpa using u4) u5 eP eQ hne _).1 hstep
  -- from index `M - 1` on, the shifted walk follows the image pattern
  let W' : ℕ → ℤ × ℤ := fun m => recMap S t r (W (M - 1 + m))
  have hW' : Pattern W' := (hW.shift (M - 1)).recMap r
  have hmem : ∀ m, m < M' - M + 2 → (S.chart f').Mem t (W' m) := fun m hm =>
    himg (M - 1 + m) (by omega) (by omega)
  have key := forced_eq_pattern hV hW' hmem
    ((hp.shift (M - 1)).mono (show M' - M + 2 ≤ N - (M - 1) by omega)) (by
      intro m hm h3
      rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl
      · rw [Nat.add_zero, e1, ← eP]
        exact pt_congr _ _ (by simp only [W', Nat.add_zero])
      · rw [show M - 1 + 1 = M by omega, e0, ← eQ]
        exact pt_congr _ _ (by simp only [W', show M - 1 + 1 = M by omega])
      · rw [show M - 1 + 2 = M + 1 by omega, hnext]
        exact pt_congr _ _ (by simp only [W', show M - 1 + 2 = M + 1 by omega]))
  intro m hm1 hm2
  have e : M - 1 + (m - (M - 1)) = m := by omega
  have := key (m - (M - 1)) (by omega)
  rw [e] at this
  rw [this]
  exact pt_congr _ _ (by simp only [W', e])

/-- **Seam passage, overlap case.** If the record image of the last *three* walk points lies in
`f'` (the target chart contains both apexes of the glued edge), no distinctness hypothesis is
needed: the walk is `Φ ∘ W` on `[M-2, M']`. -/
theorem seam_passage_overlap (hV : Valid S t) {W : ℕ → ℤ × ℤ} (hW : Pattern W) {r : Fin S.R}
    {f f' : Fin S.C} (hf : S.src r = f) (hf' : S.tgt r = f') {p : ℕ → Vertex S t} {N M M' : ℕ}
    (hp : IsForced (graph S t) p N) (hM : 2 ≤ M) (hMM : M ≤ M') (hMN : M' < N)
    (hW2 : (S.chart f).Mem t (W (M - 2))) (hW1 : (S.chart f).Mem t (W (M - 1)))
    (hW0 : (S.chart f).Mem t (W M))
    (e2 : p (M - 2) = pt S t f _ hW2) (e1 : p (M - 1) = pt S t f _ hW1)
    (e0 : p M = pt S t f _ hW0)
    (himg : ∀ m, M - 2 ≤ m → m ≤ M' → (S.chart f').Mem t (recMap S t r (W m))) :
    ∀ m (hm1 : M - 2 ≤ m) (hm2 : m ≤ M'), p m = pt S t f' _ (himg m hm1 hm2) := by
  let W' : ℕ → ℤ × ℤ := fun m => recMap S t r (W (M - 2 + m))
  have hW' : Pattern W' := (hW.shift (M - 2)).recMap r
  have hmem : ∀ m, m < M' - M + 3 → (S.chart f').Mem t (W' m) := fun m hm =>
    himg (M - 2 + m) (by omega) (by omega)
  have key := forced_eq_pattern hV hW' hmem
    ((hp.shift (M - 2)).mono (show M' - M + 3 ≤ N - (M - 2) by omega)) (by
      intro m hm h3
      rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl
      · rw [Nat.add_zero, e2, ← pt_recMap hf hf' hW2 (himg (M - 2) le_rfl (by omega))]
        exact pt_congr _ _ (by simp only [W', Nat.add_zero])
      · rw [show M - 2 + 1 = M - 1 by omega, e1,
          ← pt_recMap hf hf' hW1 (himg (M - 1) (by omega) (by omega))]
        exact pt_congr _ _ (by simp only [W', show M - 2 + 1 = M - 1 by omega])
      · rw [show M - 2 + 2 = M by omega, e0,
          ← pt_recMap hf hf' hW0 (himg M (by omega) (by omega))]
        exact pt_congr _ _ (by simp only [W', show M - 2 + 2 = M by omega]))
  intro m hm1 hm2
  have e : M - 2 + (m - (M - 2)) = m := by omega
  have := key (m - (M - 2)) (by omega)
  rw [e] at this
  rw [this]
  exact pt_congr _ _ (by simp only [W', e])

/-- Inside one passage the vertices are pairwise distinct (embedded charts, injective rows). -/
theorem passage_injective (hV : Valid S t) {f : Fin S.C} (k : ℕ) (h i₀ : ℤ) {m m' : ℕ}
    (hz : (S.chart f).Mem t (rotN k (rowPt h (i₀ + m))))
    (hz' : (S.chart f).Mem t (rotN k (rowPt h (i₀ + m'))))
    (e : pt S t f _ hz = pt S t f _ hz') : m = m' := by
  have := rowPt_injective h (rotN_injective k (valid_pt_inj hV hz hz' e))
  omega

end ClaudeChallenge2.Geo
