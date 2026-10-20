import Formal.Claude3GeoQuot
import Formal.Claude3GeoSeam

/-!
# Theorem 1a, geometric foundation (8): identifications in normal form

Written by a Claude worker (2026-10-20, Theorem 1a geometric session).

Combining `vtx_eq_iff_stepN` with explicit record maps gives a `t`-uniform normal form of the
quotient: two chart points are the same vertex iff, for one of finitely many words `w` of
fewer than `C` signed records (data independent of `t`),

* the chart sequence of `w` runs from the first chart to the second (`WordOK`),
* the first point lies in each of finitely many fixed charts `wordCharts S w f`
  (the pulled-back charts of the intermediate sites; integer-affine bounds), and
* the second point is `rotN J z + (A t, B t)` for the fixed affine map `wordAff S w`.

So each identification is a fixed finite disjunction of conjunctions of the chart inequalities
`L ≤ x`, `y`, `x + y ≤ U` (integer-affine `L, U`) of the first point, plus one affine equation.

* `AffMap`, `AffMap.apply`, `AffMap.comp`, `apply_comp` : rotations plus affine translations.
* `pullChart`, `mem_pullChart` : pulling a chart back along an `AffMap` gives a chart.
* `letterAff`, `letterMap_eq`, `step_iff_letter` : one record step, forwards or backwards.
* `chainOK_iff`, `stepN_iff_chain`, `vtx_eq_iff_word` : the normal form.
-/

namespace ClaudeChallenge2.Geo

open ClaudeChallenge2

variable {S : Sig} {t : ℕ}

/-! ## Affine maps with rotation -/

/-- The zero affine function. -/
def zeroAff : Aff := ⟨0, 0⟩

@[simp] theorem zeroAff_eval (t : ℕ) : zeroAff.eval t = 0 := by simp [zeroAff, Aff.eval]

/-- Difference of affine functions. -/
def subAff (A B : Aff) : Aff := ⟨A.a - B.a, A.b - B.b⟩

@[simp] theorem subAff_eval (A B : Aff) (t : ℕ) : (subAff A B).eval t = A.eval t - B.eval t := by
  simp only [subAff, Aff.eval]; ring

/-- `rotN n` on pairs of affine functions. -/
def rotAff : ℕ → Aff × Aff → Aff × Aff
  | 0, p => p
  | n + 1, p => (negAff (rotAff n p).2, addAff (rotAff n p).1 (rotAff n p).2)

theorem rotN_affPair (n : ℕ) (p : Aff × Aff) (t : ℕ) :
    rotN n (p.1.eval t, p.2.eval t) = ((rotAff n p).1.eval t, (rotAff n p).2.eval t) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rotN, ih, rot, rotAff]

/-- `z ↦ rotN J z + (A t, B t)`. -/
structure AffMap where
  J : ℕ
  A : Aff
  B : Aff

def AffMap.apply (φ : AffMap) (t : ℕ) (z : ℤ × ℤ) : ℤ × ℤ :=
  rotN φ.J z + (φ.A.eval t, φ.B.eval t)

def AffMap.id : AffMap := ⟨0, zeroAff, zeroAff⟩

@[simp] theorem AffMap.apply_id (t : ℕ) (z : ℤ × ℤ) : AffMap.id.apply t z = z := by
  simp [AffMap.apply, AffMap.id, rotN]

/-- Composition `ψ ∘ φ`. -/
def AffMap.comp (ψ φ : AffMap) : AffMap :=
  ⟨ψ.J + φ.J, addAff (rotAff ψ.J (φ.A, φ.B)).1 ψ.A, addAff (rotAff ψ.J (φ.A, φ.B)).2 ψ.B⟩

theorem AffMap.apply_comp (ψ φ : AffMap) (t : ℕ) (z : ℤ × ℤ) :
    (ψ.comp φ).apply t z = ψ.apply t (φ.apply t z) := by
  simp only [AffMap.apply, AffMap.comp, rotN_add, rotN_add_exp]
  have := rotN_affPair ψ.J (φ.A, φ.B) t
  simp only at this
  rw [this]
  ext <;> simp <;> ring

/-! ## Pulling charts back -/

/-- The chart `{z | z + (A t, B t) ∈ c}`. -/
def transChart (c : Chart) (A B : Aff) : Chart where
  lx := subAff c.lx A
  ux := subAff c.ux A
  ly := subAff c.ly B
  uy := subAff c.uy B
  ls := subAff (subAff c.ls A) B
  us := subAff (subAff c.us A) B

theorem mem_transChart (c : Chart) (A B : Aff) (t : ℕ) (z : ℤ × ℤ) :
    c.Mem t (z + (A.eval t, B.eval t)) ↔ (transChart c A B).Mem t z := by
  obtain ⟨x, y⟩ := z
  simp only [Chart.Mem, transChart, subAff_eval, Prod.mk_add_mk]
  constructor
  · intro H; omega
  · intro H; omega

/-- The chart `{z | φ z ∈ c}`. -/
def pullChart (c : Chart) (φ : AffMap) : Chart := rotPreN φ.J (transChart c φ.A φ.B)

theorem mem_pullChart (c : Chart) (φ : AffMap) (t : ℕ) (z : ℤ × ℤ) :
    c.Mem t (φ.apply t z) ↔ (pullChart c φ).Mem t z := by
  rw [AffMap.apply, mem_transChart, mem_rotN_iff]; rfl

/-! ## Signed record letters -/

/-- A record used forwards (`true`, from `src` to `tgt`) or backwards (`false`). -/
abbrev Letter (S : Sig) : Type := Fin S.R × Bool

def letterSrc (S : Sig) : Letter S → Fin S.C
  | (r, true) => S.src r
  | (r, false) => S.tgt r

def letterTgt (S : Sig) : Letter S → Fin S.C
  | (r, true) => S.tgt r
  | (r, false) => S.src r

/-- The affine map of a letter (independent of `t`). -/
def letterAff (S : Sig) : Letter S → AffMap
  | (r, true) => ⟨S.rotj r, S.dx r, S.dy r⟩
  | (r, false) =>
    ⟨6 - S.rotj r % 6, (rotAff (6 - S.rotj r % 6) (negAff (S.dx r), negAff (S.dy r))).1,
      (rotAff (6 - S.rotj r % 6) (negAff (S.dx r), negAff (S.dy r))).2⟩

theorem rotN_inv_rotN (n : ℕ) (z : ℤ × ℤ) : rotN (6 - n % 6) (rotN n z) = z := by
  rw [← rotN_add_exp, rotN_mod, show (6 - n % 6 + n) % 6 = 0 by omega]; rfl

/-- The backward map undoes the forward map. -/
theorem letterAff_false_apply (r : Fin S.R) (t : ℕ) (z : ℤ × ℤ) :
    (letterAff S (r, false)).apply t z = rotN (6 - S.rotj r % 6) (z - ((S.dx r).eval t,
      (S.dy r).eval t)) := by
  have := rotN_affPair (6 - S.rotj r % 6) (negAff (S.dx r), negAff (S.dy r)) t
  simp only [negAff_eval] at this
  simp only [AffMap.apply, letterAff, ← this, sub_eq_add_neg, rotN_add, Prod.neg_mk]

theorem recMap_letter_false (r : Fin S.R) (t : ℕ) (z : ℤ × ℤ) :
    recMap S t r ((letterAff S (r, false)).apply t z) = z := by
  rw [letterAff_false_apply, recMap, rotN_rotN_inv', sub_add_cancel]

theorem letter_false_recMap (r : Fin S.R) (t : ℕ) (z : ℤ × ℤ) :
    (letterAff S (r, false)).apply t (recMap S t r z) = z := by
  rw [letterAff_false_apply, recMap, add_sub_cancel_right, rotN_inv_rotN]

/-- One record step in letter form. -/
theorem step_iff_letter (s s' : Site S t) :
    Step S t s s' ↔ ∃ l : Letter S, s.1.1 = letterSrc S l ∧ s'.1.1 = letterTgt S l ∧
      s'.1.2 = (letterAff S l).apply t s.1.2 := by
  constructor
  · rintro (⟨r, h1, h2, h3⟩ | ⟨r, h1, h2, h3⟩)
    · exact ⟨(r, true), h1, h2, h3.symm⟩
    · refine ⟨(r, false), h2, h1, ?_⟩
      rw [← h3]
      exact (letter_false_recMap r t s'.1.2).symm
  · rintro ⟨⟨r, b⟩, h1, h2, h3⟩
    cases b with
    | true => exact Or.inl ⟨r, h1, h2, h3.symm⟩
    | false =>
      refine Or.inr ⟨r, h2, h1, ?_⟩
      rw [h3]
      exact recMap_letter_false r t s.1.2

/-! ## Words -/

/-- Chains along a word, starting at chart `f` and point `z`, ending at `f'`, `z'`, with every
intermediate point in its chart. -/
def ChainOK (S : Sig) (t : ℕ) : List (Letter S) → Fin S.C → ℤ × ℤ → Fin S.C → ℤ × ℤ → Prop
  | [], f, z, f', z' => f = f' ∧ z = z' ∧ (S.chart f).Mem t z
  | l :: w, f, z, f', z' => f = letterSrc S l ∧ (S.chart f).Mem t z ∧
      ChainOK S t w (letterTgt S l) ((letterAff S l).apply t z) f' z'

/-- The chart sequence of a word runs from `f` to `f'`. -/
def WordOK (S : Sig) : List (Letter S) → Fin S.C → Fin S.C → Prop
  | [], f, f' => f = f'
  | l :: w, f, f' => f = letterSrc S l ∧ WordOK S w (letterTgt S l) f'

/-- The composite affine map of a word. -/
def wordAff (S : Sig) : List (Letter S) → AffMap
  | [] => AffMap.id
  | l :: w => (wordAff S w).comp (letterAff S l)

/-- The intermediate charts of a word, pulled back to the coordinates of the first point. -/
def wordCharts (S : Sig) : List (Letter S) → Fin S.C → List Chart
  | [], f => [S.chart f]
  | l :: w, f => S.chart f :: (wordCharts S w (letterTgt S l)).map (pullChart · (letterAff S l))

theorem chainOK_iff (w : List (Letter S)) (f : Fin S.C) (z : ℤ × ℤ) (f' : Fin S.C)
    (z' : ℤ × ℤ) :
    ChainOK S t w f z f' z' ↔ WordOK S w f f' ∧ (∀ c ∈ wordCharts S w f, c.Mem t z) ∧
      z' = (wordAff S w).apply t z := by
  induction w generalizing f z with
  | nil =>
    simp only [ChainOK, WordOK, wordCharts, List.mem_singleton, forall_eq, wordAff,
      AffMap.apply_id]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, h2.symm⟩
    · rintro ⟨h1, h3, h2⟩; exact ⟨h1, h2.symm, h3⟩
  | cons l w ih =>
    simp only [ChainOK, WordOK, wordCharts, List.mem_cons, List.mem_map, wordAff, ih,
      AffMap.apply_comp]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨⟨h1, h3⟩, ?_, h5⟩
      rintro c (rfl | ⟨c', hc', rfl⟩)
      · exact h2
      · exact (mem_pullChart _ _ _ _).1 (h4 c' hc')
    · rintro ⟨⟨h1, h3⟩, h4, h5⟩
      refine ⟨h1, h4 _ (Or.inl rfl), h3, fun c hc => ?_, h5⟩
      exact (mem_pullChart _ _ _ _).2 (h4 _ (Or.inr ⟨c, hc, rfl⟩))

theorem chainOK_mem : ∀ {w : List (Letter S)} {f : Fin S.C} {z : ℤ × ℤ} {f' : Fin S.C}
    {z' : ℤ × ℤ}, ChainOK S t w f z f' z' → (S.chart f).Mem t z
  | [], _, _, _, _, h => h.2.2
  | _ :: _, _, _, _, _, h => h.2.1

theorem stepN_iff_chain (n : ℕ) (s s' : Site S t) :
    StepN S t n s s' ↔ ∃ w : List (Letter S), w.length = n ∧
      ChainOK S t w s.1.1 s.1.2 s'.1.1 s'.1.2 := by
  induction n generalizing s with
  | zero =>
    simp only [StepN, List.length_eq_zero_iff, exists_eq_left, ChainOK]
    constructor
    · rintro rfl; exact ⟨rfl, rfl, s.2⟩
    · rintro ⟨h1, h2, -⟩
      exact Subtype.ext (Prod.ext h1 h2)
  | succ n ih =>
    simp only [StepN]
    constructor
    · rintro ⟨s1, hs, hn⟩
      obtain ⟨l, h1, h2, h3⟩ := (step_iff_letter s s1).1 hs
      obtain ⟨w, hw, hc⟩ := (ih s1).1 hn
      refine ⟨l :: w, by simp [hw], h1, s.2, ?_⟩
      rw [← h2, ← h3]
      exact hc
    · rintro ⟨_ | ⟨l, w⟩, hw, hc⟩
      · simp at hw
      · obtain ⟨h1, -, h3⟩ := hc
        let s1 : Site S t := ⟨(letterTgt S l, (letterAff S l).apply t s.1.2), chainOK_mem h3⟩
        refine ⟨s1, (step_iff_letter s s1).2 ⟨l, h1, rfl, rfl⟩, (ih s1).2 ⟨w, ?_, h3⟩⟩
        simpa using hw

/-- **Normal form of identifications.** Under chart-embeddedness, two chart points are the
same vertex iff some word of fewer than `C` signed records has the right chart sequence, the
first point lies in all of its (fixed, pulled-back) charts, and the second point is the image
of the first under its (fixed) affine map. -/
theorem vtx_eq_iff_word (hE : Embedded S t) {f f' : Fin S.C} {z z' : ℤ × ℤ}
    (h : (S.chart f).Mem t z) (h' : (S.chart f').Mem t z') :
    pt S t f z h = pt S t f' z' h' ↔ ∃ w : List (Letter S), w.length < S.C ∧ WordOK S w f f' ∧
      (∀ c ∈ wordCharts S w f, c.Mem t z) ∧ z' = (wordAff S w).apply t z := by
  rw [vtx_eq_iff_stepN hE]
  constructor
  · rintro ⟨n, hn, hs⟩
    obtain ⟨w, rfl, hc⟩ := (stepN_iff_chain _ _ _).1 hs
    exact ⟨w, hn, (chainOK_iff _ _ _ _ _).1 hc⟩
  · rintro ⟨w, hn, hc⟩
    exact ⟨w.length, hn, (stepN_iff_chain _ _ _).2 ⟨w, rfl, (chainOK_iff _ _ _ _ _).2 hc⟩⟩

end ClaudeChallenge2.Geo
