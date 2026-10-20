import Formal.Claude3IdentNrm

/-!
# Theorem 1a, G3b (2): identification of row points is restricted arithmetic

Written by a Claude worker (2026-10-20, Theorem 1a, part G3b).

Generic row descriptors (no dependence on the state types of G4/G5):

* `RowSet S` : a chart `f`, an affine embedding `emb : AffMap` (`z = rotN J (x, h) + D(t)`)
  and finitely many normal constraints `cons` on the aligned coordinates `(x, h)`.
  The points of the row at height `h` are `emb (x, h)` for the positions `x` satisfying
  `cons` (`RowSet.At`). An interval of positions `σ h + c(t) ≤ x ≤ σ' h + c'(t)` with
  `σ, σ' ∈ {-1, 0}` is a normal constraint list (`intervalRow`, `boundNCs`); a single position
  `x = σ h + c(t)` is the interval with equal ends (`affineRow`).
* `Meet S t R₁ h₁ R₂ h₂` : some point of `R₁` at height `h₁` and some point of `R₂` at height
  `h₂` are sites of their charts and the same vertex.

Main results.

* `ident_iff_word` : under `Embedded`, `∃ sites, pt z = pt z'` iff a short record word
  (charts and affine equation, data independent of `t`).
* **`meet_iff_patoms`** : under `Embedded`, `Meet S t R₁ h₁ R₂ h₂` iff for some word `w` of
  fewer than `C` signed records with `WordOK S w R₂.f R₁.f`, all pairwise atoms of the fixed list
  `meetPA R₁ R₂ w` hold at `(h₁, h₂)`; **`meetPA_ok`** : these atoms have coefficients in
  `{-1, 0, 1}` (no `2 h₁ + h₂`).
* **`sat_meetHF`** : an explicit formula `meetHF R₁ R₂ x y : HF T m k` (restricted arithmetic of
  `R002.Claude3Fold`) with free state variables `x, y` such that
  `HF.Sat lo hi t (meetHF R₁ R₂ x y) ν V ↔ Meet S t R₁ (ν x).2 R₂ (ν y).2`, for every `t` with
  `Embedded S t` and every `lo hi ν V`.
* `sat_meetHF1` : the same with one free variable, the first row at height `0`
  (used for fixed points such as marked corners: `constRow`).

Why `σ = +1` is excluded: the endpoints of the row intervals are `Aₑ = max(L_x, L_s - h)`,
`Bₑ = min(U_x - 1, U_s - h - 1)` etc., so only `σ ∈ {-1, 0}` occurs; `x - h` is not a lattice
normal, and with it the substitution step could produce coefficient `2`.
-/

namespace ClaudeChallenge2.Geo

open ClaudeChallenge2

variable {S : Sig} {t : ℕ}

/-! ## Words of bounded length -/

/-- All signed letters. -/
def allLetters (S : Sig) : List (Letter S) :=
  (List.finRange S.R).flatMap fun r => [(r, true), (r, false)]

theorem mem_allLetters (l : Letter S) : l ∈ allLetters S := by
  obtain ⟨r, b⟩ := l
  simp only [allLetters, List.mem_flatMap, List.mem_finRange, List.mem_cons, List.not_mem_nil,
    or_false, true_and]
  exact ⟨r, by cases b <;> simp⟩

/-- All words of length `n`. -/
def wordsLen (S : Sig) : ℕ → List (List (Letter S))
  | 0 => [[]]
  | n + 1 => (wordsLen S n).flatMap fun w => (allLetters S).map (· :: w)

theorem mem_wordsLen (n : ℕ) (w : List (Letter S)) : w ∈ wordsLen S n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [wordsLen]
  | succ n ih =>
    simp only [wordsLen, List.mem_flatMap, List.mem_map, ih]
    constructor
    · rintro ⟨w', hw', l, -, rfl⟩; simp [hw']
    · intro hw
      obtain ⟨l, w', rfl⟩ : ∃ l w', w = l :: w' := by
        cases w with
        | nil => simp at hw
        | cons l w' => exact ⟨l, w', rfl⟩
      exact ⟨w', by simpa using hw, l, mem_allLetters l, rfl⟩

/-- All words of length `< n`. -/
def wordsLT (S : Sig) (n : ℕ) : List (List (Letter S)) := (List.range n).flatMap (wordsLen S)

theorem mem_wordsLT (n : ℕ) (w : List (Letter S)) : w ∈ wordsLT S n ↔ w.length < n := by
  simp [wordsLT, mem_wordsLen]

instance wordOKDec : (w : List (Letter S)) → (f f' : Fin S.C) → Decidable (WordOK S w f f')
  | [], f, f' => inferInstanceAs (Decidable (f = f'))
  | l :: w, f, f' =>
    haveI := wordOKDec w (letterTgt S l) f'
    inferInstanceAs (Decidable (f = letterSrc S l ∧ WordOK S w (letterTgt S l) f'))

/-! ## Identification of two chart points -/

theorem chainOK_end : ∀ {w : List (Letter S)} {f : Fin S.C} {z : ℤ × ℤ} {f' : Fin S.C}
    {z' : ℤ × ℤ}, ChainOK S t w f z f' z' → (S.chart f').Mem t z'
  | [], _, _, _, _, h => by obtain ⟨rfl, rfl, h⟩ := h; exact h
  | _ :: _, _, _, _, _, h => chainOK_end h.2.2

/-- Under embeddedness, two plane points are sites of `f`, `f'` with the same vertex iff a word
of fewer than `C` records carries the first to the second. -/
theorem ident_iff_word (hE : Embedded S t) (f f' : Fin S.C) (z z' : ℤ × ℤ) :
    (∃ (hz : (S.chart f).Mem t z) (hz' : (S.chart f').Mem t z'), pt S t f z hz = pt S t f' z' hz')
      ↔ ∃ w : List (Letter S), w.length < S.C ∧ WordOK S w f f' ∧
        (∀ c ∈ wordCharts S w f, c.Mem t z) ∧ z' = (wordAff S w).apply t z := by
  constructor
  · rintro ⟨hz, hz', e⟩
    exact (vtx_eq_iff_word hE hz hz').1 e
  · rintro ⟨w, hw, hok, hc, he⟩
    have hch := (chainOK_iff (t := t) w f z f' z').2 ⟨hok, hc, he⟩
    exact ⟨chainOK_mem hch, chainOK_end hch,
      (vtx_eq_iff_word hE (chainOK_mem hch) (chainOK_end hch)).2 ⟨w, hw, hok, hc, he⟩⟩

/-! ## Row descriptors -/

/-- A generic row: chart `f`, embedding `emb` of the aligned coordinates `(x, h)`, and normal
constraints on `(x, h)`. -/
structure RowSet (S : Sig) where
  f : Fin S.C
  emb : AffMap
  cons : List NC

/-- All constraints are signed lattice normals. -/
def RowSet.WF (R : RowSet S) : Prop := ∀ c ∈ R.cons, c.Nrm

/-- `z` is a point of the row `R` at height `h`. -/
def RowSet.At (R : RowSet S) (t : ℕ) (h : ℤ) (z : ℤ × ℤ) : Prop :=
  ∃ x : ℤ, (∀ c ∈ R.cons, c.Sat t (x, h)) ∧ z = R.emb.apply t (x, h)

/-- Some point of `R₁` at height `h₁` and some point of `R₂` at height `h₂` are sites of their
charts with the same vertex. -/
def Meet (S : Sig) (t : ℕ) (R₁ : RowSet S) (h₁ : ℤ) (R₂ : RowSet S) (h₂ : ℤ) : Prop :=
  ∃ z₁ z₂ : ℤ × ℤ, R₁.At t h₁ z₁ ∧ R₂.At t h₂ z₂ ∧
    ∃ (hz₁ : (S.chart R₁.f).Mem t z₁) (hz₂ : (S.chart R₂.f).Mem t z₂),
      pt S t R₁.f z₁ hz₁ = pt S t R₂.f z₂ hz₂

/-- A position bound `σ h + c(t)`. -/
structure Bnd where
  σ : ℤ
  c : Aff

/-- `σ ∈ {-1, 0}` (the endpoint forms of the row lemma). -/
def Bnd.WF (b : Bnd) : Prop := b.σ = 0 ∨ b.σ = -1

/-- `x ≥ σ h + c` and `x ≤ σ h + c` as normal constraints. -/
def Bnd.lowNC (b : Bnd) : NC := ⟨-1, b.σ, negAff b.c⟩
def Bnd.upNC (b : Bnd) : NC := ⟨1, -b.σ, b.c⟩

/-- The constraints of lower bounds `lows` and upper bounds `ups`. -/
def boundNCs (lows ups : List Bnd) : List NC := lows.map Bnd.lowNC ++ ups.map Bnd.upNC

theorem sat_boundNCs (lows ups : List Bnd) (t : ℕ) (x h : ℤ) :
    (∀ c ∈ boundNCs lows ups, c.Sat t (x, h)) ↔
      (∀ b ∈ lows, b.σ * h + b.c.eval t ≤ x) ∧ ∀ b ∈ ups, x ≤ b.σ * h + b.c.eval t := by
  simp only [boundNCs, List.mem_append, or_imp, forall_and, List.forall_mem_map]
  refine and_congr (forall₂_congr fun b _ => ?_) (forall₂_congr fun b _ => ?_) <;>
    simp only [NC.Sat, Bnd.lowNC, Bnd.upNC, negAff_eval] <;> constructor <;> intro h <;> linarith

theorem boundNCs_nrm {lows ups : List Bnd} (hl : ∀ b ∈ lows, b.WF) (hu : ∀ b ∈ ups, b.WF) :
    ∀ c ∈ boundNCs lows ups, c.Nrm := by
  simp only [boundNCs, List.mem_append, or_imp, forall_and, List.forall_mem_map]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · rcases hl b hb with h | h <;> simp [Bnd.lowNC, NC.Nrm, h]
  · rcases hu b hb with h | h <;> simp [Bnd.upNC, NC.Nrm, h]

/-- The row `rotN k (x, h) + (Dx t, Dy t)` of chart `f`, positions between the bounds. -/
def intervalRow (f : Fin S.C) (k : ℕ) (Dx Dy : Aff) (lows ups : List Bnd) : RowSet S :=
  ⟨f, ⟨k, Dx, Dy⟩, boundNCs lows ups⟩

theorem intervalRow_at (f : Fin S.C) (k : ℕ) (Dx Dy : Aff) (lows ups : List Bnd) (h : ℤ)
    (z : ℤ × ℤ) :
    (intervalRow f k Dx Dy lows ups).At t h z ↔ ∃ x : ℤ, ((∀ b ∈ lows, b.σ * h + b.c.eval t ≤ x) ∧
      ∀ b ∈ ups, x ≤ b.σ * h + b.c.eval t) ∧ z = rotN k (x, h) + (Dx.eval t, Dy.eval t) := by
  simp only [RowSet.At, intervalRow, sat_boundNCs, AffMap.apply]

theorem intervalRow_wf (f : Fin S.C) (k : ℕ) (Dx Dy : Aff) {lows ups : List Bnd}
    (hl : ∀ b ∈ lows, b.WF) (hu : ∀ b ∈ ups, b.WF) : (intervalRow f k Dx Dy lows ups).WF :=
  boundNCs_nrm hl hu

/-- The single point `rotN k (σ h + c(t), h) + (Dx t, Dy t)` of chart `f`. -/
def affineRow (f : Fin S.C) (k : ℕ) (Dx Dy : Aff) (b : Bnd) : RowSet S :=
  intervalRow f k Dx Dy [b] [b]

theorem affineRow_at (f : Fin S.C) (k : ℕ) (Dx Dy : Aff) (b : Bnd) (h : ℤ) (z : ℤ × ℤ) :
    (affineRow f k Dx Dy b).At t h z ↔
      z = rotN k (b.σ * h + b.c.eval t, h) + (Dx.eval t, Dy.eval t) := by
  simp only [affineRow, intervalRow_at, List.mem_singleton, forall_eq]
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    rw [le_antisymm h2 h1]
  · rintro rfl
    exact ⟨_, ⟨le_refl _, le_refl _⟩, rfl⟩

theorem affineRow_wf (f : Fin S.C) (k : ℕ) (Dx Dy : Aff) {b : Bnd} (hb : b.WF) :
    (affineRow f k Dx Dy b).WF :=
  intervalRow_wf f k Dx Dy (by simpa using hb) (by simpa using hb)

/-- The fixed point `(cx t, cy t)` of chart `f`, as a row at height `0` (position `0`). -/
def constRow (f : Fin S.C) (cx cy : Aff) : RowSet S :=
  ⟨f, ⟨0, cx, cy⟩, [⟨1, 0, zeroAff⟩, ⟨-1, 0, zeroAff⟩]⟩

theorem constRow_at (f : Fin S.C) (cx cy : Aff) (z : ℤ × ℤ) :
    (constRow f cx cy).At t 0 z ↔ z = (cx.eval t, cy.eval t) := by
  simp only [RowSet.At, constRow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, NC.Sat, zeroAff_eval, AffMap.apply, rotN]
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    have : x = 0 := by linarith
    subst this; simp
  · rintro rfl
    exact ⟨0, ⟨by simp, by simp⟩, by simp⟩

theorem constRow_wf (f : Fin S.C) (cx cy : Aff) : (constRow (S := S) f cx cy).WF := by
  simp [RowSet.WF, constRow, NC.Nrm]

/-! ## The atoms of an identification -/

/-- The aligned coordinates of `R₁` as an affine function of those of `R₂`, along word `w`. -/
def psiMap (R₁ R₂ : RowSet S) (w : List (Letter S)) : AffMap :=
  R₁.emb.inv.comp ((wordAff S w).comp R₂.emb)

/-- All constraints on the aligned coordinates `(X, h₂)` of `R₂`. -/
def allNC (R₁ R₂ : RowSet S) (w : List (Letter S)) : List NC :=
  R₂.cons ++ (wordCharts S w R₂.f).flatMap (pullNCs · R₂.emb) ++
    R₁.cons.map (NC.pull · (psiMap R₁ R₂ w))

/-- The pairwise atoms of the identification along `w`. -/
def meetPA (R₁ R₂ : RowSet S) (w : List (Letter S)) : List PA :=
  elim (rowCoef (psiMap R₁ R₂ w).J) (psiMap R₁ R₂ w).B (allNC R₁ R₂ w)

theorem allNC_nrm {R₁ R₂ : RowSet S} (h₁ : R₁.WF) (h₂ : R₂.WF) (w : List (Letter S)) :
    ∀ c ∈ allNC R₁ R₂ w, c.Nrm := by
  simp only [allNC, List.mem_append, List.mem_flatMap, List.mem_map]
  rintro c ((hc | ⟨ch, -, hc⟩) | ⟨c', hc', rfl⟩)
  · exact h₂ c hc
  · exact pullNCs_nrm ch _ c hc
  · exact NC.nrm_pull (h₁ c' hc') _

/-- **No coefficient `2`.** -/
theorem meetPA_ok {R₁ R₂ : RowSet S} (h₁ : R₁.WF) (h₂ : R₂.WF) (w : List (Letter S)) :
    ∀ a ∈ meetPA R₁ R₂ w, a.OK :=
  elim_ok _ (rowCoef_ok _) _ _ (allNC_nrm h₁ h₂ w)

theorem psiMap_snd (R₁ R₂ : RowSet S) (w : List (Letter S)) (t : ℕ) (X H : ℤ) :
    ((psiMap R₁ R₂ w).apply t (X, H)).2 =
      (rowCoef (psiMap R₁ R₂ w).J).1 * X + (rowCoef (psiMap R₁ R₂ w).J).2 * H +
        (psiMap R₁ R₂ w).B.eval t := by
  simp only [AffMap.apply, Prod.snd_add, rotN_snd]

/-- One word: the existence of positions is the existence of `X` under all constraints with
`h₁` affine in `(X, h₂)`. -/
theorem word_inner_iff (R₁ R₂ : RowSet S) (w : List (Letter S)) (t : ℕ) (h₁ h₂ : ℤ) :
    (∃ x₁ X : ℤ, (∀ c ∈ R₁.cons, c.Sat t (x₁, h₁)) ∧ (∀ c ∈ R₂.cons, c.Sat t (X, h₂)) ∧
      (∀ c ∈ wordCharts S w R₂.f, c.Mem t (R₂.emb.apply t (X, h₂))) ∧
      R₁.emb.apply t (x₁, h₁) = (wordAff S w).apply t (R₂.emb.apply t (X, h₂))) ↔
    ∃ X : ℤ, (∀ c ∈ allNC R₁ R₂ w, c.Sat t (X, h₂)) ∧
      h₁ = (rowCoef (psiMap R₁ R₂ w).J).1 * X + (rowCoef (psiMap R₁ R₂ w).J).2 * h₂ +
        (psiMap R₁ R₂ w).B.eval t := by
  have hpsi : ∀ X x₁ : ℤ, R₁.emb.apply t (x₁, h₁) = (wordAff S w).apply t (R₂.emb.apply t (X, h₂))
      ↔ (x₁, h₁) = (psiMap R₁ R₂ w).apply t (X, h₂) := by
    intro X x₁
    rw [AffMap.apply_eq_iff, psiMap, AffMap.apply_comp, AffMap.apply_comp]
  have hch : ∀ X : ℤ, (∀ c ∈ wordCharts S w R₂.f, c.Mem t (R₂.emb.apply t (X, h₂))) ↔
      ∀ n ∈ (wordCharts S w R₂.f).flatMap (pullNCs · R₂.emb), n.Sat t (X, h₂) := by
    intro X
    simp only [List.mem_flatMap, forall_exists_index, and_imp]
    constructor
    · intro h n c hc hn; exact (mem_apply_iff c R₂.emb t (X, h₂)).1 (h c hc) n hn
    · intro h c hc; exact (mem_apply_iff c R₂.emb t (X, h₂)).2 fun n hn => h n c hc hn
  simp only [allNC, List.mem_append, or_imp, forall_and, List.forall_mem_map, ← hch, hpsi]
  constructor
  · rintro ⟨x₁, X, hc₁, hc₂, hcw, he⟩
    refine ⟨X, ⟨⟨hc₂, hcw⟩, fun c hc => ?_⟩, ?_⟩
    · rw [← NC.sat_pull, ← he]; exact hc₁ c hc
    · rw [← psiMap_snd, ← he]
  · rintro ⟨X, ⟨⟨hc₂, hcw⟩, hc₁⟩, he⟩
    have he' : (((psiMap R₁ R₂ w).apply t (X, h₂)).1, h₁) = (psiMap R₁ R₂ w).apply t (X, h₂) :=
      Prod.ext rfl (by rw [psiMap_snd, he])
    refine ⟨((psiMap R₁ R₂ w).apply t (X, h₂)).1, X, fun c hc => ?_, hc₂, hcw, he'⟩
    rw [he', NC.sat_pull]; exact hc₁ c hc

/-- **Identification is restricted arithmetic.** Under embeddedness, two rows meet iff, for one
of the fixed words, a fixed finite conjunction of pairwise atoms (coefficients in `{-1,0,1}` by
`meetPA_ok`) holds at the two heights. -/
theorem meet_iff_patoms (hE : Embedded S t) {R₁ R₂ : RowSet S} (hR₁ : R₁.WF) (hR₂ : R₂.WF)
    (h₁ h₂ : ℤ) :
    Meet S t R₁ h₁ R₂ h₂ ↔ ∃ w : List (Letter S), w.length < S.C ∧ WordOK S w R₂.f R₁.f ∧
      ∀ a ∈ meetPA R₁ R₂ w, a.Sat t h₁ h₂ := by
  have step1 : Meet S t R₁ h₁ R₂ h₂ ↔ ∃ z₁ z₂ : ℤ × ℤ, R₁.At t h₁ z₁ ∧ R₂.At t h₂ z₂ ∧
      ∃ w : List (Letter S), w.length < S.C ∧ WordOK S w R₂.f R₁.f ∧
        (∀ c ∈ wordCharts S w R₂.f, c.Mem t z₂) ∧ z₁ = (wordAff S w).apply t z₂ := by
    simp only [Meet]
    refine exists₂_congr fun z₁ z₂ => and_congr Iff.rfl (and_congr Iff.rfl ?_)
    rw [← ident_iff_word hE]
    exact ⟨fun ⟨a, b, e⟩ => ⟨b, a, e.symm⟩, fun ⟨a, b, e⟩ => ⟨b, a, e.symm⟩⟩
  rw [step1]
  constructor
  · rintro ⟨z₁, z₂, ⟨x₁, hc₁, rfl⟩, ⟨X, hc₂, rfl⟩, w, hw, hok, hcw, he⟩
    refine ⟨w, hw, hok, ?_⟩
    rw [meetPA, ← exists_iff_elim _ (rowCoef_ok _) _ _ (allNC_nrm hR₁ hR₂ w),
      ← word_inner_iff]
    exact ⟨x₁, X, hc₁, hc₂, hcw, he⟩
  · rintro ⟨w, hw, hok, ha⟩
    rw [meetPA, ← exists_iff_elim _ (rowCoef_ok _) _ _ (allNC_nrm hR₁ hR₂ w),
      ← word_inner_iff] at ha
    obtain ⟨x₁, X, hc₁, hc₂, hcw, he⟩ := ha
    exact ⟨_, _, ⟨x₁, hc₁, rfl⟩, ⟨X, hc₂, rfl⟩, w, hw, hok, hcw, he⟩

end ClaudeChallenge2.Geo
