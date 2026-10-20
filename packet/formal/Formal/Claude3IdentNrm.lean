import Formal.Claude3GeoChain

/-!
# Theorem 1a, G3b (1): normal constraints and the elimination of one position

Written by a Claude worker (2026-10-20, Theorem 1a, part G3b).

Plane coordinates are those of `ClaudeChallenge2` (basis `(1,0)`, `(0,1) = rot (1,0)`).
The three lattice normals are `x`, `y`, `x + y`; with signs they are the six functionals
`p x + q y` with `(p, q)` one of `±(1,0)`, `±(0,1)`, `±(1,1)` (`NC.Nrm`).

* `NC`, `NC.Sat`, `NC.Nrm` : a constraint `p x + q y ≤ F(t)` (integer-affine `F`).
* `chartNCs`, `mem_iff_chartNCs` : chart membership is six normal constraints.
* `NC.pull`, `NC.sat_pull`, `NC.nrm_pull` : pulling a constraint back along an `AffMap`
  (rotation plus affine translation) gives a normal constraint (`rot` permutes the normals
  with signs: `(p, q) ↦ (q, q - p)`).
* **Normals lemma** `mem_apply_iff` : `c.Mem t (φ.apply t z)` iff `z` satisfies six fixed normal
  constraints (independent of `t`).
* `AffMap.inv` : the inverse affine map.
* `PA` : a pairwise atom `a h₁ + b h₂ ≤ F(t)`, `PA.OK` : `a, b ∈ {-1, 0, 1}`.
* `rowCoef`, `rotN_snd` : `(rotN J (X, H)).2 = α X + β H` with `(α, β) = rowCoef J`, and
  `RowCoefOK` : `(α, β)` is `(0, ±1)` (parallel rows) or `(±1, 0)`, `(±1, ±1)` (same sign).
* **Elimination** `elim`, `exists_iff_elim`, `elim_ok` : `∃ X, (∀ c ∈ L, c (X, H)) ∧
  h₁ = α X + β H + E(t)` is equivalent to a fixed finite conjunction of pairwise atoms in
  `h₁, H`, all with coefficients in `{-1, 0, 1}`. Non-parallel rows (`α = ±1`): substitution
  `X = α (h₁ - β H - E)`. Parallel rows (`α = 0`): `h₁ = β H + E` and Fourier–Motzkin with unit
  coefficients (every lower bound at most every upper bound). The coefficient check is the
  determinant `±1` argument: two non-parallel normals express every normal with coefficients
  in `{-1, 0, 1}`.
-/

namespace ClaudeChallenge2.Geo

open ClaudeChallenge2

/-! ## Affine functions -/

/-- Integer multiple of an affine function. -/
def smulAff (n : ℤ) (A : Aff) : Aff := ⟨n * A.a, n * A.b⟩

@[simp] theorem smulAff_eval (n : ℤ) (A : Aff) (t : ℕ) : (smulAff n A).eval t = n * A.eval t := by
  simp only [smulAff, Aff.eval]; ring

/-! ## Normal constraints -/

/-- The constraint `p x + q y ≤ F(t)`. -/
structure NC where
  p : ℤ
  q : ℤ
  F : Aff

/-- `z` satisfies the constraint at `t`. -/
def NC.Sat (c : NC) (t : ℕ) (z : ℤ × ℤ) : Prop := c.p * z.1 + c.q * z.2 ≤ c.F.eval t

/-- `(p, q)` is one of the six signed lattice normals `±x`, `±y`, `±(x + y)`. -/
def NC.Nrm (c : NC) : Prop :=
  (c.p = 1 ∧ c.q = 0) ∨ (c.p = 0 ∧ c.q = 1) ∨ (c.p = 1 ∧ c.q = 1) ∨
    (c.p = -1 ∧ c.q = 0) ∨ (c.p = 0 ∧ c.q = -1) ∨ (c.p = -1 ∧ c.q = -1)

/-- The six normal constraints of a chart. -/
def chartNCs (c : Chart) : List NC :=
  [⟨-1, 0, negAff c.lx⟩, ⟨1, 0, c.ux⟩, ⟨0, -1, negAff c.ly⟩, ⟨0, 1, c.uy⟩,
    ⟨-1, -1, negAff c.ls⟩, ⟨1, 1, c.us⟩]

theorem mem_iff_chartNCs (c : Chart) (t : ℕ) (z : ℤ × ℤ) :
    c.Mem t z ↔ ∀ n ∈ chartNCs c, n.Sat t z := by
  obtain ⟨x, y⟩ := z
  simp only [Chart.Mem, chartNCs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, NC.Sat, negAff_eval]
  constructor
  · intro H; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith [H.1, H.2.1, H.2.2.1, H.2.2.2.1,
      H.2.2.2.2.1, H.2.2.2.2.2]
  · intro H; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith [H.1, H.2.1, H.2.2.1, H.2.2.2.1,
      H.2.2.2.2.1, H.2.2.2.2.2]

theorem chartNCs_nrm (c : Chart) : ∀ n ∈ chartNCs c, n.Nrm := by
  simp [chartNCs, NC.Nrm]

/-! ## Pulling constraints back -/

/-- `{z | rot z ∈ {p x + q y ≤ F}} = {q x + (q - p) y ≤ F}`. -/
def NC.pullRot (c : NC) : NC := ⟨c.q, c.q - c.p, c.F⟩

theorem NC.sat_pullRot (c : NC) (t : ℕ) (z : ℤ × ℤ) :
    c.Sat t (rot z) ↔ c.pullRot.Sat t z := by
  obtain ⟨x, y⟩ := z
  simp only [NC.Sat, rot, NC.pullRot]
  constructor <;> intro h <;> linarith

theorem NC.nrm_pullRot {c : NC} (h : c.Nrm) : c.pullRot.Nrm := by
  obtain ⟨p, q, F⟩ := c
  simp only [NC.Nrm, NC.pullRot] at h ⊢
  omega

/-- Pull back along `rotN n`. -/
def NC.pullRotN : ℕ → NC → NC
  | 0, c => c
  | n + 1, c => (NC.pullRotN n c.pullRot)

theorem NC.sat_pullRotN (n : ℕ) (c : NC) (t : ℕ) (z : ℤ × ℤ) :
    c.Sat t (rotN n z) ↔ (c.pullRotN n).Sat t z := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [rotN, NC.sat_pullRot, ih]; rfl

theorem NC.nrm_pullRotN (n : ℕ) {c : NC} (h : c.Nrm) : (c.pullRotN n).Nrm := by
  induction n generalizing c with
  | zero => exact h
  | succ n ih => exact ih (NC.nrm_pullRot h)

/-- Pull back along the translation by `(A t, B t)`. -/
def NC.trans (c : NC) (A B : Aff) : NC :=
  ⟨c.p, c.q, subAff (subAff c.F (smulAff c.p A)) (smulAff c.q B)⟩

theorem NC.sat_trans (c : NC) (A B : Aff) (t : ℕ) (z : ℤ × ℤ) :
    c.Sat t (z + (A.eval t, B.eval t)) ↔ (c.trans A B).Sat t z := by
  obtain ⟨x, y⟩ := z
  simp only [NC.Sat, NC.trans, Prod.mk_add_mk, subAff_eval, smulAff_eval]
  constructor <;> intro h <;> linarith

/-- Pull back along an affine map with rotation. -/
def NC.pull (c : NC) (φ : AffMap) : NC := (c.trans φ.A φ.B).pullRotN φ.J

theorem NC.sat_pull (c : NC) (φ : AffMap) (t : ℕ) (z : ℤ × ℤ) :
    c.Sat t (φ.apply t z) ↔ (c.pull φ).Sat t z := by
  rw [AffMap.apply, NC.sat_trans, NC.sat_pullRotN]; rfl

theorem NC.nrm_pull {c : NC} (h : c.Nrm) (φ : AffMap) : (c.pull φ).Nrm :=
  NC.nrm_pullRotN _ (by simpa [NC.trans, NC.Nrm] using h)

/-- The normal constraints of chart `c` pulled back along `φ`. -/
def pullNCs (c : Chart) (φ : AffMap) : List NC := (chartNCs c).map (NC.pull · φ)

/-- **Normals lemma.** Membership of `φ z = rotN J z + (A t, B t)` in a chart is the
conjunction of six fixed normal constraints `±x, ±y, ±(x + y) ≤ a t + b` on `z`. -/
theorem mem_apply_iff (c : Chart) (φ : AffMap) (t : ℕ) (z : ℤ × ℤ) :
    c.Mem t (φ.apply t z) ↔ ∀ n ∈ pullNCs c φ, n.Sat t z := by
  rw [mem_iff_chartNCs]
  simp only [pullNCs, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    NC.sat_pull]

theorem pullNCs_nrm (c : Chart) (φ : AffMap) : ∀ n ∈ pullNCs c φ, n.Nrm := by
  simp only [pullNCs, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact fun n hn => NC.nrm_pull (chartNCs_nrm c n hn) φ

/-! ## Inverse affine maps -/

/-- The inverse of `z ↦ rotN J z + d`: `w ↦ rotN (6 - J % 6) (w - d)`. -/
def AffMap.inv (φ : AffMap) : AffMap :=
  ⟨6 - φ.J % 6, (rotAff (6 - φ.J % 6) (negAff φ.A, negAff φ.B)).1,
    (rotAff (6 - φ.J % 6) (negAff φ.A, negAff φ.B)).2⟩

theorem AffMap.inv_apply' (φ : AffMap) (t : ℕ) (w : ℤ × ℤ) :
    φ.inv.apply t w = rotN (6 - φ.J % 6) (w - (φ.A.eval t, φ.B.eval t)) := by
  have := rotN_affPair (6 - φ.J % 6) (negAff φ.A, negAff φ.B) t
  simp only [negAff_eval] at this
  simp only [AffMap.apply, AffMap.inv, ← this, sub_eq_add_neg, rotN_add, Prod.neg_mk]

theorem AffMap.apply_inv (φ : AffMap) (t : ℕ) (w : ℤ × ℤ) : φ.apply t (φ.inv.apply t w) = w := by
  rw [AffMap.inv_apply', AffMap.apply, rotN_rotN_inv', sub_add_cancel]

theorem AffMap.inv_apply (φ : AffMap) (t : ℕ) (z : ℤ × ℤ) : φ.inv.apply t (φ.apply t z) = z := by
  rw [AffMap.inv_apply', AffMap.apply, add_sub_cancel_right, rotN_inv_rotN]

theorem AffMap.apply_eq_iff (φ : AffMap) (t : ℕ) (z w : ℤ × ℤ) :
    φ.apply t z = w ↔ z = φ.inv.apply t w := by
  constructor
  · rintro rfl; rw [AffMap.inv_apply]
  · rintro rfl; rw [AffMap.apply_inv]

/-! ## Pairwise atoms -/

/-- `s ∈ {-1, 0, 1}`. -/
def Sgn (s : ℤ) : Prop := s = -1 ∨ s = 0 ∨ s = 1

/-- The pairwise atom `a h₁ + b h₂ ≤ F(t)`. -/
structure PA where
  a : ℤ
  b : ℤ
  F : Aff

def PA.Sat (c : PA) (t : ℕ) (h₁ h₂ : ℤ) : Prop := c.a * h₁ + c.b * h₂ ≤ c.F.eval t

/-- Coefficients in `{-1, 0, 1}` (no coefficient `2`): an atom of restricted arithmetic. -/
def PA.OK (c : PA) : Prop := Sgn c.a ∧ Sgn c.b

/-! ## Second coordinate of a rotation -/

/-- `((rotN J (1,0)).2, (rotN J (0,1)).2)`. -/
def rowCoef (J : ℕ) : ℤ × ℤ := ((rotN J (1, 0)).2, (rotN J (0, 1)).2)

theorem rotN_snd (J : ℕ) (z : ℤ × ℤ) :
    (rotN J z).2 = (rowCoef J).1 * z.1 + (rowCoef J).2 * z.2 := by
  obtain ⟨x, y⟩ := z
  simp only [rowCoef]
  rw [rotN_mod J (x, y), rotN_mod J (1, 0), rotN_mod J (0, 1)]
  have h6 : J % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases (J % 6) <;> simp [rotN, rot]

/-- The possible coefficient pairs: parallel rows `(0, ±1)`, otherwise `α = ±1`, `β ∈ {0, α}`. -/
def RowCoefOK (αβ : ℤ × ℤ) : Prop :=
  (αβ.1 = 0 ∧ (αβ.2 = 1 ∨ αβ.2 = -1)) ∨
    ((αβ.1 = 1 ∨ αβ.1 = -1) ∧ (αβ.2 = 0 ∨ αβ.2 = αβ.1))

theorem rowCoef_ok (J : ℕ) : RowCoefOK (rowCoef J) := by
  simp only [rowCoef]
  rw [rotN_mod J (1, 0), rotN_mod J (0, 1)]
  have h6 : J % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases (J % 6) <;> simp [rotN, rot, RowCoefOK]

/-! ## Fourier–Motzkin with unit coefficients -/

theorem le_foldr_max {l : ℤ} {ls : List ℤ} (b : ℤ) (h : l ∈ ls) : l ≤ ls.foldr max b := by
  induction ls with
  | nil => simp at h
  | cons a ls ih =>
    simp only [List.mem_cons] at h
    simp only [List.foldr_cons]
    rcases h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem foldr_max_le {ls : List ℤ} {b c : ℤ} (hb : b ≤ c) (h : ∀ l ∈ ls, l ≤ c) :
    ls.foldr max b ≤ c := by
  induction ls with
  | nil => exact hb
  | cons a ls ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun l hl => h l (by simp [hl]))

theorem foldr_min_le {u : ℤ} {us : List ℤ} (b : ℤ) (h : u ∈ us) : us.foldr min b ≤ u := by
  induction us with
  | nil => simp at h
  | cons a us ih =>
    simp only [List.mem_cons] at h
    simp only [List.foldr_cons]
    rcases h with rfl | h
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (ih h)

theorem foldr_min_le_self (us : List ℤ) (b : ℤ) : us.foldr min b ≤ b := by
  induction us with
  | nil => exact le_refl _
  | cons a us ih => exact le_trans (min_le_right _ _) ih

/-- An integer lies between finitely many lower and upper bounds iff every lower bound is at
most every upper bound. -/
theorem exists_between_iff (ls us : List ℤ) :
    (∃ X : ℤ, (∀ l ∈ ls, l ≤ X) ∧ ∀ u ∈ us, X ≤ u) ↔ ∀ l ∈ ls, ∀ u ∈ us, l ≤ u := by
  constructor
  · rintro ⟨X, h1, h2⟩ l hl u hu
    exact le_trans (h1 l hl) (h2 u hu)
  · intro h
    refine ⟨ls.foldr max (us.foldr min 0), fun l hl => le_foldr_max _ hl, fun u hu => ?_⟩
    exact foldr_max_le (foldr_min_le _ hu) fun l hl => h l hl u hu

/-! ## Elimination of the position -/

/-- Constraints with `p = s`. -/
def ncFilter (s : ℤ) (L : List NC) : List NC := L.filter (fun c => decide (c.p = s))

theorem mem_ncFilter {s : ℤ} {L : List NC} {c : NC} : c ∈ ncFilter s L ↔ c ∈ L ∧ c.p = s := by
  simp [ncFilter]

/-- The parallel case (`α = 0`): `h₁ = β H + E`, the constraints without `X`, and every lower
bound (`p = -1`) against every upper bound (`p = 1`). -/
def elimPar (β : ℤ) (E : Aff) (L : List NC) : List PA :=
  [⟨1, -β, E⟩, ⟨-1, β, negAff E⟩] ++ (ncFilter 0 L).map (fun c => ⟨0, c.q, c.F⟩) ++
    (ncFilter (-1) L).flatMap (fun l =>
      (ncFilter 1 L).map (fun u => ⟨0, l.q + u.q, addAff l.F u.F⟩))

/-- The non-parallel case (`α = ±1`): substitute `X = α (h₁ - β H - E)`. -/
def elimSub (α β : ℤ) (E : Aff) (L : List NC) : List PA :=
  L.map (fun c => ⟨c.p * α, c.q - c.p * α * β, addAff c.F (smulAff (c.p * α) E)⟩)

/-- The elimination of `X` from `(∀ c ∈ L, c (X, H)) ∧ h₁ = α X + β H + E`. -/
def elim (αβ : ℤ × ℤ) (E : Aff) (L : List NC) : List PA :=
  if αβ.1 = 0 then elimPar αβ.2 E L else elimSub αβ.1 αβ.2 E L

theorem exists_iff_elimPar (β : ℤ) (E : Aff) (L : List NC) (hL : ∀ c ∈ L, c.Nrm) (t : ℕ)
    (h₁ H : ℤ) :
    (∃ X : ℤ, (∀ c ∈ L, c.Sat t (X, H)) ∧ h₁ = 0 * X + β * H + E.eval t) ↔
      ∀ a ∈ elimPar β E L, a.Sat t h₁ H := by
  have hsplit : ∀ c ∈ L, c.p = 0 ∨ c.p = -1 ∨ c.p = 1 := by
    intro c hc
    rcases hL c hc with h | h | h | h | h | h <;> omega
  have key : (∃ X : ℤ, ∀ c ∈ L, c.Sat t (X, H)) ↔ (∀ c ∈ ncFilter 0 L, c.q * H ≤ c.F.eval t) ∧
      ∀ l ∈ ncFilter (-1) L, ∀ u ∈ ncFilter 1 L,
        (l.q + u.q) * H ≤ l.F.eval t + u.F.eval t := by
    have e1 : (∃ X : ℤ, ∀ c ∈ L, c.Sat t (X, H)) ↔ (∀ c ∈ ncFilter 0 L, c.q * H ≤ c.F.eval t) ∧
        ∃ X : ℤ, (∀ l ∈ (ncFilter (-1) L).map (fun c => c.q * H - c.F.eval t), l ≤ X) ∧
          ∀ u ∈ (ncFilter 1 L).map (fun c => c.F.eval t - c.q * H), X ≤ u := by
      simp only [List.forall_mem_map, mem_ncFilter, and_imp]
      constructor
      · rintro ⟨X, hX⟩
        refine ⟨fun c hc hp => ?_, X, fun c hc hp => ?_, fun c hc hp => ?_⟩
        · have := hX c hc; simp only [NC.Sat, hp] at this; linarith
        · have := hX c hc; simp only [NC.Sat, hp] at this; linarith
        · have := hX c hc; simp only [NC.Sat, hp] at this; linarith
      · rintro ⟨h0, X, hl, hu⟩
        refine ⟨X, fun c hc => ?_⟩
        rcases hsplit c hc with hp | hp | hp
        · have := h0 c hc hp; simp only [NC.Sat, hp]; linarith
        · have := hl c hc hp; simp only [NC.Sat, hp]; linarith
        · have := hu c hc hp; simp only [NC.Sat, hp]; linarith
    rw [e1, exists_between_iff]
    simp only [List.forall_mem_map]
    refine and_congr Iff.rfl ⟨fun h l hl u hu => ?_, fun h l hl u hu => ?_⟩
    · have := h l hl u hu; linarith
    · have := h l hl u hu; linarith
  simp only [zero_mul, zero_add]
  rw [exists_and_right, key]
  simp only [elimPar, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_flatMap]
  constructor
  · rintro ⟨⟨h0, hlu⟩, he⟩ a ha
    rcases ha with ((rfl | rfl) | ⟨c, hc, rfl⟩) | ⟨l, hl, u, hu, rfl⟩
    · simp only [PA.Sat]; linarith
    · simp only [PA.Sat, negAff_eval]; linarith
    · simp only [PA.Sat, zero_mul, zero_add]; exact h0 c hc
    · simp only [PA.Sat, zero_mul, zero_add, addAff_eval]; exact hlu l hl u hu
  · intro h
    refine ⟨⟨fun c hc => ?_, fun l hl u hu => ?_⟩, ?_⟩
    · have := h ⟨0, c.q, c.F⟩ (Or.inl (Or.inr ⟨c, hc, rfl⟩))
      simpa [PA.Sat] using this
    · have := h ⟨0, l.q + u.q, addAff l.F u.F⟩ (Or.inr ⟨l, hl, u, hu, rfl⟩)
      simpa [PA.Sat] using this
    · have h1 := h ⟨1, -β, E⟩ (Or.inl (Or.inl (Or.inl rfl)))
      have h2 := h ⟨-1, β, negAff E⟩ (Or.inl (Or.inl (Or.inr rfl)))
      simp only [PA.Sat, negAff_eval] at h1 h2
      linarith

theorem exists_iff_elimSub (α β : ℤ) (hα : α = 1 ∨ α = -1) (E : Aff) (L : List NC) (t : ℕ)
    (h₁ H : ℤ) :
    (∃ X : ℤ, (∀ c ∈ L, c.Sat t (X, H)) ∧ h₁ = α * X + β * H + E.eval t) ↔
      ∀ a ∈ elimSub α β E L, a.Sat t h₁ H := by
  have hαα : α * α = 1 := by rcases hα with rfl | rfl <;> norm_num
  have hX : ∀ X : ℤ, h₁ = α * X + β * H + E.eval t ↔ X = α * (h₁ - β * H - E.eval t) := by
    intro X
    constructor
    · rintro rfl; linear_combination (-X) * hαα
    · rintro rfl; linear_combination (-(h₁ - β * H - E.eval t)) * hαα
  simp only [hX, exists_eq_right, elimSub, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, PA.Sat, NC.Sat, addAff_eval, smulAff_eval]
  refine forall₂_congr fun c _ => ?_
  constructor <;> intro h <;> linarith

/-- **Elimination.** For the coefficient pairs of rotations, the existence of a position `X`
is a fixed finite conjunction of pairwise atoms. -/
theorem exists_iff_elim (αβ : ℤ × ℤ) (hαβ : RowCoefOK αβ) (E : Aff) (L : List NC)
    (hL : ∀ c ∈ L, c.Nrm) (t : ℕ) (h₁ H : ℤ) :
    (∃ X : ℤ, (∀ c ∈ L, c.Sat t (X, H)) ∧ h₁ = αβ.1 * X + αβ.2 * H + E.eval t) ↔
      ∀ a ∈ elim αβ E L, a.Sat t h₁ H := by
  obtain ⟨α, β⟩ := αβ
  simp only [elim]
  split_ifs with h0
  · subst h0
    exact exists_iff_elimPar β E L hL t h₁ H
  · have hα : α = 1 ∨ α = -1 := by
      rcases hαβ with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h h0
      · exact h
    exact exists_iff_elimSub α β hα E L t h₁ H

/-- **No coefficient `2`.** Every atom produced by the elimination has coefficients in
`{-1, 0, 1}`. -/
theorem elim_ok (αβ : ℤ × ℤ) (hαβ : RowCoefOK αβ) (E : Aff) (L : List NC)
    (hL : ∀ c ∈ L, c.Nrm) : ∀ a ∈ elim αβ E L, a.OK := by
  obtain ⟨α, β⟩ := αβ
  simp only [RowCoefOK] at hαβ
  simp only [elim]
  split_ifs with h0
  · have hβ : β = 1 ∨ β = -1 := by
      rcases hαβ with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · omega
    simp only [elimPar, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map, List.mem_flatMap, mem_ncFilter]
    rintro a (((rfl | rfl) | ⟨c, ⟨hc, hp⟩, rfl⟩) | ⟨l, ⟨hl, hlp⟩, u, ⟨hu, hup⟩, rfl⟩)
    · unfold PA.OK Sgn; dsimp only; omega
    · unfold PA.OK Sgn; dsimp only; omega
    · have := hL c hc; simp only [NC.Nrm] at this; unfold PA.OK Sgn; dsimp only; omega
    · have := hL l hl; have := hL u hu; simp only [NC.Nrm] at *; unfold PA.OK Sgn; dsimp only; omega
  · have hα : (α = 1 ∨ α = -1) ∧ (β = 0 ∨ β = α) := by
      rcases hαβ with ⟨h, -⟩ | h
      · exact absurd h h0
      · exact h
    simp only [elimSub, List.mem_map]
    rintro a ⟨c, hc, rfl⟩
    have hc' := hL c hc
    simp only [NC.Nrm] at hc'
    simp only [PA.OK, Sgn]
    obtain ⟨hα1 | hα1, hβ | hβ⟩ := hα <;> subst hα1 <;> subst hβ <;>
      rcases hc' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp [h1, h2]

end ClaudeChallenge2.Geo
