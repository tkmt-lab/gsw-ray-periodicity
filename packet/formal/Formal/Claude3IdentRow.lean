import Formal.Claude3IdentDeg

/-!
# Theorem 1a, G3b (6): convenience descriptors for G6

Written by a Claude worker (2026-10-20, Theorem 1a, part G3b).

* `rowPtRow f k η lows ups` : the points `rotN k (rowPt h (2 x + η))` (`η ∈ {0, 1}`) of the row
  walk of paper eq. (rows), with positions `x` between the bounds (`rowPtRow_at`);
  `rowPtPt f k η b` : the single point with `x = σ h + c(t)` (`rowPtPt_at`, `rowPtPt_single`).
  An index `j` of fixed parity, `j = 2 (σ h + c) + η`, is of this form. Several lower (upper)
  bounds express a `max` (`min`), e.g. `A_e = max(L_x, L_s - h)`.
* `cornerRow m` : the marked corner `m` as a row at height `0` (`cornerRow_at`).
* `siteHFo R ox`, `sat_siteHFo` : the (single) point of `R` exists and is a site.
* `degAllHFo R n ox`, `sat_degAllHFo` : every site point of `R` has degree `n`.
* `guardHFo L ox oy`, `sat_guardHFo` : a conjunction of pairwise atoms (for branch guards
  such as `h ≤ U_s - U_x`).
-/

namespace ClaudeChallenge2.Geo

open ClaudeChallenge2 R002.Claude3Fold

universe u

variable {S : Sig} {t : ℕ}

/-- The constant affine function. -/
def constAff (c : ℤ) : Aff := ⟨0, c⟩

@[simp] theorem constAff_eval (c : ℤ) (t : ℕ) : (constAff c).eval t = c := by
  simp [constAff, Aff.eval]

theorem rowPt_two_mul (h x η : ℤ) (hη : η = 0 ∨ η = 1) : rowPt h (2 * x + η) = (x, h + η) := by
  rcases hη with rfl | rfl
  · simpa using rowPt_even h x
  · exact rowPt_odd h x

/-- The row-walk points `rotN k (rowPt h (2 x + η))` of chart `f`, positions between bounds. -/
def rowPtRow (f : Fin S.C) (k : ℕ) (η : ℤ) (lows ups : List Bnd) : RowSet S :=
  intervalRow f k (constAff (rotN k (0, η)).1) (constAff (rotN k (0, η)).2) lows ups

theorem rowPtRow_at (f : Fin S.C) (k : ℕ) {η : ℤ} (hη : η = 0 ∨ η = 1) (lows ups : List Bnd)
    (h : ℤ) (z : ℤ × ℤ) :
    (rowPtRow f k η lows ups).At t h z ↔ ∃ x : ℤ, ((∀ b ∈ lows, b.σ * h + b.c.eval t ≤ x) ∧
      ∀ b ∈ ups, x ≤ b.σ * h + b.c.eval t) ∧ z = rotN k (rowPt h (2 * x + η)) := by
  rw [rowPtRow, intervalRow_at]
  refine exists_congr fun x => and_congr Iff.rfl ?_
  rw [rowPt_two_mul h x η hη, show ((x, h + η) : ℤ × ℤ) = (x, h) + (0, η) by simp, rotN_add]
  simp

theorem rowPtRow_wf (f : Fin S.C) (k : ℕ) (η : ℤ) {lows ups : List Bnd}
    (hl : ∀ b ∈ lows, b.WF) (hu : ∀ b ∈ ups, b.WF) : (rowPtRow f k η lows ups).WF :=
  intervalRow_wf f k _ _ hl hu

/-- The single row-walk point `rotN k (rowPt h (2 (σ h + c) + η))`. -/
def rowPtPt (f : Fin S.C) (k : ℕ) (η : ℤ) (b : Bnd) : RowSet S := rowPtRow f k η [b] [b]

theorem rowPtPt_at (f : Fin S.C) (k : ℕ) {η : ℤ} (hη : η = 0 ∨ η = 1) (b : Bnd) (h : ℤ)
    (z : ℤ × ℤ) :
    (rowPtPt f k η b).At t h z ↔ z = rotN k (rowPt h (2 * (b.σ * h + b.c.eval t) + η)) := by
  rw [rowPtPt, rowPtRow_at f k hη]
  simp only [List.mem_singleton, forall_eq]
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    rw [le_antisymm h2 h1]
  · rintro rfl
    exact ⟨_, ⟨le_refl _, le_refl _⟩, rfl⟩

theorem rowPtPt_wf (f : Fin S.C) (k : ℕ) (η : ℤ) {b : Bnd} (hb : b.WF) :
    (rowPtPt f k η b).WF :=
  rowPtRow_wf f k η (by simpa using hb) (by simpa using hb)

theorem rowPtPt_single (f : Fin S.C) (k : ℕ) {η : ℤ} (hη : η = 0 ∨ η = 1) (b : Bnd) (h : ℤ) :
    (rowPtPt f k η b).Single t h := by
  intro z z' hz hz'
  rw [rowPtPt_at f k hη] at hz hz'
  rw [hz, hz']

/-- The marked corner `m`, as a row at height `0`. -/
def cornerRow (S : Sig) (m : Fin S.M) : RowSet S := constRow (S.mchart m) (S.mx m) (S.my m)

theorem cornerRow_at (m : Fin S.M) (z : ℤ × ℤ) :
    (cornerRow S m).At t 0 z ↔ z = ((S.mx m).eval t, (S.my m).eval t) :=
  constRow_at _ _ _ z

theorem cornerRow_wf (m : Fin S.M) : (cornerRow S m).WF := constRow_wf _ _ _

theorem cornerRow_single (m : Fin S.M) : (cornerRow S m).Single t 0 := constRow_single _ _ _

/-- Meeting the corner row is being the marked corner's vertex. -/
theorem meet_cornerRow_iff (R : RowSet S) (h : ℤ) (m : Fin S.M) :
    Meet S t R h (cornerRow S m) 0 ↔ ∃ z, R.At t h z ∧ ∃ hz : (S.chart R.f).Mem t z,
      ∃ hm : (S.chart (S.mchart m)).Mem t ((S.mx m).eval t, (S.my m).eval t),
        pt S t R.f z hz = vtx ⟨(S.mchart m, ((S.mx m).eval t, (S.my m).eval t)), hm⟩ := by
  constructor
  · rintro ⟨z, z', hA, hA', hz, hz', e⟩
    rw [cornerRow_at] at hA'
    subst hA'
    exact ⟨z, hA, hz, hz', e⟩
  · rintro ⟨z, hA, hz, hm, e⟩
    exact ⟨z, _, hA, (cornerRow_at m _).2 rfl, hz, hm, e⟩

/-! ## Sites, degrees for all site points, guards -/

variable {T : Type u} {m k : ℕ}

/-- The point of `R` exists and is a site. -/
def siteHFo (R : RowSet S) (ox : Option (Fin m)) : HF T m k := meetHFo R R ox ox

theorem sat_siteHFo (hE : Embedded S t) {R : RowSet S} (hR : R.WF) (ox : Option (Fin m))
    {lo hi : T → R002.Claude3Fold.Aff} (ν : Fin m → T × ℤ) (V : Fin k → Set (T × ℤ)) :
    HF.Sat lo hi t (siteHFo R ox) ν V ↔
      ∃ P, R.At t (hgt ν ox) P ∧ (S.chart R.f).Mem t P := by
  rw [siteHFo, sat_meetHFo hE hR hR]
  constructor
  · rintro ⟨z, -, hA, -, hz, -, -⟩; exact ⟨z, hA, hz⟩
  · rintro ⟨z, hA, hz⟩; exact ⟨z, z, hA, hA, hz, hz, rfl⟩

/-- Every site point of `R` has degree `n`. -/
def degAllHFo (R : RowSet S) (n : ℕ) (ox : Option (Fin m)) : HF T m k :=
  HF.imp (siteHFo R ox) (degHFo R n ox)

theorem sat_degAllHFo (hE : Embedded S t) {R : RowSet S} (hR : R.WF) (n : ℕ)
    (ox : Option (Fin m)) {lo hi : T → R002.Claude3Fold.Aff} (ν : Fin m → T × ℤ)
    (V : Fin k → Set (T × ℤ)) (hS : R.Single t (hgt ν ox)) :
    HF.Sat lo hi t (degAllHFo R n ox) ν V ↔
      ∀ P (_ : R.At t (hgt ν ox) P) (hP : (S.chart R.f).Mem t P),
        deg (graph S t) (pt S t R.f P hP) = n := by
  rw [degAllHFo, HF.sat_imp, sat_siteHFo hE hR]
  constructor
  · intro H P hA hP
    exact (sat_degHFo hE hR n ox ν V hS hA hP).1 (H ⟨P, hA, hP⟩)
  · rintro H ⟨P, hA, hP⟩
    exact (sat_degHFo hE hR n ox ν V hS hA hP).2 (H P hA hP)

/-- A conjunction of pairwise atoms. -/
def guardHFo (L : List PA) (ox oy : Option (Fin m)) : HF T m k := bigAnd (L.map (PA.toHFo ox oy))

theorem sat_guardHFo {L : List PA} (hL : ∀ a ∈ L, a.OK) (ox oy : Option (Fin m))
    {lo hi : T → R002.Claude3Fold.Aff} (ν : Fin m → T × ℤ) (V : Fin k → Set (T × ℤ)) :
    HF.Sat lo hi t (guardHFo L ox oy) ν V ↔ ∀ a ∈ L, a.Sat t (hgt ν ox) (hgt ν oy) := by
  rw [guardHFo, sat_bigAnd]
  constructor
  · intro H a ha
    exact (PA.sat_toHFo (hL a ha) ox oy ν V).1 (H _ (List.mem_map_of_mem ha))
  · intro H φ hφ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hφ
    exact (PA.sat_toHFo (hL a ha) ox oy ν V).2 (H a ha)

end ClaudeChallenge2.Geo
