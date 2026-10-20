import Formal.Claude3IdentHF

/-!
# Theorem 1a, G3b (4): adjacency of row points as restricted arithmetic

Written by a Claude worker (2026-10-20, Theorem 1a, part G3b).

* Optional variables: `hgt ν : Option (Fin m) → ℤ` (`none ↦ 0`), `PA.toHFo`, `meetHFo`,
  `sat_meetHFo` : the identification formula where either row may sit at the fixed height `0`
  (fixed points such as marked corners, `constRow`; with `none, none` it is a sentence).
* `nbrRow R g w u` : the point `Φ_w (P) + u` of chart `g`, where `P` is the point of `R` and
  `Φ_w` the map of a record word `w` from `R.f` to `g`; `nbrRow_at`.
* `NbrMeet` : representatives in one chart differ by a unit vector; **`nbrMeet_iff`** (under
  `Embedded`): this happens iff some fixed `(g, w, u)` gives `Meet (nbrRow R₁ g w u) R₂`.
* `nbrHFo`, `sat_nbrHFo` : as a formula.
* `RowSet.Single` (at most one point; true for `affineRow`, `constRow`, and preserved by
  `nbrRow`), `AdjMeet` (the two points are adjacent in `graph S t`),
  **`adjMeet_iff`** : `AdjMeet ↔ NbrMeet ∧ ¬ Meet`, **`sat_adjHFo`**.
-/

namespace ClaudeChallenge2.Geo

open ClaudeChallenge2 R002.Claude3Fold

universe u

variable {S : Sig} {t : ℕ} {T : Type u} {m k : ℕ}

/-! ## Optional variables -/

/-- The height of an optional state variable (`none` is the fixed height `0`). -/
def hgt (ν : Fin m → T × ℤ) : Option (Fin m) → ℤ
  | none => 0
  | some x => (ν x).2

/-- The atom `a · hgt ox + b · hgt oy ≤ F(t)`. -/
def PA.toHFo (ox oy : Option (Fin m)) (c : PA) : HF T m k :=
  match ox, oy with
  | some x, some y => c.toHF x y
  | none, some y => PA.toHF y y ⟨0, c.b, c.F⟩
  | some x, none => PA.toHF x x ⟨c.a, 0, c.F⟩
  | none, none => .tNonneg (toFAff c.F)

theorem PA.sat_toHFo {c : PA} (hc : c.OK) (ox oy : Option (Fin m))
    {lo hi : T → R002.Claude3Fold.Aff} (ν : Fin m → T × ℤ) (V : Fin k → Set (T × ℤ)) :
    HF.Sat lo hi t (c.toHFo ox oy) ν V ↔ c.Sat t (hgt ν ox) (hgt ν oy) := by
  obtain ⟨a, b, F⟩ := c
  cases ox with
  | none =>
    cases oy with
    | none => simp [PA.toHFo, hgt, PA.Sat]
    | some y =>
      rw [PA.toHFo, PA.sat_toHF (c := ⟨0, b, F⟩) ⟨Or.inr (Or.inl rfl), hc.2⟩]
      simp [PA.Sat, hgt]
  | some x =>
    cases oy with
    | none =>
      rw [PA.toHFo, PA.sat_toHF (c := ⟨a, 0, F⟩) ⟨hc.1, Or.inr (Or.inl rfl)⟩]
      simp [PA.Sat, hgt]
    | some y => exact PA.sat_toHF hc x y ν V

/-- The identification formula with optional variables. -/
def meetHFo (R₁ R₂ : RowSet S) (ox oy : Option (Fin m)) : HF T m k :=
  bigOr ((wordsLT S S.C).map fun w =>
    if WordOK S w R₂.f R₁.f then bigAnd ((meetPA R₁ R₂ w).map (PA.toHFo ox oy)) else hfFalse)

theorem sat_meetHFo (hE : Embedded S t) {R₁ R₂ : RowSet S} (hR₁ : R₁.WF) (hR₂ : R₂.WF)
    (ox oy : Option (Fin m)) {lo hi : T → R002.Claude3Fold.Aff} (ν : Fin m → T × ℤ)
    (V : Fin k → Set (T × ℤ)) :
    HF.Sat lo hi t (meetHFo R₁ R₂ ox oy) ν V ↔ Meet S t R₁ (hgt ν ox) R₂ (hgt ν oy) := by
  rw [meet_iff_patoms hE hR₁ hR₂, meetHFo, sat_bigOr]
  simp only [List.mem_map, mem_wordsLT]
  constructor
  · rintro ⟨φ, ⟨w, hw, rfl⟩, hφ⟩
    split_ifs at hφ with hok
    · rw [sat_bigAnd] at hφ
      refine ⟨w, hw, hok, fun a ha => ?_⟩
      rw [← PA.sat_toHFo (meetPA_ok hR₁ hR₂ w a ha) ox oy (lo := lo) (hi := hi) ν V]
      exact hφ _ (List.mem_map_of_mem ha)
    · exact absurd hφ sat_hfFalse
  · rintro ⟨w, hw, hok, ha⟩
    refine ⟨_, ⟨w, hw, rfl⟩, ?_⟩
    simp only [hok, ↓reduceIte]
    rw [sat_bigAnd]
    intro φ hφ
    obtain ⟨a, haw, rfl⟩ := List.mem_map.1 hφ
    exact (PA.sat_toHFo (meetPA_ok hR₁ hR₂ w a haw) ox oy ν V).2 (ha a haw)

/-! ## Neighbour rows -/

/-- The translation by `u`. -/
def translMap (u : ℤ × ℤ) : AffMap := ⟨0, ⟨0, u.1⟩, ⟨0, u.2⟩⟩

theorem translMap_apply (u : ℤ × ℤ) (t : ℕ) (z : ℤ × ℤ) : (translMap u).apply t z = z + u := by
  simp [translMap, AffMap.apply, rotN, Aff.eval]

/-- The point `Φ_w (P) + u` of chart `g` (`P` the point of `R`), constrained so that the chain
of `w` from `P` stays in its charts. -/
def nbrRow (R : RowSet S) (g : Fin S.C) (w : List (Letter S)) (u : ℤ × ℤ) : RowSet S :=
  ⟨g, (translMap u).comp ((wordAff S w).comp R.emb),
    R.cons ++ (wordCharts S w R.f).flatMap (pullNCs · R.emb)⟩

theorem nbrRow_at (R : RowSet S) (g : Fin S.C) (w : List (Letter S)) (u : ℤ × ℤ) (h : ℤ)
    (z : ℤ × ℤ) :
    (nbrRow R g w u).At t h z ↔ ∃ x : ℤ, (∀ c ∈ R.cons, c.Sat t (x, h)) ∧
      (∀ ch ∈ wordCharts S w R.f, ch.Mem t (R.emb.apply t (x, h))) ∧
      z = (wordAff S w).apply t (R.emb.apply t (x, h)) + u := by
  simp only [RowSet.At, nbrRow, AffMap.apply_comp, translMap_apply, List.mem_append, or_imp,
    forall_and]
  refine exists_congr fun x => ?_
  have : (∀ n ∈ (wordCharts S w R.f).flatMap (pullNCs · R.emb), n.Sat t (x, h)) ↔
      ∀ ch ∈ wordCharts S w R.f, ch.Mem t (R.emb.apply t (x, h)) := by
    simp only [List.mem_flatMap, forall_exists_index, and_imp]
    constructor
    · intro H ch hch; exact (mem_apply_iff ch R.emb t (x, h)).2 fun n hn => H n ch hch hn
    · intro H n ch hch hn; exact (mem_apply_iff ch R.emb t (x, h)).1 (H ch hch) n hn
  rw [this, and_assoc]

theorem nbrRow_wf {R : RowSet S} (hR : R.WF) (g : Fin S.C) (w : List (Letter S)) (u : ℤ × ℤ) :
    (nbrRow R g w u).WF := by
  simp only [RowSet.WF, nbrRow, List.mem_append, List.mem_flatMap]
  rintro c (hc | ⟨ch, -, hc⟩)
  · exact hR c hc
  · exact pullNCs_nrm ch _ c hc

/-- Representatives of the two points in one chart differ by a unit vector. -/
def NbrMeet (S : Sig) (t : ℕ) (R₁ : RowSet S) (h₁ : ℤ) (R₂ : RowSet S) (h₂ : ℤ) : Prop :=
  ∃ z₁ z₂ : ℤ × ℤ, R₁.At t h₁ z₁ ∧ R₂.At t h₂ z₂ ∧
    ∃ (hz₁ : (S.chart R₁.f).Mem t z₁) (hz₂ : (S.chart R₂.f).Mem t z₂), ∃ s s' : Site S t,
      vtx s = pt S t R₁.f z₁ hz₁ ∧ vtx s' = pt S t R₂.f z₂ hz₂ ∧ s.1.1 = s'.1.1 ∧
        s'.1.2 - s.1.2 ∈ unitVec

/-- **Neighbours through fixed data.** -/
theorem nbrMeet_iff (hE : Embedded S t) (R₁ R₂ : RowSet S) (h₁ h₂ : ℤ) :
    NbrMeet S t R₁ h₁ R₂ h₂ ↔ ∃ g : Fin S.C, ∃ w : List (Letter S), ∃ u : ℤ × ℤ,
      w.length < S.C ∧ WordOK S w R₁.f g ∧ u ∈ unitVec ∧ Meet S t (nbrRow R₁ g w u) h₁ R₂ h₂ := by
  constructor
  · rintro ⟨z₁, z₂, ⟨x, hc, rfl⟩, hA₂, hz₁, hz₂, ⟨⟨g, z⟩, hz⟩, ⟨⟨g', z'⟩, hz'⟩, e, e', hf, hu⟩
    simp only at hf hu
    subst hf
    obtain ⟨w, hw, hok, hcw, hzeq⟩ := (ident_iff_word hE R₁.f g _ z).1 ⟨hz₁, hz, e.symm⟩
    refine ⟨g, w, z' - z, hw, hok, hu, z', z₂, ?_, hA₂, hz', hz₂, e'⟩
    rw [nbrRow_at]
    exact ⟨x, hc, hcw, by rw [← hzeq]; abel⟩
  · rintro ⟨g, w, u, hw, hok, hu, z', z₂, hA', hA₂, hz', hz₂, e⟩
    rw [nbrRow_at] at hA'
    obtain ⟨x, hc, hcw, rfl⟩ := hA'
    obtain ⟨hP, hz, e₀⟩ := (ident_iff_word hE R₁.f g _ _).2 ⟨w, hw, hok, hcw, rfl⟩
    refine ⟨_, z₂, ⟨x, hc, rfl⟩, hA₂, hP, hz₂,
      ⟨(g, (wordAff S w).apply t (R₁.emb.apply t (x, h₁))), hz⟩,
      ⟨(g, (wordAff S w).apply t (R₁.emb.apply t (x, h₁)) + u), hz'⟩, e₀.symm, e, rfl, ?_⟩
    show _ + u - _ ∈ unitVec
    rw [add_sub_cancel_left]; exact hu

/-- All `(g, w, u)` candidates. -/
def nbrCands (S : Sig) : List (Fin S.C × List (Letter S) × (ℤ × ℤ)) :=
  (List.finRange S.C).flatMap fun g => (wordsLT S S.C).flatMap fun w => unitVec.map fun u =>
    (g, w, u)

theorem mem_nbrCands (g : Fin S.C) (w : List (Letter S)) (u : ℤ × ℤ) :
    (g, w, u) ∈ nbrCands S ↔ w.length < S.C ∧ u ∈ unitVec := by
  simp only [nbrCands, List.mem_flatMap, List.mem_finRange, List.mem_map, mem_wordsLT,
    Prod.mk.injEq, true_and]
  constructor
  · rintro ⟨_, w', hw', u', hu', rfl, rfl, rfl⟩; exact ⟨hw', hu'⟩
  · rintro ⟨hw, hu⟩; exact ⟨g, w, hw, u, hu, rfl, rfl, rfl⟩

/-- The neighbour formula. -/
def nbrHFo (R₁ R₂ : RowSet S) (ox oy : Option (Fin m)) : HF T m k :=
  bigOr ((nbrCands S).map fun c =>
    if WordOK S c.2.1 R₁.f c.1 then meetHFo (nbrRow R₁ c.1 c.2.1 c.2.2) R₂ ox oy else hfFalse)

theorem sat_nbrHFo (hE : Embedded S t) {R₁ R₂ : RowSet S} (hR₁ : R₁.WF) (hR₂ : R₂.WF)
    (ox oy : Option (Fin m)) {lo hi : T → R002.Claude3Fold.Aff} (ν : Fin m → T × ℤ)
    (V : Fin k → Set (T × ℤ)) :
    HF.Sat lo hi t (nbrHFo R₁ R₂ ox oy) ν V ↔ NbrMeet S t R₁ (hgt ν ox) R₂ (hgt ν oy) := by
  rw [nbrMeet_iff hE, nbrHFo, sat_bigOr]
  simp only [List.mem_map]
  constructor
  · rintro ⟨φ, ⟨⟨g, w, u⟩, hc, rfl⟩, hφ⟩
    obtain ⟨hw, hu⟩ := (mem_nbrCands g w u).1 hc
    split_ifs at hφ with hok
    · exact ⟨g, w, u, hw, hok, hu,
        (sat_meetHFo hE (nbrRow_wf hR₁ g w u) hR₂ ox oy ν V).1 hφ⟩
    · exact absurd hφ sat_hfFalse
  · rintro ⟨g, w, u, hw, hok, hu, hM⟩
    refine ⟨_, ⟨(g, w, u), (mem_nbrCands g w u).2 ⟨hw, hu⟩, rfl⟩, ?_⟩
    simp only [hok, ↓reduceIte]
    exact (sat_meetHFo hE (nbrRow_wf hR₁ g w u) hR₂ ox oy ν V).2 hM

/-! ## Adjacency -/

/-- The row has at most one point at height `h`. -/
def RowSet.Single (R : RowSet S) (t : ℕ) (h : ℤ) : Prop :=
  ∀ z z', R.At t h z → R.At t h z' → z = z'

theorem affineRow_single (f : Fin S.C) (k : ℕ) (Dx Dy : Aff) (b : Bnd) (h : ℤ) :
    (affineRow f k Dx Dy b).Single t h := by
  intro z z' hz hz'
  rw [affineRow_at] at hz hz'
  rw [hz, hz']

theorem constRow_single (f : Fin S.C) (cx cy : Aff) : (constRow (S := S) f cx cy).Single t 0 := by
  intro z z' hz hz'
  rw [constRow_at] at hz hz'
  rw [hz, hz']

theorem nbrRow_single {R : RowSet S} {h : ℤ} (hS : R.Single t h) (g : Fin S.C)
    (w : List (Letter S)) (u : ℤ × ℤ) : (nbrRow R g w u).Single t h := by
  intro z z' hz hz'
  rw [nbrRow_at] at hz hz'
  obtain ⟨x, hc, -, rfl⟩ := hz
  obtain ⟨x', hc', -, rfl⟩ := hz'
  rw [hS _ _ ⟨x, hc, rfl⟩ ⟨x', hc', rfl⟩]

/-- The two points are adjacent vertices. -/
def AdjMeet (S : Sig) (t : ℕ) (R₁ : RowSet S) (h₁ : ℤ) (R₂ : RowSet S) (h₂ : ℤ) : Prop :=
  ∃ z₁ z₂ : ℤ × ℤ, R₁.At t h₁ z₁ ∧ R₂.At t h₂ z₂ ∧
    ∃ (hz₁ : (S.chart R₁.f).Mem t z₁) (hz₂ : (S.chart R₂.f).Mem t z₂),
      (graph S t).Adj (pt S t R₁.f z₁ hz₁) (pt S t R₂.f z₂ hz₂)

theorem adjMeet_iff {R₁ R₂ : RowSet S} {h₁ h₂ : ℤ} (hS₁ : R₁.Single t h₁)
    (hS₂ : R₂.Single t h₂) :
    AdjMeet S t R₁ h₁ R₂ h₂ ↔ NbrMeet S t R₁ h₁ R₂ h₂ ∧ ¬ Meet S t R₁ h₁ R₂ h₂ := by
  constructor
  · rintro ⟨z₁, z₂, hA₁, hA₂, hz₁, hz₂, hadj⟩
    obtain ⟨hne, s, s', e, e', hf, hu⟩ := (graph_adj_iff _ _).1 hadj
    refine ⟨⟨z₁, z₂, hA₁, hA₂, hz₁, hz₂, s, s', e, e', hf, hu⟩, ?_⟩
    rintro ⟨z₁', z₂', hA₁', hA₂', hz₁', hz₂', e''⟩
    obtain rfl := hS₁ _ _ hA₁ hA₁'
    obtain rfl := hS₂ _ _ hA₂ hA₂'
    exact hne e''
  · rintro ⟨⟨z₁, z₂, hA₁, hA₂, hz₁, hz₂, s, s', e, e', hf, hu⟩, hM⟩
    refine ⟨z₁, z₂, hA₁, hA₂, hz₁, hz₂,
      (graph_adj_iff _ _).2 ⟨fun he => hM ?_, s, s', e, e', hf, hu⟩⟩
    exact ⟨z₁, z₂, hA₁, hA₂, hz₁, hz₂, he⟩

/-- The adjacency formula. -/
def adjHFo (R₁ R₂ : RowSet S) (ox oy : Option (Fin m)) : HF T m k :=
  .and (nbrHFo R₁ R₂ ox oy) (.neg (meetHFo R₁ R₂ ox oy))

/-- **Adjacency as a formula** (for single points). -/
theorem sat_adjHFo (hE : Embedded S t) {R₁ R₂ : RowSet S} (hR₁ : R₁.WF) (hR₂ : R₂.WF)
    (ox oy : Option (Fin m)) {lo hi : T → R002.Claude3Fold.Aff} (ν : Fin m → T × ℤ)
    (V : Fin k → Set (T × ℤ)) (hS₁ : R₁.Single t (hgt ν ox)) (hS₂ : R₂.Single t (hgt ν oy)) :
    HF.Sat lo hi t (adjHFo R₁ R₂ ox oy) ν V ↔ AdjMeet S t R₁ (hgt ν ox) R₂ (hgt ν oy) := by
  rw [adjMeet_iff hS₁ hS₂, adjHFo, HF.Sat, HF.Sat, sat_nbrHFo hE hR₁ hR₂, sat_meetHFo hE hR₁ hR₂]

end ClaudeChallenge2.Geo
