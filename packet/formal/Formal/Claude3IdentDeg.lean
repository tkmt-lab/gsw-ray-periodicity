import Formal.Claude3IdentAdj

/-!
# Theorem 1a, G3b (5): the degree of a row point as restricted arithmetic

Written by a Claude worker (2026-10-20, Theorem 1a, part G3b).

For a row `R` with a single point `P` (a site of `R.f`) at height `h`, the neighbours of the
vertex of `P` are the vertices of the candidate points `nbrRow R g w u` (`(g, w, u)` in the
fixed list `degCands R`) that exist and differ from it (`adj_iff_cand`). Hence
`deg = n` iff some sublist `A` of candidates of length `n` consists of existing, non-self,
pairwise different neighbours and represents every existing non-self candidate
(`DegEq`, **`degEq_iff`**). All conditions are identifications of rows at the same height,
so this is a fixed formula of the restricted arithmetic (**`degHFo`**, **`sat_degHFo`**).

* `count_classes` : the combinatorial core (a list of representatives of the classes of a
  function on a list has length `n` iff the image has `n` elements).
-/

namespace ClaudeChallenge2.Geo

open ClaudeChallenge2 R002.Claude3Fold

universe u

variable {S : Sig} {t : ℕ}

/-! ## Counting classes -/

theorem exists_reps {α β : Type*} (nc : α → β) (L : List α) :
    ∃ A : List α, A.Sublist L ∧ A.Pairwise (fun a b => nc a ≠ nc b) ∧
      ∀ c ∈ L, ∃ a ∈ A, nc c = nc a := by
  induction L with
  | nil => exact ⟨[], List.Sublist.slnil, List.Pairwise.nil, by simp⟩
  | cons c L ih =>
    obtain ⟨A, hA, hp, hc⟩ := ih
    by_cases h : ∃ a ∈ A, nc c = nc a
    · refine ⟨A, hA.cons c, hp, ?_⟩
      intro c' hc'
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact h
      · exact hc c' hc'
    · push Not at h
      refine ⟨c :: A, hA.cons_cons c, List.pairwise_cons.2 ⟨h, hp⟩, ?_⟩
      intro c' hc'
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact ⟨c', by simp, rfl⟩
      · obtain ⟨a, ha, e⟩ := hc c' hc'
        exact ⟨a, by simp [ha], e⟩

theorem card_of_reps {α β : Type*} [DecidableEq β] (nc : α → β) {L A : List α}
    (hA : A.Sublist L) (hp : A.Pairwise (fun a b => nc a ≠ nc b))
    (hc : ∀ c ∈ L, ∃ a ∈ A, nc c = nc a) : (L.map nc).toFinset.card = A.length := by
  have hnd : (A.map nc).Nodup := List.pairwise_map.2 hp
  have heq : (L.map nc).toFinset = (A.map nc).toFinset := by
    ext b
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨c, hcL, rfl⟩
      obtain ⟨a, ha, e⟩ := hc c hcL
      exact ⟨a, ha, e.symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, hA.subset ha, rfl⟩
  rw [heq, List.toFinset_card_of_nodup hnd, List.length_map]

theorem count_classes {α β : Type*} [DecidableEq β] (nc : α → β) (L : List α) (n : ℕ) :
    (∃ A : List α, A.Sublist L ∧ A.length = n ∧ A.Pairwise (fun a b => nc a ≠ nc b) ∧
      ∀ c ∈ L, ∃ a ∈ A, nc c = nc a) ↔ (L.map nc).toFinset.card = n := by
  constructor
  · rintro ⟨A, hA, rfl, hp, hc⟩
    exact card_of_reps nc hA hp hc
  · intro h
    obtain ⟨A, hA, hp, hc⟩ := exists_reps nc L
    exact ⟨A, hA, by rw [← card_of_reps nc hA hp hc, h], hp, hc⟩

/-! ## Candidates -/

/-- A neighbour candidate `(g, w, u)`. -/
abbrev Cand (S : Sig) : Type := Fin S.C × List (Letter S) × (ℤ × ℤ)

/-- The candidates whose word runs from `R.f` to `g`. -/
def degCands (R : RowSet S) : List (Cand S) :=
  (nbrCands S).filter fun c => decide (WordOK S c.2.1 R.f c.1)

theorem mem_degCands {R : RowSet S} {c : Cand S} :
    c ∈ degCands R ↔ c.2.1.length < S.C ∧ c.2.2 ∈ unitVec ∧ WordOK S c.2.1 R.f c.1 := by
  obtain ⟨g, w, u⟩ := c
  simp [degCands, mem_nbrCands, and_assoc]

/-- The candidate row. -/
def candRow (R : RowSet S) (c : Cand S) : RowSet S := nbrRow R c.1 c.2.1 c.2.2

/-- `w'` is the vertex of the candidate point. -/
def CandV (R : RowSet S) (c : Cand S) (t : ℕ) (h : ℤ) (w' : Vertex S t) : Prop :=
  ∃ z : ℤ × ℤ, ∃ hz : (S.chart c.1).Mem t z, (candRow R c).At t h z ∧ pt S t c.1 z hz = w'

section Facts

variable {R : RowSet S} {h : ℤ} (hS : R.Single t h)
include hS

theorem candV_unique {c : Cand S} {w₁ w₂ : Vertex S t} (h₁ : CandV R c t h w₁)
    (h₂ : CandV R c t h w₂) : w₁ = w₂ := by
  obtain ⟨z, hz, hA, rfl⟩ := h₁
  obtain ⟨z', hz', hA', rfl⟩ := h₂
  obtain rfl := nbrRow_single hS c.1 c.2.1 c.2.2 z z' hA hA'
  rfl

omit hS in
theorem meet_self_iff (c : Cand S) :
    Meet S t (candRow R c) h (candRow R c) h ↔ ∃ w', CandV R c t h w' := by
  constructor
  · rintro ⟨z, -, hA, -, hz, -, -⟩
    exact ⟨_, z, hz, hA, rfl⟩
  · rintro ⟨_, z, hz, hA, rfl⟩
    exact ⟨z, z, hA, hA, hz, hz, rfl⟩

omit hS in
theorem meet_cand_iff (c d : Cand S) :
    Meet S t (candRow R c) h (candRow R d) h ↔ ∃ w', CandV R c t h w' ∧ CandV R d t h w' := by
  constructor
  · rintro ⟨z, z', hA, hA', hz, hz', e⟩
    exact ⟨_, ⟨z, hz, hA, rfl⟩, ⟨z', hz', hA', e.symm⟩⟩
  · rintro ⟨_, ⟨z, hz, hA, rfl⟩, ⟨z', hz', hA', e⟩⟩
    exact ⟨z, z', hA, hA', hz, hz', e.symm⟩

theorem meet_base_iff {P : ℤ × ℤ} (hA : R.At t h P) (hP : (S.chart R.f).Mem t P) (c : Cand S) :
    Meet S t (candRow R c) h R h ↔ CandV R c t h (pt S t R.f P hP) := by
  constructor
  · rintro ⟨z, z', hAz, hAz', hz, hz', e⟩
    obtain rfl := hS _ _ hA hAz'
    exact ⟨z, hz, hAz, e⟩
  · rintro ⟨z, hz, hAz, e⟩
    exact ⟨z, P, hAz, hA, hz, hP, e⟩

theorem adj_iff_cand (hE : Embedded S t) {P : ℤ × ℤ} (hA : R.At t h P)
    (hP : (S.chart R.f).Mem t P) (w' : Vertex S t) :
    (graph S t).Adj (pt S t R.f P hP) w' ↔ w' ≠ pt S t R.f P hP ∧
      ∃ c ∈ degCands R, CandV R c t h w' := by
  constructor
  · obtain ⟨x, hc, rfl⟩ := hA
    intro hadj
    obtain ⟨hne, ⟨⟨g, z⟩, hz⟩, ⟨⟨g', z'⟩, hz'⟩, e, e', hf, hu⟩ := (graph_adj_iff _ _).1 hadj
    simp only at hf hu
    subst hf
    obtain ⟨w, hw, hok, hcw, hzeq⟩ := (ident_iff_word hE R.f g _ z).1 ⟨hP, hz, e.symm⟩
    refine ⟨Ne.symm hne, (g, w, z' - z), mem_degCands.2 ⟨hw, hu, hok⟩, z', hz', ?_, e'⟩
    rw [candRow, nbrRow_at]
    exact ⟨x, hc, hcw, by rw [← hzeq]; simp⟩
  · rintro ⟨hne, ⟨g, w, u⟩, hcand, z, hz, hAz, rfl⟩
    obtain ⟨hw, hu, hok⟩ := mem_degCands.1 hcand
    rw [candRow, nbrRow_at] at hAz
    obtain ⟨x', hc', hcw, rfl⟩ := hAz
    have hPP := hS _ _ ⟨x', hc', rfl⟩ hA
    subst hPP
    obtain ⟨hP', hz₀, e₀⟩ := (ident_iff_word hE R.f g _ _).2 ⟨w, hw, hok, hcw, rfl⟩
    refine (graph_adj_iff _ _).2 ⟨Ne.symm hne,
      ⟨(g, (wordAff S w).apply t (R.emb.apply t (x', h))), hz₀⟩,
      ⟨(g, (wordAff S w).apply t (R.emb.apply t (x', h)) + u), hz⟩, e₀.symm, rfl, rfl, ?_⟩
    show _ + u - _ ∈ unitVec
    rw [add_sub_cancel_left]; exact hu

end Facts

/-! ## The degree condition -/

/-- `deg = n`, written with identifications of candidate rows only. -/
def DegEq (S : Sig) (t : ℕ) (R : RowSet S) (h : ℤ) (n : ℕ) : Prop :=
  ∃ A : List (Cand S), A.Sublist (degCands R) ∧ A.length = n ∧
    (∀ a ∈ A, Meet S t (candRow R a) h (candRow R a) h ∧ ¬ Meet S t (candRow R a) h R h) ∧
    A.Pairwise (fun a b => ¬ Meet S t (candRow R a) h (candRow R b) h) ∧
    ∀ c ∈ degCands R, Meet S t (candRow R c) h (candRow R c) h → ¬ Meet S t (candRow R c) h R h →
      ∃ a ∈ A, Meet S t (candRow R c) h (candRow R a) h

/-- **Degree through identifications.** -/
theorem degEq_iff (hE : Embedded S t) {R : RowSet S} {h : ℤ} (hS : R.Single t h)
    {P : ℤ × ℤ} (hA : R.At t h P) (hP : (S.chart R.f).Mem t P) (n : ℕ) :
    DegEq S t R h n ↔ deg (graph S t) (pt S t R.f P hP) = n := by
  classical
  set v := pt S t R.f P hP with hv
  let Pres : Cand S → Prop := fun c => ∃ w', CandV R c t h w'
  let nc : Cand S → Vertex S t := fun c => if hc : Pres c then Classical.choose hc else v
  have nc_spec : ∀ c, Pres c → CandV R c t h (nc c) := by
    intro c hc
    simp only [nc, hc, ↓reduceDIte]
    exact Classical.choose_spec hc
  have nc_eq : ∀ c w', CandV R c t h w' → nc c = w' := fun c w' hw =>
    candV_unique hS (nc_spec c ⟨w', hw⟩) hw
  let good : Cand S → Prop := fun c => Pres c ∧ ¬ CandV R c t h v
  let L := (degCands R).filter fun c => decide (good c)
  have hL : ∀ c, c ∈ L ↔ c ∈ degCands R ∧ good c := by
    intro c; simp [L]
  -- the neighbour set
  have hN : (graph S t).neighborSet v = ((L.map nc).toFinset : Set (Vertex S t)) := by
    ext w'
    simp only [SimpleGraph.mem_neighborSet, Finset.mem_coe, List.mem_toFinset, List.mem_map]
    rw [adj_iff_cand hS hE hA hP]
    constructor
    · rintro ⟨hne, c, hc, hw⟩
      refine ⟨c, (hL c).2 ⟨hc, ⟨w', hw⟩, fun hv' => hne (candV_unique hS hw hv')⟩, nc_eq c w' hw⟩
    · rintro ⟨c, hcL, rfl⟩
      obtain ⟨hc, hpres, hnself⟩ := (hL c).1 hcL
      refine ⟨fun e => hnself ?_, c, hc, nc_spec c hpres⟩
      have := nc_spec c hpres
      rwa [e] at this
  have hdeg : deg (graph S t) v = (L.map nc).toFinset.card := by
    rw [deg, hN, Set.ncard_coe_finset]
  rw [hdeg, ← count_classes nc L n]
  -- translate `DegEq`
  have hsame : ∀ a b, Pres a → Pres b →
      (Meet S t (candRow R a) h (candRow R b) h ↔ nc a = nc b) := by
    intro a b ha hb
    rw [meet_cand_iff]
    constructor
    · rintro ⟨w', h1, h2⟩; rw [nc_eq a w' h1, nc_eq b w' h2]
    · intro e; exact ⟨nc a, nc_spec a ha, e ▸ nc_spec b hb⟩
  have hgood : ∀ c, (Meet S t (candRow R c) h (candRow R c) h ∧ ¬ Meet S t (candRow R c) h R h)
      ↔ good c := by
    intro c
    rw [meet_self_iff, meet_base_iff hS hA hP]
  constructor
  · rintro ⟨A, hAs, hlen, hgA, hpw, hcov⟩
    have hgA' : ∀ a ∈ A, good a := fun a ha => (hgood a).1 (hgA a ha)
    refine ⟨A, ?_, hlen, ?_, ?_⟩
    · have := hAs.filter (fun c => decide (good c))
      rwa [List.filter_eq_self.2 (fun a ha => by simpa using hgA' a ha)] at this
    · refine hpw.imp_of_mem fun {a b} ha hb hab => ?_
      exact fun e => hab ((hsame a b (hgA' a ha).1 (hgA' b hb).1).2 e)
    · intro c hcL
      obtain ⟨hc, hg⟩ := (hL c).1 hcL
      have hg' := (hgood c).2 hg
      obtain ⟨a, ha, hm⟩ := hcov c hc hg'.1 hg'.2
      exact ⟨a, ha, (hsame c a hg.1 (hgA' a ha).1).1 hm⟩
  · rintro ⟨A, hAs, hlen, hpw, hcov⟩
    have hgA' : ∀ a ∈ A, a ∈ degCands R ∧ good a := fun a ha => (hL a).1 (hAs.subset ha)
    refine ⟨A, hAs.trans List.filter_sublist, hlen, fun a ha => (hgood a).2 (hgA' a ha).2, ?_, ?_⟩
    · refine hpw.imp_of_mem fun {a b} ha hb hab => ?_
      exact fun hm => hab ((hsame a b (hgA' a ha).2.1 (hgA' b hb).2.1).1 hm)
    · intro c hc h1 h2
      have hg : good c := (hgood c).1 ⟨h1, h2⟩
      obtain ⟨a, ha, e⟩ := hcov c ((hL c).2 ⟨hc, hg⟩)
      exact ⟨a, ha, (hsame c a hg.1 (hgA' a ha).2.1).2 e⟩

/-! ## As a formula -/

variable {T : Type u} {m k : ℕ}

/-- Pairwise non-identification of a list of candidates. -/
def pairHFo (R : RowSet S) (ox : Option (Fin m)) : List (Cand S) → HF T m k
  | [] => hfTrue
  | a :: l => .and (bigAnd (l.map fun b => .neg (meetHFo (candRow R a) (candRow R b) ox ox)))
      (pairHFo R ox l)

/-- The degree formula: `deg = n` for the point of `R` at the height of `ox`. -/
def degHFo (R : RowSet S) (n : ℕ) (ox : Option (Fin m)) : HF T m k :=
  bigOr (((degCands R).sublists.filter fun A => decide (A.length = n)).map fun A =>
    bigAnd [bigAnd (A.map fun a => .and (meetHFo (candRow R a) (candRow R a) ox ox)
        (.neg (meetHFo (candRow R a) R ox ox))),
      pairHFo R ox A,
      bigAnd ((degCands R).map fun c => HF.imp (.and (meetHFo (candRow R c) (candRow R c) ox ox)
        (.neg (meetHFo (candRow R c) R ox ox))) (bigOr (A.map fun a =>
          meetHFo (candRow R c) (candRow R a) ox ox)))])

theorem candRow_wf {R : RowSet S} (hR : R.WF) (c : Cand S) : (candRow R c).WF :=
  nbrRow_wf hR _ _ _

theorem sat_pairHFo (hE : Embedded S t) {R : RowSet S} (hR : R.WF) (ox : Option (Fin m))
    {lo hi : T → R002.Claude3Fold.Aff} (ν : Fin m → T × ℤ) (V : Fin k → Set (T × ℤ))
    (A : List (Cand S)) :
    HF.Sat lo hi t (pairHFo R ox A) ν V ↔
      A.Pairwise (fun a b => ¬ Meet S t (candRow R a) (hgt ν ox) (candRow R b) (hgt ν ox)) := by
  induction A with
  | nil => simp [pairHFo]
  | cons a l ih =>
    rw [pairHFo, HF.Sat, ih, sat_bigAnd, List.pairwise_cons]
    refine and_congr ⟨fun H b hb => ?_, fun H φ hφ => ?_⟩ Iff.rfl
    · have := H _ (List.mem_map_of_mem hb)
      rwa [HF.Sat, sat_meetHFo hE (candRow_wf hR a) (candRow_wf hR b)] at this
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hφ
      rw [HF.Sat, sat_meetHFo hE (candRow_wf hR a) (candRow_wf hR b)]
      exact H b hb

/-- **Degree as a formula.** -/
theorem sat_degHFo (hE : Embedded S t) {R : RowSet S} (hR : R.WF) (n : ℕ)
    (ox : Option (Fin m)) {lo hi : T → R002.Claude3Fold.Aff} (ν : Fin m → T × ℤ)
    (V : Fin k → Set (T × ℤ)) (hS : R.Single t (hgt ν ox)) {P : ℤ × ℤ}
    (hA : R.At t (hgt ν ox) P) (hP : (S.chart R.f).Mem t P) :
    HF.Sat lo hi t (degHFo R n ox) ν V ↔ deg (graph S t) (pt S t R.f P hP) = n := by
  rw [← degEq_iff hE hS hA hP n, degHFo, sat_bigOr, DegEq]
  have hM : ∀ a b, HF.Sat lo hi t (meetHFo (T := T) (k := k) (candRow R a) (candRow R b) ox ox)
      ν V ↔ Meet S t (candRow R a) (hgt ν ox) (candRow R b) (hgt ν ox) := fun a b =>
    sat_meetHFo hE (candRow_wf hR a) (candRow_wf hR b) ox ox ν V
  have hMR : ∀ a, HF.Sat lo hi t (meetHFo (T := T) (k := k) (candRow R a) R ox ox) ν V ↔
      Meet S t (candRow R a) (hgt ν ox) R (hgt ν ox) := fun a =>
    sat_meetHFo hE (candRow_wf hR a) hR ox ox ν V
  simp only [List.mem_map, List.mem_filter, List.mem_sublists, decide_eq_true_eq]
  constructor
  · rintro ⟨φ, ⟨A, ⟨hAs, hlen⟩, rfl⟩, hφ⟩
    simp only [sat_bigAnd, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hφ
    obtain ⟨h1, h2, h3⟩ := hφ
    refine ⟨A, hAs, hlen, fun a ha => ?_, (sat_pairHFo hE hR ox ν V A).1 h2, fun c hc hp hs => ?_⟩
    · have := h1 _ (List.mem_map_of_mem ha)
      simp only [HF.Sat, hM, hMR] at this
      exact this
    · have := h3 _ (List.mem_map_of_mem hc)
      simp only [HF.sat_imp, HF.Sat, hM, hMR, sat_bigOr, List.mem_map] at this
      obtain ⟨_, ⟨a, ha, rfl⟩, hm⟩ := this ⟨hp, hs⟩
      exact ⟨a, ha, (hM c a).1 hm⟩
  · rintro ⟨A, hAs, hlen, h1, h2, h3⟩
    refine ⟨_, ⟨A, ⟨hAs, hlen⟩, rfl⟩, ?_⟩
    simp only [sat_bigAnd, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    refine ⟨fun φ hφ => ?_, (sat_pairHFo hE hR ox ν V A).2 h2, fun φ hφ => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hφ
      simp only [HF.Sat, hM, hMR]
      exact h1 a ha
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hφ
      simp only [HF.sat_imp, HF.Sat, hM, hMR, sat_bigOr, List.mem_map]
      rintro ⟨hp, hs⟩
      obtain ⟨a, ha, hm⟩ := h3 c hc hp hs
      exact ⟨_, ⟨a, ha, rfl⟩, (hM c a).2 hm⟩

end ClaudeChallenge2.Geo
