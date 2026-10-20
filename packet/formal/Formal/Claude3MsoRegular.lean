import Formal.Claude3MsoSyntax
import Formal.Claude3MsoAutomata

/-!
# Büchi–Elgot–Trakhtenbrot (MSO ⇒ regular)

Free variables are encoded in the extended alphabet
`Sym α m k = α × (Fin m → Bool) × (Fin k → Bool)`: first-order variable `j` is a track
with exactly one `true`, set variable `j` is an arbitrary track. `langOf φ` is the set of
well-formed encodings satisfying `φ`; it is regular by induction on `φ`
(atoms: explicit scanners; `¬`: complement inside the well-formed words;
`∧`: intersection; `∃`: letter-to-letter projection).
-/

namespace R002.Claude3Mso

open MSO

universe u

variable {α : Type u}

/-- Extended alphabet: a letter, first-order tracks and set tracks. -/
abbrev Sym (α : Type u) (m k : ℕ) := α × (Fin m → Bool) × (Fin k → Bool)

variable {m k : ℕ}

/-- first-order track `j` -/
def ftrack (j : Fin m) (b : Sym α m k) : Bool := b.2.1 j
/-- set track `j` -/
def strack (j : Fin k) (b : Sym α m k) : Bool := b.2.2 j

/-- underlying word -/
def word (u : List (Sym α m k)) : List α := u.map Prod.fst
/-- the set valuation read off the set tracks -/
def sets (u : List (Sym α m k)) : Fin k → Set ℕ := fun j => {i | Hit (strack j) u i}
/-- the first-order tracks encode the valuation `ν` (each track is the indicator of `ν j`) -/
def Valid (u : List (Sym α m k)) (ν : Fin m → ℕ) : Prop := ∀ j i, Hit (ftrack j) u i ↔ i = ν j

/-- The language of encodings of models of `φ`. -/
def langOf (φ : MSO α m k) : Language (Sym α m k) :=
  {u | ∃ ν, Valid u ν ∧ Sat (word u) φ ν (sets u)}

/-- Well-formed encodings. -/
def validL : Language (Sym α m k) := {u | ∃ ν, Valid u ν}

theorem mem_langOf {φ : MSO α m k} {u : List (Sym α m k)} :
    u ∈ langOf φ ↔ ∃ ν, Valid u ν ∧ Sat (word u) φ ν (sets u) := Iff.rfl

theorem mem_validL {u : List (Sym α m k)} : u ∈ validL ↔ ∃ ν, Valid u ν := Iff.rfl

theorem mem_compl' {β : Type*} {L : Language β} {u : List β} : u ∈ Lᶜ ↔ u ∉ L := Iff.rfl

theorem Valid.unique {u : List (Sym α m k)} {ν ν' : Fin m → ℕ} (h : Valid u ν)
    (h' : Valid u ν') : ν = ν' := by
  funext j
  exact ((h j (ν' j)).1 ((h' j (ν' j)).2 rfl)).symm

theorem Valid.lt {u : List (Sym α m k)} {ν : Fin m → ℕ} (h : Valid u ν) (j : Fin m) :
    ν j < u.length :=
  ((h j (ν j)).2 rfl).lt

theorem mem_langOf_of_valid {φ : MSO α m k} {u : List (Sym α m k)} {ν : Fin m → ℕ}
    (hν : Valid u ν) : u ∈ langOf φ ↔ Sat (word u) φ ν (sets u) := by
  constructor
  · rintro ⟨ν', hν', hs⟩
    rwa [hν.unique hν']
  · exact fun hs => ⟨ν, hν, hs⟩

theorem langOf_eq_of {φ : MSO α m k} (L : Language (Sym α m k))
    (h : ∀ u ν, Valid u ν → (Sat (word u) φ ν (sets u) ↔ u ∈ L)) :
    langOf φ = validL ⊓ L := by
  refine Language.ext fun u => ?_
  rw [Language.mem_inf]
  constructor
  · rintro ⟨ν, hν, hs⟩
    exact ⟨⟨ν, hν⟩, (h u ν hν).1 hs⟩
  · rintro ⟨⟨ν, hν⟩, hL⟩
    exact ⟨ν, hν, (h u ν hν).2 hL⟩

theorem validL_eq : (validL : Language (Sym α m k)) =
    forallFin (fun j => exSat (ftrack j) ⊓ (exLt (ftrack j) (ftrack j))ᶜ) := by
  refine Language.ext fun u => ?_
  rw [mem_forallFin, mem_validL]
  simp only [Language.mem_inf, mem_compl', mem_exSat, mem_exLt]
  constructor
  · rintro ⟨ν, hν⟩ j
    refine ⟨⟨ν j, (hν j _).2 rfl⟩, ?_⟩
    rintro ⟨i, i', hii', hi, hi'⟩
    rw [hν] at hi hi'
    omega
  · intro h
    choose ν hν using fun j => (h j).1
    refine ⟨ν, fun j i => ⟨fun hi => ?_, fun e => e ▸ hν j⟩⟩
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact (h j).2 ⟨i, ν j, hlt, hi, hν j⟩
    · exact (h j).2 ⟨ν j, i, hlt, hν j, hi⟩

theorem isRegular_validL : (validL : Language (Sym α m k)).IsRegular := by
  rw [validL_eq]
  exact isRegular_forallFin _ fun j =>
    (isRegular_exSat _).inf (isRegular_exLt _ _).compl

/-! ## Projections of the alphabet -/

/-- forget first-order track `0` -/
def dropF (b : Sym α (m + 1) k) : Sym α m k := (b.1, Fin.tail b.2.1, b.2.2)
/-- forget set track `0` -/
def dropS (b : Sym α m (k + 1)) : Sym α m k := (b.1, b.2.1, Fin.tail b.2.2)

section drop
variable {v : List (Sym α (m + 1) k)} {v' : List (Sym α m (k + 1))}

theorem word_map_dropF : word (v.map dropF) = word v := by
  simp [word, List.map_map, Function.comp_def, dropF]

theorem sets_map_dropF : sets (v.map dropF) = sets v := by
  funext j; ext i
  simp only [sets, Set.mem_ofPred_eq, hit_map]
  rfl

theorem hit_ftrack_map_dropF {j : Fin m} {i : ℕ} :
    Hit (ftrack j) (v.map dropF) i ↔ Hit (ftrack j.succ) v i := by
  rw [hit_map]; rfl

theorem word_map_dropS : word (v'.map dropS) = word v' := by
  simp [word, List.map_map, Function.comp_def, dropS]

theorem sets_map_dropS : sets (v'.map dropS) = Fin.tail (sets v') := by
  funext j; ext i
  simp only [sets, Set.mem_ofPred_eq, hit_map, Fin.tail]
  rfl

theorem valid_map_dropS {ν : Fin m → ℕ} : Valid (v'.map dropS) ν ↔ Valid v' ν := by
  simp only [Valid, hit_map]
  rfl

end drop

theorem langOf_exF (φ : MSO α (m + 1) k) : langOf (.exF φ) = imageMap dropF (langOf φ) := by
  refine Language.ext fun u => ?_
  rw [mem_imageMap]
  constructor
  · rintro ⟨ν, hν, x, hx, hs⟩
    have hx' : x < u.length := by simpa [word] using hx
    let u' : List (Sym α (m + 1) k) :=
      u.mapIdx (fun i b => (b.1, (Fin.cons (decide (i = x)) b.2.1 : Fin (m + 1) → Bool), b.2.2))
    have hu' : u'.map dropF = u := by
      apply List.ext_getElem?
      intro i
      simp only [u', List.getElem?_map, List.getElem?_mapIdx, Option.map_map]
      cases u[i]? <;> simp [dropF]
    refine ⟨u', ⟨Fin.cons x ν, ?_, ?_⟩, hu'⟩
    · intro j i
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · simp only [u', hit_mapIdx, ftrack, Fin.cons_zero, decide_eq_true_eq]
        constructor
        · rintro ⟨b, -, h⟩; exact h
        · rintro rfl
          exact ⟨_, List.getElem?_eq_getElem hx', rfl⟩
      · rw [← hit_ftrack_map_dropF, hu', Fin.cons_succ]
        exact hν j i
    · rw [← word_map_dropF, ← sets_map_dropF, hu']
      exact hs
  · rintro ⟨u', ⟨ν', hν', hs⟩, rfl⟩
    refine ⟨Fin.tail ν', fun j i => ?_, ν' 0, ?_, ?_⟩
    · rw [hit_ftrack_map_dropF]; exact hν' j.succ i
    · simpa [word] using hν'.lt 0
    · rw [word_map_dropF, sets_map_dropF, Fin.cons_self_tail]
      exact hs

theorem langOf_exS (φ : MSO α m (k + 1)) : langOf (.exS φ) = imageMap dropS (langOf φ) := by
  classical
  refine Language.ext fun u => ?_
  rw [mem_imageMap]
  constructor
  · rintro ⟨ν, hν, X, hX, hs⟩
    let u' : List (Sym α m (k + 1)) :=
      u.mapIdx (fun i b => (b.1, b.2.1, (Fin.cons (decide (i ∈ X)) b.2.2 : Fin (k + 1) → Bool)))
    have hu' : u'.map dropS = u := by
      apply List.ext_getElem?
      intro i
      simp only [u', List.getElem?_map, List.getElem?_mapIdx, Option.map_map]
      cases u[i]? <;> simp [dropS]
    have hsets : sets u' = Fin.cons X (sets u) := by
      funext j
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · ext i
        simp only [sets, Set.mem_ofPred_eq, u', hit_mapIdx, strack, Fin.cons_zero,
          decide_eq_true_eq]
        constructor
        · rintro ⟨b, -, h⟩; exact h
        · intro hi
          have : i < u.length := by simpa [word] using hX hi
          exact ⟨_, List.getElem?_eq_getElem this, hi⟩
      · rw [Fin.cons_succ, ← hu', sets_map_dropS]
        rfl
    refine ⟨u', ⟨ν, ?_, ?_⟩, hu'⟩
    · rw [← valid_map_dropS, hu']; exact hν
    · rw [← word_map_dropS, hu', hsets]; exact hs
  · rintro ⟨u', ⟨ν, hν, hs⟩, rfl⟩
    refine ⟨ν, valid_map_dropS.2 hν, sets u' 0, ?_, ?_⟩
    · intro i hi
      simpa [word_map_dropS, word] using (show Hit _ u' i from hi).lt
    · rw [word_map_dropS, sets_map_dropS, Fin.cons_self_tail]
      exact hs

/-- **Main lemma.** For every formula, the language of encodings of its models is regular. -/
theorem isRegular_langOf : ∀ {m k : ℕ} (φ : MSO α m k), (langOf φ).IsRegular := by
  classical
  intro m k φ
  induction φ with
  | lt x y =>
    rw [langOf_eq_of (exLt (ftrack x) (ftrack y))]
    · exact isRegular_validL.inf (isRegular_exLt _ _)
    intro u ν hν
    simp only [Sat, mem_exLt]
    exact ⟨fun h => ⟨_, _, h, (hν x _).2 rfl, (hν y _).2 rfl⟩,
      fun ⟨i, j, h, hi, hj⟩ => (hν x i).1 hi ▸ (hν y j).1 hj ▸ h⟩
  | eq x y =>
    rw [langOf_eq_of (exSat (fun b => ftrack x b && ftrack y b))]
    · exact isRegular_validL.inf (isRegular_exSat _)
    intro u ν hν
    simp only [Sat, mem_exSat, hit_and]
    exact ⟨fun h => ⟨_, (hν x _).2 rfl, (hν y _).2 h⟩,
      fun ⟨i, hi, hj⟩ => ((hν x i).1 hi).symm.trans ((hν y i).1 hj)⟩
  | succ x y =>
    rw [langOf_eq_of (exAdj (ftrack x) (ftrack y))]
    · exact isRegular_validL.inf (isRegular_exAdj _ _)
    intro u ν hν
    simp only [Sat, mem_exAdj]
    exact ⟨fun h => ⟨_, (hν x _).2 rfl, (hν y _).2 h.symm⟩,
      fun ⟨i, hi, hj⟩ => ((hν y _).1 hj).symm.trans (by rw [(hν x i).1 hi])⟩
  | mem x X =>
    rw [langOf_eq_of (exSat (fun b => ftrack x b && strack X b))]
    · exact isRegular_validL.inf (isRegular_exSat _)
    intro u ν hν
    simp only [Sat, mem_exSat, hit_and, sets, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨_, (hν x _).2 rfl, h⟩, fun ⟨i, hi, hj⟩ => (hν x i).1 hi ▸ hj⟩
  | lab a x =>
    rw [langOf_eq_of (exSat (fun b => ftrack x b && decide (b.1 = a)))]
    · exact isRegular_validL.inf (isRegular_exSat _)
    intro u ν hν
    have hw : ∀ i, (word u)[i]? = some a ↔ Hit (fun b : Sym α _ _ => decide (b.1 = a)) u i := by
      intro i
      simp only [word, List.getElem?_map, Option.map_eq_some_iff, Hit, decide_eq_true_eq]
    simp only [Sat, mem_exSat, hit_and, hw]
    exact ⟨fun h => ⟨_, (hν x _).2 rfl, h⟩, fun ⟨i, hi, hj⟩ => (hν x i).1 hi ▸ hj⟩
  | neg φ ih =>
    rw [langOf_eq_of (langOf φ)ᶜ]
    · exact isRegular_validL.inf ih.compl
    intro u ν hν
    rw [mem_compl', mem_langOf_of_valid hν]
    rfl
  | and φ ψ ihφ ihψ =>
    rw [langOf_eq_of (langOf φ ⊓ langOf ψ)]
    · exact isRegular_validL.inf (ihφ.inf ihψ)
    intro u ν hν
    rw [Language.mem_inf, mem_langOf_of_valid hν, mem_langOf_of_valid hν]
    rfl
  | exF φ ih =>
    rw [langOf_exF]
    exact isRegular_imageMap ih _
  | exS φ ih =>
    rw [langOf_exS]
    exact isRegular_imageMap ih _

/-! ## Sentences -/

/-- letters of `α` as letters of the extended alphabet with no tracks -/
def embed (a : α) : Sym α 0 0 := (a, fun i => i.elim0, fun i => i.elim0)

theorem models_iff_mem (w : List α) (φ : Sentence α) :
    Models w φ ↔ w.map embed ∈ langOf φ := by
  have hw : word (w.map embed) = w := by simp [word, List.map_map, Function.comp_def, embed]
  have hv : Valid (w.map embed) (fun i => i.elim0) := fun j => j.elim0
  rw [mem_langOf_of_valid hv, hw]
  have hs : sets (w.map embed) = fun i => i.elim0 := funext fun i => i.elim0
  rw [hs]
  rfl

/-- The language of a sentence. -/
def modelsLang (φ : Sentence α) : Language α := {w | Models w φ}

theorem mem_modelsLang {φ : Sentence α} {w : List α} : w ∈ modelsLang φ ↔ Models w φ := Iff.rfl

/-- **Büchi–Elgot–Trakhtenbrot** (MSO-definable ⇒ regular): the set of finite words
satisfying an MSO sentence is a regular language. -/
theorem isRegular_modelsLang (φ : Sentence α) : (modelsLang φ).IsRegular := by
  have : modelsLang φ = preimageMap embed (langOf φ) :=
    Language.ext fun w => (models_iff_mem w φ).trans mem_preimageMap.symm
  rw [this]
  exact isRegular_preimageMap (isRegular_langOf φ) _

/-- Explicit DFA form of `isRegular_modelsLang`. -/
theorem exists_dfa_models (φ : Sentence α) :
    ∃ (σ : Type) (_ : Fintype σ) (M : DFA α σ), ∀ w, w ∈ M.accepts ↔ Models w φ := by
  obtain ⟨σ, hσ, M, hM⟩ := isRegular_modelsLang φ
  exact ⟨σ, hσ, M, fun w => by rw [hM]; rfl⟩

end R002.Claude3Mso
