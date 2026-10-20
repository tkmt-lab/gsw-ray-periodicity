import Mathlib.Computability.NFA

/-!
# Closure properties and basic regular languages for the MSO-to-automata proof

* `isRegular_of_snoc`: a language recognised by a finite "snoc-summary" is regular.
* `isRegular_imageMap`: regular languages are closed under letter-to-letter images
  (projection), via an NFA and the subset construction.
* `isRegular_preimageMap`: closure under letter-to-letter preimages (`DFA.comap`).
* `isRegular_forall_fin`: closure under finite intersections indexed by `Fin m`.
* the three scanning languages `exSat`, `exLt`, `exAdj` are regular.
-/

namespace R002.Claude3Mso

universe u v

variable {β : Type u} {γ : Type v}

/-- `Hit p u i`: position `i` of `u` exists and its letter satisfies `p`. -/
def Hit (p : β → Bool) (u : List β) (i : ℕ) : Prop := ∃ b, u[i]? = some b ∧ p b = true

theorem Hit.lt {p : β → Bool} {u : List β} {i : ℕ} (h : Hit p u i) : i < u.length := by
  obtain ⟨b, hb, -⟩ := h
  exact (List.getElem?_eq_some_iff.1 hb).1

theorem hit_snoc {p : β → Bool} {u : List β} {b : β} {i : ℕ} :
    Hit p (u ++ [b]) i ↔ Hit p u i ∨ (i = u.length ∧ p b = true) := by
  unfold Hit
  rcases lt_trichotomy i u.length with h | h | h
  · simp [List.getElem?_append_left h, h.ne]
  · subst h; simp
  · have h1 : u[i]? = none := List.getElem?_eq_none h.le
    have h2 : (u ++ [b])[i]? = none := List.getElem?_eq_none (by simp; omega)
    simp [h1, h2, h.ne']

@[simp] theorem hit_nil {p : β → Bool} {i : ℕ} : ¬ Hit p ([] : List β) i := by
  simp [Hit]

theorem hit_map {p : γ → Bool} {f : β → γ} {u : List β} {i : ℕ} :
    Hit p (u.map f) i ↔ Hit (fun b => p (f b)) u i := by
  simp [Hit]

theorem hit_mapIdx {p : γ → Bool} {g : ℕ → β → γ} {u : List β} {i : ℕ} :
    Hit p (u.mapIdx g) i ↔ ∃ b, u[i]? = some b ∧ p (g i b) = true := by
  simp [Hit]

theorem hit_and {p q : β → Bool} {u : List β} {i : ℕ} :
    Hit (fun b => p b && q b) u i ↔ Hit p u i ∧ Hit q u i := by
  unfold Hit
  constructor
  · rintro ⟨b, hb, h⟩
    simp only [Bool.and_eq_true] at h
    exact ⟨⟨b, hb, h.1⟩, ⟨b, hb, h.2⟩⟩
  · rintro ⟨⟨b, hb, h1⟩, ⟨c, hc, h2⟩⟩
    rw [hb] at hc
    cases hc
    exact ⟨b, hb, by simp [h1, h2]⟩

/-! ## Generic regularity from a finite snoc-summary -/

theorem isRegular_of_snoc {σ : Type} [Finite σ] (L : Language β) (f : List β → σ)
    (step : σ → β → σ) (A : Set σ) (hstep : ∀ u b, f (u ++ [b]) = step (f u) b)
    (hacc : ∀ u, u ∈ L ↔ f u ∈ A) : L.IsRegular := by
  refine ⟨σ, Fintype.ofFinite σ, ⟨step, f [], A⟩, ?_⟩
  have key : ∀ u, (⟨step, f [], A⟩ : DFA β σ).eval u = f u := by
    intro u
    induction u using List.reverseRecOn with
    | nil => rfl
    | append_singleton u b ih => rw [DFA.eval_append_singleton, ih, hstep]
  refine Language.ext fun u => ?_
  rw [DFA.mem_accepts, key, hacc]

theorem isRegular_univ : (⊤ : Language β).IsRegular :=
  isRegular_of_snoc ⊤ (fun _ => ()) (fun _ _ => ()) Set.univ (fun _ _ => rfl)
    (fun _ => by simp only [Set.mem_univ, iff_true]; trivial)

/-! ## Projection and preimage -/

/-- Image of a language under a letter-to-letter map. -/
def imageMap (f : β → γ) (L : Language β) : Language γ := {v | ∃ u ∈ L, u.map f = v}

theorem mem_imageMap {f : β → γ} {L : Language β} {v : List γ} :
    v ∈ imageMap f L ↔ ∃ u ∈ L, u.map f = v := Iff.rfl

/-- Preimage of a language under a letter-to-letter map. -/
def preimageMap (f : γ → β) (L : Language β) : Language γ := {v | v.map f ∈ L}

theorem mem_preimageMap {f : γ → β} {L : Language β} {v : List γ} :
    v ∈ preimageMap f L ↔ v.map f ∈ L := Iff.rfl

/-- Regular languages are closed under letter-to-letter images (projection). -/
theorem isRegular_imageMap {L : Language β} (h : L.IsRegular) (f : β → γ) :
    (imageMap f L).IsRegular := by
  obtain ⟨σ, _, M, rfl⟩ := h
  classical
  let N : NFA γ σ := ⟨fun s c => {t | ∃ b, f b = c ∧ M.step s b = t}, {M.start}, M.accept⟩
  have key : ∀ (v : List γ) (S : Set σ) (t : σ),
      t ∈ N.evalFrom S v ↔ ∃ s ∈ S, ∃ u : List β, u.map f = v ∧ M.evalFrom s u = t := by
    intro v
    induction v with
    | nil =>
      intro S t
      simp only [NFA.evalFrom_nil, List.map_eq_nil_iff, exists_eq_left, DFA.evalFrom_nil,
        exists_eq_right]
    | cons c v ih =>
      intro S t
      rw [NFA.evalFrom_cons, ih]
      constructor
      · rintro ⟨s', hs', u, rfl, rfl⟩
        obtain ⟨s, hs, b, hb, rfl⟩ := NFA.mem_stepSet.1 hs'
        exact ⟨s, hs, b :: u, by simp [hb], by simp [DFA.evalFrom_cons]⟩
      · rintro ⟨s, hs, u, hu, rfl⟩
        cases u with
        | nil => simp at hu
        | cons b u =>
          simp only [List.map_cons, List.cons.injEq] at hu
          obtain ⟨rfl, rfl⟩ := hu
          exact ⟨M.step s b, NFA.mem_stepSet.2 ⟨s, hs, b, rfl, rfl⟩, u, rfl, rfl⟩
  have hN : N.accepts = imageMap f M.accepts := by
    refine Language.ext fun v => ?_
    rw [NFA.mem_accepts, mem_imageMap]
    constructor
    · rintro ⟨t, ht, hv⟩
      obtain ⟨s, hs, u, hu, rfl⟩ := (key v _ t).1 hv
      rw [Set.mem_singleton_iff] at hs
      subst hs
      exact ⟨u, ht, hu⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨M.eval u, hu, (key _ _ _).2 ⟨M.start, rfl, u, rfl, rfl⟩⟩
  exact ⟨Set σ, inferInstance, N.toDFA, by rw [NFA.toDFA_correct, hN]⟩

/-- Regular languages are closed under letter-to-letter preimages. -/
theorem isRegular_preimageMap {L : Language β} (h : L.IsRegular) (f : γ → β) :
    (preimageMap f L).IsRegular := by
  obtain ⟨σ, _, M, rfl⟩ := h
  exact ⟨σ, inferInstance, M.comap f, by rw [DFA.accepts_comap]; rfl⟩

/-- Intersection of a family indexed by `Fin m`. -/
def forallFin {m : ℕ} (L : Fin m → Language β) : Language β := {u | ∀ j, u ∈ L j}

theorem mem_forallFin {m : ℕ} {L : Fin m → Language β} {u : List β} :
    u ∈ forallFin L ↔ ∀ j, u ∈ L j := Iff.rfl

/-- Finite intersections indexed by `Fin m`. -/
theorem isRegular_forallFin {m : ℕ} (L : Fin m → Language β) (h : ∀ j, (L j).IsRegular) :
    (forallFin L).IsRegular := by
  induction m with
  | zero =>
    convert (isRegular_univ : (⊤ : Language β).IsRegular)
    refine Language.ext fun u => ?_
    rw [mem_forallFin]
    simp only [IsEmpty.forall_iff]
    exact ⟨fun _ => trivial, fun _ => trivial⟩
  | succ m ih =>
    have e : forallFin L = L 0 ⊓ forallFin (fun j : Fin m => L j.succ) := by
      refine Language.ext fun u => ?_
      rw [Language.mem_inf, mem_forallFin, mem_forallFin]
      exact Fin.forall_fin_succ
    rw [e]
    exact (h 0).inf (ih _ fun j => h j.succ)

/-! ## Scanning languages -/

/-- Some position satisfies `p`. -/
def exSat (p : β → Bool) : Language β := {u | ∃ i, Hit p u i}

/-- Some position satisfying `p` is strictly before some position satisfying `q`. -/
def exLt (p q : β → Bool) : Language β := {u | ∃ i j, i < j ∧ Hit p u i ∧ Hit q u j}

/-- Some position satisfying `p` is immediately followed by one satisfying `q`. -/
def exAdj (p q : β → Bool) : Language β := {u | ∃ i, Hit p u i ∧ Hit q u (i + 1)}

/-- The last letter satisfies `p`. -/
def lastSat (p : β → Bool) : Language β := {u | ∃ i, i + 1 = u.length ∧ Hit p u i}

section
variable {p q : β → Bool} {u : List β} {b : β}

theorem mem_exSat : u ∈ exSat p ↔ ∃ i, Hit p u i := Iff.rfl
theorem mem_exLt : u ∈ exLt p q ↔ ∃ i j, i < j ∧ Hit p u i ∧ Hit q u j := Iff.rfl
theorem mem_exAdj : u ∈ exAdj p q ↔ ∃ i, Hit p u i ∧ Hit q u (i + 1) := Iff.rfl
theorem mem_lastSat : u ∈ lastSat p ↔ ∃ i, i + 1 = u.length ∧ Hit p u i := Iff.rfl

theorem exSat_snoc : u ++ [b] ∈ exSat p ↔ u ∈ exSat p ∨ p b = true := by
  simp only [mem_exSat]
  constructor
  · rintro ⟨i, hi⟩
    rcases hit_snoc.1 hi with h | h
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr h.2
  · rintro (⟨i, hi⟩ | h)
    · exact ⟨i, hit_snoc.2 (Or.inl hi)⟩
    · exact ⟨u.length, hit_snoc.2 (Or.inr ⟨rfl, h⟩)⟩

theorem exLt_snoc : u ++ [b] ∈ exLt p q ↔ u ∈ exLt p q ∨ (u ∈ exSat p ∧ q b = true) := by
  simp only [mem_exLt, mem_exSat]
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    rcases hit_snoc.1 hj with hj' | ⟨rfl, hq⟩
    · rcases hit_snoc.1 hi with hi' | ⟨rfl, -⟩
      · exact Or.inl ⟨i, j, hij, hi', hj'⟩
      · exact absurd hj'.lt (by omega)
    · rcases hit_snoc.1 hi with hi' | ⟨rfl, -⟩
      · exact Or.inr ⟨⟨i, hi'⟩, hq⟩
      · omega
  · rintro (⟨i, j, hij, hi, hj⟩ | ⟨⟨i, hi⟩, hq⟩)
    · exact ⟨i, j, hij, hit_snoc.2 (Or.inl hi), hit_snoc.2 (Or.inl hj)⟩
    · exact ⟨i, u.length, hi.lt, hit_snoc.2 (Or.inl hi), hit_snoc.2 (Or.inr ⟨rfl, hq⟩)⟩

theorem lastSat_snoc : u ++ [b] ∈ lastSat p ↔ p b = true := by
  simp only [mem_lastSat, List.length_append, List.length_singleton,
    Nat.add_right_cancel_iff]
  constructor
  · rintro ⟨i, rfl, hi⟩
    rcases hit_snoc.1 hi with h | h
    · exact absurd h.lt (lt_irrefl _)
    · exact h.2
  · intro h
    exact ⟨u.length, rfl, hit_snoc.2 (Or.inr ⟨rfl, h⟩)⟩

theorem exAdj_snoc : u ++ [b] ∈ exAdj p q ↔ u ∈ exAdj p q ∨ (u ∈ lastSat p ∧ q b = true) := by
  simp only [mem_exAdj, mem_lastSat]
  constructor
  · rintro ⟨i, hi, hj⟩
    rcases hit_snoc.1 hj with hj' | ⟨h, hq⟩
    · rcases hit_snoc.1 hi with hi' | ⟨rfl, -⟩
      · exact Or.inl ⟨i, hi', hj'⟩
      · exact absurd hj'.lt (by omega)
    · rcases hit_snoc.1 hi with hi' | ⟨rfl, -⟩
      · exact Or.inr ⟨⟨i, h, hi'⟩, hq⟩
      · omega
  · rintro (⟨i, hi, hj⟩ | ⟨⟨i, h, hi⟩, hq⟩)
    · exact ⟨i, hit_snoc.2 (Or.inl hi), hit_snoc.2 (Or.inl hj)⟩
    · exact ⟨i, hit_snoc.2 (Or.inl hi), hit_snoc.2 (Or.inr ⟨h, hq⟩)⟩

end

theorem isRegular_exSat (p : β → Bool) : (exSat p).IsRegular := by
  classical
  refine isRegular_of_snoc _ (fun u => decide (u ∈ exSat p)) (fun s b => s || p b) {true}
    (fun u b => ?_) (fun u => by simp)
  rw [Bool.eq_iff_iff]
  simp [exSat_snoc]

theorem isRegular_exLt (p q : β → Bool) : (exLt p q).IsRegular := by
  classical
  refine isRegular_of_snoc _ (fun u => (decide (u ∈ exSat p), decide (u ∈ exLt p q)))
    (fun s b => (s.1 || p b, s.2 || (s.1 && q b))) {s | s.2 = true}
    (fun u b => ?_) (fun u => by simp)
  refine Prod.ext ?_ ?_
  · rw [Bool.eq_iff_iff]; simp [exSat_snoc]
  · rw [Bool.eq_iff_iff]; simp [exLt_snoc]

theorem isRegular_exAdj (p q : β → Bool) : (exAdj p q).IsRegular := by
  classical
  refine isRegular_of_snoc _ (fun u => (decide (u ∈ lastSat p), decide (u ∈ exAdj p q)))
    (fun s b => (p b, s.2 || (s.1 && q b))) {s | s.2 = true}
    (fun u b => ?_) (fun u => by simp)
  refine Prod.ext ?_ ?_
  · rw [Bool.eq_iff_iff]; simp [lastSat_snoc]
  · rw [Bool.eq_iff_iff]; simp [exAdj_snoc]

end R002.Claude3Mso
