import Formal.Claude3MsoLenMod

/-!
# Eventual MSO definability over unary words

`EvDef P` says that the family of predicates `P n ν V` (`n` the word length, `ν` a valuation
of position variables, `V` of set variables) agrees, for all large `n` and all valuations by
positions `< n`, with the semantics of one fixed MSO formula over the unary word of length `n`.

* closure: `neg`, `and`, `or`, `exF`, `exS`, `exSN` (a block of `N` set quantifiers),
  `exists_fintype` (finite disjunction), `congr`, `of_eventually_iff` (eventually constant).
* exact position formulas: `posLe d x` (`x ≤ d`), `posLeR d x` (`n ≤ x + d + 1`),
  `sumLe d x y` (`x + y ≤ d`), `sumLeR d x y` (`2n ≤ x + y + d + 2`),
  `posMod q ρ x` (`x % q = ρ`).
-/

namespace R002.Claude3Mso

open MSO

/-- the unary word of length `n` -/
abbrev uw (n : ℕ) : List Unit := List.replicate n ()

@[simp] theorem uw_length (n : ℕ) : (uw n).length = n := List.length_replicate

/-- Eventual MSO definability of a family of predicates on positions and sets of positions. -/
def EvDef {m k : ℕ} (P : ℕ → (Fin m → ℕ) → (Fin k → Set ℕ) → Prop) : Prop :=
  ∃ (ψ : MSO Unit m k) (N : ℕ), ∀ n, N ≤ n → ∀ ν : Fin m → ℕ, (∀ i, ν i < n) →
    ∀ V : Fin k → Set ℕ, (Sat (uw n) ψ ν V ↔ P n ν V)

namespace EvDef

variable {m k : ℕ} {P Q : ℕ → (Fin m → ℕ) → (Fin k → Set ℕ) → Prop}

theorem of_exact (ψ : MSO Unit m k)
    (h : ∀ n, ∀ ν : Fin m → ℕ, (∀ i, ν i < n) → ∀ V, (Sat (uw n) ψ ν V ↔ P n ν V)) :
    EvDef P :=
  ⟨ψ, 0, fun n _ ν hν V => h n ν hν V⟩

theorem congr (h : EvDef P) (N : ℕ)
    (hPQ : ∀ n, N ≤ n → ∀ ν : Fin m → ℕ, (∀ i, ν i < n) → ∀ V, (P n ν V ↔ Q n ν V)) :
    EvDef Q := by
  obtain ⟨ψ, N', hψ⟩ := h
  exact ⟨ψ, max N N', fun n hn ν hν V =>
    (hψ n (le_of_max_le_right hn) ν hν V).trans (hPQ n (le_of_max_le_left hn) ν hν V)⟩

theorem of_eventually_iff (p : Prop) (N : ℕ)
    (h : ∀ n, N ≤ n → ∀ ν : Fin m → ℕ, (∀ i, ν i < n) → ∀ V, (P n ν V ↔ p)) : EvDef P := by
  classical
  by_cases hp : p
  · exact ⟨tt, N, fun n hn ν hν V => by simp only [sat_tt, true_iff]; exact (h n hn ν hν V).2 hp⟩
  · exact ⟨ff, N, fun n hn ν hν V => by
      simp only [sat_ff, false_iff]; exact fun hP => hp ((h n hn ν hν V).1 hP)⟩

theorem const (p : Prop) : EvDef (fun _ _ _ => p : ℕ → (Fin m → ℕ) → (Fin k → Set ℕ) → Prop) :=
  of_eventually_iff p 0 fun _ _ _ _ _ => Iff.rfl

theorem neg (h : EvDef P) : EvDef (fun n ν V => ¬ P n ν V) := by
  obtain ⟨ψ, N, hψ⟩ := h
  exact ⟨.neg ψ, N, fun n hn ν hν V => by simp only [Sat]; rw [hψ n hn ν hν V]⟩

theorem and (hP : EvDef P) (hQ : EvDef Q) : EvDef (fun n ν V => P n ν V ∧ Q n ν V) := by
  obtain ⟨ψ, N, hψ⟩ := hP
  obtain ⟨χ, M, hχ⟩ := hQ
  exact ⟨.and ψ χ, max N M, fun n hn ν hν V => by
    simp only [Sat]
    rw [hψ n (le_of_max_le_left hn) ν hν V, hχ n (le_of_max_le_right hn) ν hν V]⟩

theorem or (hP : EvDef P) (hQ : EvDef Q) : EvDef (fun n ν V => P n ν V ∨ Q n ν V) := by
  obtain ⟨ψ, N, hψ⟩ := hP
  obtain ⟨χ, M, hχ⟩ := hQ
  exact ⟨MSO.or ψ χ, max N M, fun n hn ν hν V => by
    simp only [sat_or]
    rw [hψ n (le_of_max_le_left hn) ν hν V, hχ n (le_of_max_le_right hn) ν hν V]⟩

theorem cons_lt {n x : ℕ} {ν : Fin m → ℕ} (hx : x < n) (hν : ∀ i, ν i < n) :
    ∀ i, (Fin.cons x ν : Fin (m + 1) → ℕ) i < n := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa using hx
  · simpa using hν i

theorem exF {P : ℕ → (Fin (m + 1) → ℕ) → (Fin k → Set ℕ) → Prop} (h : EvDef P) :
    EvDef (fun n ν V => ∃ x, x < n ∧ P n (Fin.cons x ν) V) := by
  obtain ⟨ψ, N, hψ⟩ := h
  refine ⟨.exF ψ, N, fun n hn ν hν V => ?_⟩
  simp only [Sat, uw_length]
  exact exists_congr fun x => and_congr_right fun hx => hψ n hn _ (cons_lt hx hν) V

theorem exS {P : ℕ → (Fin m → ℕ) → (Fin (k + 1) → Set ℕ) → Prop} (h : EvDef P) :
    EvDef (fun n ν V => ∃ X : Set ℕ, X ⊆ {i | i < n} ∧ P n ν (Fin.cons X V)) := by
  obtain ⟨ψ, N, hψ⟩ := h
  refine ⟨.exS ψ, N, fun n hn ν hν V => ?_⟩
  simp only [Sat, uw_length]
  exact exists_congr fun X => and_congr_right fun _ => hψ n hn ν hν _

/-- Finite disjunctions. -/
theorem exists_fintype {ι : Type*} [Finite ι]
    {P : ι → ℕ → (Fin m → ℕ) → (Fin k → Set ℕ) → Prop} (h : ∀ i, EvDef (P i)) :
    EvDef (fun n ν V => ∃ i, P i n ν V) := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, EvDef (fun n ν V => ∃ i ∈ s, P i n ν V) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact of_eventually_iff False 0 fun _ _ _ _ _ => by simp
    | insert a s _ ih =>
      exact ((h a).or ih).congr 0 fun n _ ν _ V => by simp
  exact (key Finset.univ).congr 0 fun n _ ν _ V => by simp

/-! ### Blocks of set quantifiers -/

/-- `ext N W V`: the set valuation with `W 0, …, W (N-1)` at indices `0, …, N-1` followed by
`V` (shifted by `N`). -/
def ext {K : ℕ} : (N : ℕ) → (Fin N → Set ℕ) → (Fin K → Set ℕ) → Fin (K + N) → Set ℕ
  | 0, _, V => V
  | N + 1, W, V => Fin.cons (W 0) (ext N (Fin.tail W) V)

/-- index of the `c`-th new set variable -/
def idxW {K N : ℕ} (c : Fin N) : Fin (K + N) := ⟨c.val, by omega⟩
/-- index of the old set variable `i` -/
def idxV {K N : ℕ} (i : Fin K) : Fin (K + N) := ⟨N + i.val, by omega⟩

theorem ext_idxW {K : ℕ} : ∀ (N : ℕ) (W : Fin N → Set ℕ) (V : Fin K → Set ℕ) (c : Fin N),
    ext N W V (idxW c) = W c := by
  intro N
  induction N with
  | zero => intro W V c; exact c.elim0
  | succ N ih =>
    intro W V c
    rcases c with ⟨c, hc⟩
    cases c with
    | zero => rfl
    | succ c =>
      have e : (idxW (K := K) (⟨c + 1, hc⟩ : Fin (N + 1)) : Fin (K + (N + 1))) =
          Fin.succ (idxW (K := K) (⟨c, by omega⟩ : Fin N)) := rfl
      simp only [ext]
      rw [e, Fin.cons_succ, ih]
      rfl

theorem ext_idxV {K : ℕ} : ∀ (N : ℕ) (W : Fin N → Set ℕ) (V : Fin K → Set ℕ) (i : Fin K),
    ext N W V (idxV i) = V i := by
  intro N
  induction N with
  | zero => intro W V i; simp [ext, idxV]
  | succ N ih =>
    intro W V i
    have e : (idxV (N := N + 1) i : Fin (K + (N + 1))) = Fin.succ (idxV (N := N) i) := by
      ext; simp [idxV]; omega
    simp only [ext]
    rw [e, Fin.cons_succ, ih]

/-- A block of `N` set quantifiers. -/
theorem exSN : ∀ (N : ℕ) {K : ℕ} {P : ℕ → (Fin m → ℕ) → (Fin (K + N) → Set ℕ) → Prop},
    EvDef P → EvDef (fun n ν V =>
      ∃ W : Fin N → Set ℕ, (∀ c, W c ⊆ {i | i < n}) ∧ P n ν (ext N W V)) := by
  intro N
  induction N with
  | zero =>
    intro K P h
    refine h.congr 0 fun n _ ν _ V => ?_
    exact ⟨fun hP => ⟨fun i => i.elim0, fun i => i.elim0, hP⟩, fun ⟨_, _, hP⟩ => hP⟩
  | succ N ih =>
    intro K P h
    refine (ih h.exS).congr 0 fun n _ ν _ V => ?_
    constructor
    · rintro ⟨W', hW', X, hX, hP⟩
      refine ⟨Fin.cons X W', fun c => ?_, ?_⟩
      · refine Fin.cases ?_ (fun c => ?_) c
        · simpa using hX
        · simpa using hW' c
      · simp only [ext, Fin.cons_zero, Fin.tail_cons]
        exact hP
    · rintro ⟨W, hW, hP⟩
      exact ⟨Fin.tail W, fun c => hW _, W 0, hW 0, hP⟩

end EvDef

/-! ## Exact position formulas -/

section Formulas

variable {α : Type*} {w : List α} {m k : ℕ} {ν : Fin m → ℕ} {V : Fin k → Set ℕ}

/-- `x ≤ d` -/
def posLe (d : ℕ) (x : Fin m) : MSO α m k := .exF (.and (isFirst 0) (leAdd d x.succ 0))

theorem sat_posLe (d : ℕ) (x : Fin m) (hx : ν x < w.length) :
    Sat w (posLe d x : MSO α m k) ν V ↔ ν x ≤ d := by
  simp only [posLe, Sat]
  constructor
  · rintro ⟨f, hf, h1, h2⟩
    rw [sat_isFirst_of_lt _ (by simpa using hf)] at h1
    rw [sat_leAdd _ _ _ _ (by simpa using hx)] at h2
    simp only [Fin.cons_zero, Fin.cons_succ] at h1 h2
    omega
  · intro h
    refine ⟨0, by omega, ?_, ?_⟩
    · rw [sat_isFirst_of_lt _ (by simp; omega)]; simp
    · rw [sat_leAdd _ _ _ _ (by simpa using hx)]; simpa using h

/-- `|w| ≤ x + d + 1` (`x` is within distance `d` of the last position) -/
def posLeR (d : ℕ) (x : Fin m) : MSO α m k := .exF (.and (isLast 0) (leAdd d 0 x.succ))

theorem sat_posLeR (d : ℕ) (x : Fin m) (hx : ν x < w.length) :
    Sat w (posLeR d x : MSO α m k) ν V ↔ w.length ≤ ν x + d + 1 := by
  simp only [posLeR, Sat]
  constructor
  · rintro ⟨l, hl, h1, h2⟩
    rw [sat_isLast_of_lt _ (by simpa using hl)] at h1
    rw [sat_leAdd _ _ _ _ (by simpa using hl)] at h2
    simp only [Fin.cons_zero, Fin.cons_succ] at h1 h2
    omega
  · intro h
    refine ⟨w.length - 1, by omega, ?_, ?_⟩
    · rw [sat_isLast_of_lt _ (by simp; omega)]; simp; omega
    · rw [sat_leAdd _ _ _ _ (by simp; omega)]; simp; omega

/-- `x + y ≤ d` -/
def sumLe : ℕ → {m : ℕ} → Fin m → Fin m → MSO α m k
  | 0, _, x, y => .and (posLe 0 x) (posLe 0 y)
  | d + 1, _, x, y =>
    MSO.or (.and (posLe 0 x) (posLe (d + 1) y)) (.exF (.and (.succ 0 x.succ) (sumLe d 0 y.succ)))

theorem sat_sumLe : ∀ (d : ℕ) {m : ℕ} (x y : Fin m) (ν : Fin m → ℕ),
    ν x < w.length → ν y < w.length →
    (Sat w (sumLe d x y : MSO α m k) ν V ↔ ν x + ν y ≤ d) := by
  intro d
  induction d with
  | zero =>
    intro m x y ν hx hy
    simp only [sumLe, Sat, sat_posLe _ _ hx, sat_posLe _ _ hy]
    omega
  | succ d ih =>
    intro m x y ν hx hy
    simp only [sumLe, sat_or, Sat, sat_posLe _ _ hx, sat_posLe _ _ hy, Fin.cons_zero,
      Fin.cons_succ]
    constructor
    · rintro (h | ⟨z, hz, h1, h2⟩)
      · omega
      · rw [ih 0 y.succ (Fin.cons z ν) (by simpa using hz) (by simpa using hy)] at h2
        simp only [Fin.cons_zero, Fin.cons_succ] at h2
        omega
    · intro h
      by_cases h0 : ν x = 0
      · exact Or.inl ⟨by omega, by omega⟩
      · refine Or.inr ⟨ν x - 1, by omega, by omega, ?_⟩
        rw [ih 0 y.succ (Fin.cons (ν x - 1) ν) (by simp; omega) (by simpa using hy)]
        simp only [Fin.cons_zero, Fin.cons_succ]
        omega

/-- `2|w| ≤ x + y + d + 2`, i.e. `(|w|-1-x) + (|w|-1-y) ≤ d` -/
def sumLeR : ℕ → {m : ℕ} → Fin m → Fin m → MSO α m k
  | 0, _, x, y => .and (isLast x) (isLast y)
  | d + 1, _, x, y =>
    MSO.or (.and (isLast x) (posLeR (d + 1) y)) (.exF (.and (.succ x.succ 0) (sumLeR d 0 y.succ)))

theorem sat_sumLeR : ∀ (d : ℕ) {m : ℕ} (x y : Fin m) (ν : Fin m → ℕ),
    ν x < w.length → ν y < w.length →
    (Sat w (sumLeR d x y : MSO α m k) ν V ↔ 2 * w.length ≤ ν x + ν y + d + 2) := by
  intro d
  induction d with
  | zero =>
    intro m x y ν hx hy
    simp only [sumLeR, Sat, sat_isLast_of_lt _ hx, sat_isLast_of_lt _ hy]
    omega
  | succ d ih =>
    intro m x y ν hx hy
    simp only [sumLeR, sat_or, Sat, sat_isLast_of_lt _ hx, sat_posLeR _ _ hy, Fin.cons_zero,
      Fin.cons_succ]
    constructor
    · rintro (h | ⟨z, hz, h1, h2⟩)
      · omega
      · rw [ih 0 y.succ (Fin.cons z ν) (by simpa using hz) (by simpa using hy)] at h2
        simp only [Fin.cons_zero, Fin.cons_succ] at h2
        omega
    · intro h
      by_cases h0 : ν x + 1 = w.length
      · exact Or.inl ⟨h0, by omega⟩
      · refine Or.inr ⟨ν x + 1, by omega, rfl, ?_⟩
        rw [ih 0 y.succ (Fin.cons (ν x + 1) ν) (by simp; omega) (by simpa using hy)]
        simp only [Fin.cons_zero, Fin.cons_succ]
        omega

/-- `x % q = ρ` -/
def posMod (q ρ : ℕ) (x : Fin m) : MSO α m k :=
  .exS (.and (multOf q 0) (.exF (.and (.mem 0 0) (addEq ρ 0 x.succ))))

theorem sat_posMod {q ρ : ℕ} (hq : 0 < q) (hρ : ρ < q) (x : Fin m) (hx : ν x < w.length) :
    Sat w (posMod q ρ x : MSO α m k) ν V ↔ ν x % q = ρ := by
  simp only [posMod, Sat]
  constructor
  · rintro ⟨X, -, hm, z, hz, hzX, hadd⟩
    rw [sat_multOf] at hm
    simp only [Fin.cons_zero] at hm hzX
    rw [sat_addEq _ _ _ _ (by simpa using hx)] at hadd
    simp only [Fin.cons_zero, Fin.cons_succ] at hadd
    obtain ⟨c, rfl⟩ := (multOf_mem_iff hq hm z hz).1 hzX
    rw [hadd, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hρ
  · intro h
    have e := Nat.div_add_mod (ν x) q
    refine ⟨{i | i < w.length ∧ q ∣ i}, fun i hi => hi.1, ?_, q * (ν x / q), by omega, ?_, ?_⟩
    · rw [sat_multOf]
      simpa only [Fin.cons_zero] using multOf_exists hq
    · simp only [Fin.cons_zero]
      exact ⟨by omega, dvd_mul_right q _⟩
    · rw [sat_addEq _ _ _ _ (by simpa using hx)]
      simp only [Fin.cons_zero, Fin.cons_succ]
      omega

end Formulas

end R002.Claude3Mso
