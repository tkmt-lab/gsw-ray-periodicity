import Formal.Claude3MsoSyntax

/-!
# Derived MSO formulas and their semantics

* `rename`: variable renaming (weakening / substitution of variables), `sat_rename`.
* `sing X` (singleton), `isFirst x`, `isLast x`.
* `addEq c x y` (`y = x + c`), `leAdd c x y` (`x ≤ y + c`) for a fixed natural `c`.
* set patterns: `subset`, `isEmpty`, `between`, `convex`, and MSO connectivity `conn`
  (no nonempty proper succ-closed subset), with `conn ↔ convex` on words.

Variables are de Bruijn indices; `v1 = Fin.succ 0`, `v2 = Fin.succ (Fin.succ 0)`.
-/

namespace R002.Claude3Mso

universe u

variable {α : Type u}

namespace MSO

/-- lift a renaming under a binder -/
def liftR {m m' : ℕ} (f : Fin m → Fin m') : Fin (m + 1) → Fin (m' + 1) :=
  Fin.cases 0 (fun i => (f i).succ)

theorem cons_comp_liftR {β : Type*} {m m' : ℕ} (f : Fin m → Fin m') (x : β) (ν : Fin m' → β) :
    (Fin.cons x ν : Fin (m' + 1) → β) ∘ liftR f = Fin.cons x (ν ∘ f) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [liftR]

/-- Renaming of first-order and set variables. -/
def rename : {m k m' k' : ℕ} → (Fin m → Fin m') → (Fin k → Fin k') → MSO α m k → MSO α m' k'
  | _, _, _, _, f, _, .lt x y => .lt (f x) (f y)
  | _, _, _, _, f, _, .eq x y => .eq (f x) (f y)
  | _, _, _, _, f, _, .succ x y => .succ (f x) (f y)
  | _, _, _, _, f, g, .mem x X => .mem (f x) (g X)
  | _, _, _, _, f, _, .lab a x => .lab a (f x)
  | _, _, _, _, f, g, .neg φ => .neg (rename f g φ)
  | _, _, _, _, f, g, .and φ ψ => .and (rename f g φ) (rename f g ψ)
  | _, _, _, _, f, g, .exF φ => .exF (rename (liftR f) g φ)
  | _, _, _, _, f, g, .exS φ => .exS (rename f (liftR g) φ)

theorem sat_rename {w : List α} : ∀ {m k m' k' : ℕ} (f : Fin m → Fin m') (g : Fin k → Fin k')
    (φ : MSO α m k) (ν : Fin m' → ℕ) (V : Fin k' → Set ℕ),
    Sat w (rename f g φ) ν V ↔ Sat w φ (ν ∘ f) (V ∘ g) := by
  intro m k m' k' f g φ
  induction φ generalizing m' k' with
  | lt x y => intro ν V; simp [rename]
  | eq x y => intro ν V; simp [rename]
  | succ x y => intro ν V; simp [rename]
  | mem x X => intro ν V; simp [rename]
  | lab a x => intro ν V; simp [rename]
  | neg φ ih => intro ν V; simp [rename, ih]
  | and φ ψ ihφ ihψ => intro ν V; simp [rename, ihφ, ihψ]
  | exF φ ih => intro ν V; simp [rename, ih, cons_comp_liftR]
  | exS φ ih => intro ν V; simp [rename, ih, cons_comp_liftR]

/-- weakening by one fresh first-order variable (index `0`) -/
def wkF {m k : ℕ} (φ : MSO α m k) : MSO α (m + 1) k := rename Fin.succ id φ
/-- weakening by one fresh set variable (index `0`) -/
def wkS {m k : ℕ} (φ : MSO α m k) : MSO α m (k + 1) := rename id Fin.succ φ

@[simp] theorem sat_wkF {w : List α} {m k : ℕ} (φ : MSO α m k) (x : ℕ) (ν : Fin m → ℕ)
    (V : Fin k → Set ℕ) : Sat w (wkF φ) (Fin.cons x ν) V ↔ Sat w φ ν V := by
  rw [wkF, sat_rename]; rfl

@[simp] theorem sat_wkS {w : List α} {m k : ℕ} (φ : MSO α m k) (ν : Fin m → ℕ) (X : Set ℕ)
    (V : Fin k → Set ℕ) : Sat w (wkS φ) ν (Fin.cons X V) ↔ Sat w φ ν V := by
  rw [wkS, sat_rename]; rfl

variable {w : List α} {m k : ℕ} {ν : Fin m → ℕ} {V : Fin k → Set ℕ}

/-! ## Singletons, first and last positions -/

/-- `X` is a singleton: `∃x ∀y (y ∈ X ↔ y = x)` -/
def sing (X : Fin k) : MSO α m k := .exF (allF (iff (.mem 0 X) (.eq 0 (Fin.succ 0))))

theorem sat_sing (X : Fin k) :
    Sat w (sing X : MSO α m k) ν V ↔
      ∃ x, x < w.length ∧ ∀ y, y < w.length → (y ∈ V X ↔ y = x) := by
  simp [sing]

theorem sat_sing_of_subset (X : Fin k) (hV : V X ⊆ {i | i < w.length}) :
    Sat w (sing X : MSO α m k) ν V ↔ ∃ x, V X = {x} := by
  rw [sat_sing]
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨x, Set.ext fun y => ?_⟩
    by_cases hy : y < w.length
    · rw [h y hy]; rfl
    · constructor
      · exact fun hm => absurd (hV hm) hy
      · rintro rfl; exact absurd hx hy
  · rintro ⟨x, hx⟩
    have hxl : x < w.length := hV (hx ▸ rfl)
    exact ⟨x, hxl, fun y _ => by rw [hx]; rfl⟩

/-- `x` is the first position: `¬∃y. y < x` -/
def isFirst (x : Fin m) : MSO α m k := .neg (.exF (.lt 0 x.succ))

theorem sat_isFirst (x : Fin m) :
    Sat w (isFirst x : MSO α m k) ν V ↔ ∀ y, y < w.length → ν x ≤ y := by
  simp [isFirst]

theorem sat_isFirst_of_lt (x : Fin m) (hx : ν x < w.length) :
    Sat w (isFirst x : MSO α m k) ν V ↔ ν x = 0 := by
  rw [sat_isFirst]
  constructor
  · intro h; have := h 0 (by omega); omega
  · intro h y _; omega

/-- `x` is the last position: `¬∃y. x < y` -/
def isLast (x : Fin m) : MSO α m k := .neg (.exF (.lt x.succ 0))

theorem sat_isLast (x : Fin m) :
    Sat w (isLast x : MSO α m k) ν V ↔ ∀ y, y < w.length → y ≤ ν x := by
  simp [isLast]

theorem sat_isLast_of_lt (x : Fin m) (hx : ν x < w.length) :
    Sat w (isLast x : MSO α m k) ν V ↔ ν x + 1 = w.length := by
  rw [sat_isLast]
  constructor
  · intro h; have := h (w.length - 1) (by omega); omega
  · intro h y hy; omega

/-! ## Fixed offsets -/

/-- `addEq c x y` : `y = x + c` (iterated successor) -/
def addEq : ℕ → {m : ℕ} → Fin m → Fin m → MSO α m k
  | 0, _, x, y => .eq y x
  | c + 1, _, x, y => .exF (.and (.succ x.succ 0) (addEq c 0 y.succ))

theorem sat_addEq : ∀ (c : ℕ) {m : ℕ} (x y : Fin m) (ν : Fin m → ℕ), ν y < w.length →
    (Sat w (addEq c x y : MSO α m k) ν V ↔ ν y = ν x + c) := by
  intro c
  induction c with
  | zero => intro m x y ν _; simp [addEq]
  | succ c ih =>
    intro m x y ν hy
    simp only [addEq, Sat, Fin.cons_succ, Fin.cons_zero]
    constructor
    · rintro ⟨z, -, hz, h⟩
      rw [ih 0 y.succ (Fin.cons z ν) (by simpa using hy)] at h
      simp only [Fin.cons_succ, Fin.cons_zero] at h
      omega
    · intro h
      refine ⟨ν x + 1, by omega, rfl, ?_⟩
      rw [ih 0 y.succ (Fin.cons (ν x + 1) ν) (by simpa using hy)]
      simp only [Fin.cons_succ, Fin.cons_zero]
      omega

/-- `leAdd c x y` : `x ≤ y + c` -/
def leAdd : ℕ → {m : ℕ} → Fin m → Fin m → MSO α m k
  | 0, _, x, y => le x y
  | c + 1, _, x, y => or (le x y) (.exF (.and (.succ y.succ 0) (leAdd c x.succ 0)))

theorem sat_leAdd : ∀ (c : ℕ) {m : ℕ} (x y : Fin m) (ν : Fin m → ℕ), ν x < w.length →
    (Sat w (leAdd c x y : MSO α m k) ν V ↔ ν x ≤ ν y + c) := by
  intro c
  induction c with
  | zero => intro m x y ν _; simp [leAdd]
  | succ c ih =>
    intro m x y ν hx
    simp only [leAdd, sat_or, sat_le, Sat, Fin.cons_succ, Fin.cons_zero]
    constructor
    · rintro (h | ⟨z, -, hz, h⟩)
      · omega
      · rw [ih x.succ 0 (Fin.cons z ν) (by simpa using hx)] at h
        simp only [Fin.cons_succ, Fin.cons_zero] at h
        omega
    · intro h
      by_cases h' : ν x ≤ ν y
      · exact Or.inl h'
      · refine Or.inr ⟨ν y + 1, by omega, rfl, ?_⟩
        rw [ih x.succ 0 (Fin.cons (ν y + 1) ν) (by simpa using hx)]
        simp only [Fin.cons_succ, Fin.cons_zero]
        omega

/-! ## Set patterns -/

/-- `X ⊆ Y` -/
def subset (X Y : Fin k) : MSO α m k := allF (imp (.mem 0 X) (.mem 0 Y))

theorem sat_subset (X Y : Fin k) :
    Sat w (subset X Y : MSO α m k) ν V ↔ ∀ x, x < w.length → x ∈ V X → x ∈ V Y := by
  simp [subset]

/-- `X = ∅` -/
def isEmpty (X : Fin k) : MSO α m k := allF (.neg (.mem 0 X))

theorem sat_isEmpty (X : Fin k) :
    Sat w (isEmpty X : MSO α m k) ν V ↔ ∀ x, x < w.length → x ∉ V X := by
  simp [isEmpty]

/-- every position between `x` and `y` (inclusive) lies in `X` -/
def between (x y : Fin m) (X : Fin k) : MSO α m k :=
  allF (imp (.and (le x.succ 0) (le 0 y.succ)) (.mem 0 X))

theorem sat_between (x y : Fin m) (X : Fin k) :
    Sat w (between x y X : MSO α m k) ν V ↔
      ∀ z, z < w.length → ν x ≤ z → z ≤ ν y → z ∈ V X := by
  simp [between]

/-- `X` is convex (an interval of positions) -/
def convex (X : Fin k) : MSO α m k :=
  allF (allF (imp (.and (.mem (Fin.succ 0) X) (.mem 0 X)) (between (Fin.succ 0) 0 X)))

theorem sat_convex (X : Fin k) :
    Sat w (convex X : MSO α m k) ν V ↔
      ∀ x z y, x < w.length → z < w.length → y < w.length →
        x ∈ V X → z ∈ V X → x ≤ y → y ≤ z → y ∈ V X := by
  simp only [convex, sat_allF, sat_imp, Sat, sat_between, Fin.cons_succ, Fin.cons_zero]
  constructor
  · intro h x z y hx hz hy hxX hzX hxy hyz
    exact h x hx z hz ⟨hxX, hzX⟩ y hy hxy hyz
  · intro h x hx z hz ⟨hxX, hzX⟩ y hy hxy hyz
    exact h x z y hx hz hy hxX hzX hxy hyz

/-- MSO connectivity of `X` for the successor relation: every nonempty `Y ⊆ X` closed under
successor steps inside `X` contains `X`. -/
def conn (X : Fin k) : MSO α m k :=
  allS (imp
    (.and (subset 0 X.succ)
      (.and (.exF (.mem 0 0))
        (allF (allF (imp
          (.and (.mem (Fin.succ 0) X.succ) (.and (.mem 0 X.succ) (.succ (Fin.succ 0) 0)))
          (iff (.mem (Fin.succ 0) 0) (.mem 0 0)))))))
    (subset X.succ 0))

theorem sat_conn (X : Fin k) :
    Sat w (conn X : MSO α m k) ν V ↔
      ∀ Y : Set ℕ, Y ⊆ {i | i < w.length} →
        (∀ x, x < w.length → x ∈ Y → x ∈ V X) → (∃ y, y < w.length ∧ y ∈ Y) →
        (∀ x, x < w.length → ∀ y, y < w.length → x ∈ V X → y ∈ V X → y = x + 1 →
          (x ∈ Y ↔ y ∈ Y)) →
        ∀ x, x < w.length → x ∈ V X → x ∈ Y := by
  simp only [conn, sat_allS, sat_imp, Sat, sat_subset, sat_allF, sat_iff, Fin.cons_succ,
    Fin.cons_zero]
  constructor
  · intro h Y hY h1 h2 h3
    exact h Y hY ⟨h1, h2, fun x hx y hy ⟨hxX, hyX, hxy⟩ => h3 x hx y hy hxX hyX hxy⟩
  · intro h Y hY ⟨h1, h2, h3⟩
    exact h Y hY h1 h2 fun x hx y hy hxX hyX hxy => h3 x hx y hy ⟨hxX, hyX, hxy⟩

/-- On words, MSO connectivity of a set of positions is the same as convexity. -/
theorem sat_conn_iff_convex (X : Fin k) (hV : V X ⊆ {i | i < w.length}) :
    Sat w (conn X : MSO α m k) ν V ↔ Sat w (convex X : MSO α m k) ν V := by
  rw [sat_conn, sat_convex]
  constructor
  · intro h x z y hx hz hy hxX hzX hxy hyz
    by_contra hyX
    -- `Y = {i ∈ X | i < y}` is nonempty, closed, but misses `z`
    have := h {i | i ∈ V X ∧ i < y} (fun i hi => hV hi.1) (fun i _ hi => hi.1)
      ⟨x, hx, hxX, lt_of_le_of_ne hxy (fun e => hyX (e ▸ hxX))⟩
      (fun a _ b _ haX hbX hab => by
        simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨-, ha⟩
          refine ⟨hbX, lt_of_le_of_ne (by omega) (fun e => hyX (e ▸ hbX))⟩
        · rintro ⟨-, hb⟩; exact ⟨haX, by omega⟩) z hz hzX
    exact absurd this.2 (by omega)
  · intro h Y _ hYX ⟨y₀, hy₀, hy₀Y⟩ hcl x hx hxX
    have hy₀X := hYX y₀ hy₀ hy₀Y
    rcases le_total y₀ x with hle | hle
    · -- walk up from `y₀` to `x`
      have : ∀ d, y₀ + d ≤ x → y₀ + d ∈ Y := by
        intro d
        induction d with
        | zero => intro _; simpa using hy₀Y
        | succ d ih =>
          intro hd
          have h1 : y₀ + d ∈ V X := h y₀ x (y₀ + d) hy₀ hx (by omega) hy₀X hxX (by omega) (by omega)
          have h2 : y₀ + (d + 1) ∈ V X :=
            h y₀ x (y₀ + (d + 1)) hy₀ hx (by omega) hy₀X hxX (by omega) hd
          exact (hcl _ (by omega) _ (by omega) h1 h2 (by omega)).1 (ih (by omega))
      simpa [Nat.add_sub_cancel' hle] using this (x - y₀) (by omega)
    · -- walk down from `y₀` to `x`
      have : ∀ d, x + d ≤ y₀ → y₀ - d ∈ Y := by
        intro d
        induction d with
        | zero => intro _; simpa using hy₀Y
        | succ d ih =>
          intro hd
          have h1 : y₀ - (d + 1) ∈ V X :=
            h x y₀ (y₀ - (d + 1)) hx hy₀ (by omega) hxX hy₀X (by omega) (by omega)
          have h2 : y₀ - d ∈ V X := h x y₀ (y₀ - d) hx hy₀ (by omega) hxX hy₀X (by omega) (by omega)
          exact (hcl _ (by omega) _ (by omega) h1 h2 (by omega)).2 (ih (by omega))
      have e : y₀ - (y₀ - x) = x := by omega
      simpa [e] using this (y₀ - x) (by omega)

end MSO

end R002.Claude3Mso
