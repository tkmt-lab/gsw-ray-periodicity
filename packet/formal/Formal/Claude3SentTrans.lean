import Formal.Claude3SentRow

/-!
# Theorem 1a, G6: the transition through identifications of at most two heights

Written by a Claude worker (2026-10-20, Theorem 1a, parts G6/A).

The three identifications of `TransAt t x y i` share the entry index `i` of `y`. They are
decoupled by the **shift trick**: the first identification `rp y i ∼ q_{u+1}` comes from a word
`w` with `rp y i = Φ_w (q_{u+1})` (`ident_iff_word`), and then `rp y (i + n) = Φ_w (q_{u+1}) +
rotN k_y (dS η n)` (`rp_shift`, `η` the parity of `i`). So the second and third identifications
are between points depending on the height of `x` only (`entRow`, a neighbour row of the exit
point), and only the existence of the entry position on the row of `y` (with the passage range)
couples the two heights (`YPart`). For a terminal `y` the terminal index is pinned by the corner
word (`TermPart`, explicit affine data `cornerY`).

* `trans_iff_char` : under `Embedded` and `RowsIn t y`, `Trans t x y ↔ TransChar t x y`.
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo

variable {S : Sig} {t : ℕ}

/-- The point `Φ_w (q_{u+1}) + d` of the chart of `τy` (a single point, height of `x`). -/
def entRow (τx τy : PType S) (b : Bool) (w : List (Letter S)) (d : ℤ × ℤ) : RowSet S :=
  nbrRow (exitRow τx b 1) τy.f w d

theorem entRow_at (x : PState S) (τy : PType S) (b : Bool) (hg : ExitGuard x.1 b t x.2)
    (w : List (Letter S)) (d z : ℤ × ℤ) :
    (entRow x.1 τy b w d).At t x.2 z ↔
      (∀ ch ∈ wordCharts S w x.1.f, ch.Mem t (rp x (hiS t x + 1))) ∧
        z = (wordAff S w).apply t (rp x (hiS t x + 1)) + d := by
  rw [entRow, nbrRow_at']
  constructor
  · rintro ⟨p, hp, hch, rfl⟩
    rw [exitRow_at1 x b hg] at hp
    subst hp
    exact ⟨hch, rfl⟩
  · rintro ⟨hch, rfl⟩
    exact ⟨_, (exitRow_at1 x b hg _).2 rfl, hch, rfl⟩

/-- The row of `y` with parity `η` and position bounds. -/
abbrev yRow (τ : PType S) (η : ℤ) (ups : List Bnd) : RowSet S :=
  rowPtRow τ.f τ.k η (lowsY τ η) ups

/-- The terminal part: the corner `m` pins the terminal index; the entry is not after it. -/
def TermPart (t : ℕ) (y : PState S) (m : Fin S.M) (η : ℤ) (R : RowSet S) (hx : ℤ) : Prop :=
  ∃ w' : List (Letter S), w'.length < S.C ∧ WordOK S w' (S.mchart m) y.1.f ∧
    (∀ c ∈ wordCharts S w' (S.mchart m), c.Mem t ((S.mx m).eval t, (S.my m).eval t)) ∧
    ∃ ηc : ℤ, (ηc = 0 ∨ ηc = 1) ∧ y.2 + ηc = (cornerY S y.1.k m w').2.eval t ∧
      2 * (cornerY S y.1.k m w').1.eval t + ηc - 2 ≤ hiS t y ∧
      Meet S t (yRow y.1 η [⟨0, affAdd (cornerY S y.1.k m w').1 ((ηc - η - 2) / 2)⟩]) y.2 R hx

/-- The part of the transition on the row of `y`. -/
def YPart (t : ℕ) (y : PState S) (η : ℤ) (R : RowSet S) (hx : ℤ) : Prop :=
  (y.1.term = none ∧ Meet S t (yRow y.1 η (upsY y.1 η)) y.2 R hx) ∨
    ∃ m, y.1.term = some m ∧ TermPart t y m η R hx

/-- **The transition, decoupled.** -/
def TransChar (t : ℕ) (x y : PState S) : Prop :=
  x.1.term = none ∧ y.1.root = none ∧ ∃ b, ExitGuard x.1 b t x.2 ∧
    ∃ w : List (Letter S), w.length < S.C ∧ WordOK S w x.1.f y.1.f ∧
      ∃ η : ℤ, (η = 0 ∨ η = 1) ∧
        Meet S t (entRow x.1 y.1 b w (rotN y.1.k (dS η 1))) x.2 (exitRow x.1 b 2) x.2 ∧
        ¬ Meet S t (entRow x.1 y.1 b w (rotN y.1.k (dS η 2))) x.2 (exitRow x.1 b 0) x.2 ∧
        YPart t y η (entRow x.1 y.1 b w 0) x.2

/-- The entry position from the meeting with the entry point. -/
theorem meet_entry (hE : Embedded S t) {x y : PState S} {b : Bool} (hg : ExitGuard x.1 b t x.2)
    {w : List (Letter S)} {η : ℤ} (hη : η = 0 ∨ η = 1) {ups : List Bnd}
    (h : Meet S t (yRow y.1 η ups) y.2 (entRow x.1 y.1 b w 0) x.2) :
    ∃ X : ℤ, ((∀ b ∈ lowsY y.1 η, b.σ * y.2 + b.c.eval t ≤ X) ∧
      ∀ b ∈ ups, X ≤ b.σ * y.2 + b.c.eval t) ∧
      rp y (2 * X + η) = (wordAff S w).apply t (rp x (hiS t x + 1)) ∧
      (∀ ch ∈ wordCharts S w x.1.f, ch.Mem t (rp x (hiS t x + 1))) ∧
      (S.chart y.1.f).Mem t (rp y (2 * X + η)) := by
  obtain ⟨z₁, z₂, h₁, h₂, hz₁, hz₂, he⟩ := h
  rw [rowPtRow_at _ _ hη] at h₁
  obtain ⟨X, hb, rfl⟩ := h₁
  rw [entRow_at x y.1 b hg] at h₂
  obtain ⟨hch, rfl⟩ := h₂
  have := hE y.1.f _ _ hz₁ hz₂ he
  rw [add_zero] at this
  exact ⟨X, hb, this, hch, hz₁⟩

theorem trans_iff_char (hE : Embedded S t) {x y : PState S} (hy : RowsIn t y) :
    Trans t x y ↔ TransChar t x y := by
  constructor
  · rintro ⟨i, hxt, hyr, ⟨e, hP⟩, ⟨v₁, ⟨hz₁y, rfl⟩, ⟨hz₁x, hq₁⟩⟩, ⟨v₂, ⟨hz₂y, rfl⟩, ⟨hz₂x, hq₂⟩⟩,
      hN⟩
    obtain ⟨b, hg⟩ := exitGuard_exists x.1 t x.2
    obtain ⟨w, hw, hok, hch, hwe⟩ := (ident_iff_word hE x.1.f y.1.f _ _).1 ⟨hz₁x, hz₁y, hq₁⟩
    obtain ⟨X, η, hη, rfl⟩ : ∃ X η : ℤ, (η = 0 ∨ η = 1) ∧ i = 2 * X + η :=
      ⟨i / 2, i % 2, by omega, by omega⟩
    refine ⟨hxt, hyr, b, hg, w, hw, hok, η, hη, ?_, ?_, ?_⟩
    · refine ⟨_, _, (entRow_at x y.1 b hg w _ _).2 ⟨hch, ?_⟩, (exitRow_at2 x b hg _).2 rfl,
        hz₂y, hz₂x, hq₂.symm⟩
      rw [rp_shift y X η 1 hη, hwe]
    · rintro ⟨z₁, z₂, h₁, h₂, hz₁, hz₂, he⟩
      rw [entRow_at x y.1 b hg] at h₁
      rw [exitRow_at0 x b hg] at h₂
      obtain ⟨-, h₁⟩ := h₁
      rw [← hwe, ← rp_shift y X η 2 hη] at h₁
      subst h₁ h₂
      exact hN _ _ ⟨hz₁, rfl⟩ ⟨hz₂, rfl⟩ he
    · obtain ⟨-, hlo, hie, hehi, hex⟩ := hP
      cases ht : y.1.term with
      | none =>
        refine Or.inl ⟨ht, _, _, (rowPtRow_at _ _ hη _ _ _ _).2 ⟨X, ⟨(lo_le_iff y hη X).1 hlo,
          (le_hi_iff y hη X).1 ?_⟩, rfl⟩, (entRow_at x y.1 b hg w 0 _).2 ⟨hch, ?_⟩, hz₁y, hz₁y,
          rfl⟩
        · rw [← hex.1 ht]; exact hie
        · rw [add_zero]; exact hwe
      | some m =>
        obtain ⟨w', hw', hok', hch', hce⟩ := (atCorner_iff_word hE y (e + 2) m).1 (hex.2 m ht)
        obtain ⟨ηc, hηc, hj, hh⟩ := (rp_eq_corner_iff y m w' (e + 2)).1 hce
        refine Or.inr ⟨m, ht, w', hw', hok', hch', ηc, hηc, hh, by omega, _, _,
          (rowPtRow_at _ _ hη _ _ _ _).2 ⟨X, ⟨(lo_le_iff y hη X).1 hlo, ?_⟩, rfl⟩,
          (entRow_at x y.1 b hg w 0 _).2 ⟨hch, ?_⟩, hz₁y, hz₁y, rfl⟩
        · simp only [List.mem_singleton, forall_eq, zero_mul, zero_add, affAdd_eval]
          omega
        · rw [add_zero]; exact hwe
  · rintro ⟨hxt, hyr, b, hg, w, hw, hok, η, hη, hM₂, hN₃, hYP⟩
    -- the entry position and the passage
    obtain ⟨X, e, hrp, hch, hzy, hP⟩ : ∃ X e : ℤ,
        rp y (2 * X + η) = (wordAff S w).apply t (rp x (hiS t x + 1)) ∧
        (∀ ch ∈ wordCharts S w x.1.f, ch.Mem t (rp x (hiS t x + 1))) ∧
        (S.chart y.1.f).Mem t (rp y (2 * X + η)) ∧ PassOK t y (2 * X + η) e := by
      rcases hYP with ⟨ht, hM⟩ | ⟨m, ht, w', hw', hok', hch', ηc, hηc, hh, hehi, hM⟩
      · obtain ⟨X, ⟨hlo, hup⟩, hrp, hch, hzy⟩ := meet_entry hE hg hη hM
        exact ⟨X, hiS t y, hrp, hch, hzy, hy, (lo_le_iff y hη X).2 hlo,
          (le_hi_iff y hη X).2 hup, le_refl _, ⟨fun _ => rfl, fun m hm => by simp [ht] at hm⟩⟩
      · obtain ⟨X, ⟨hlo, hup⟩, hrp, hch, hzy⟩ := meet_entry hE hg hη hM
        simp only [List.mem_singleton, forall_eq, zero_mul, zero_add, affAdd_eval] at hup
        refine ⟨X, 2 * (cornerY S y.1.k m w').1.eval t + ηc - 2, hrp, hch, hzy, hy,
          (lo_le_iff y hη X).2 hlo, by omega, hehi, ⟨fun h => by simp [ht] at h, ?_⟩⟩
        intro m' hm'
        rw [ht, Option.some.injEq] at hm'
        subst hm'
        refine (atCorner_iff_word hE y _ m).2 ⟨w', hw', hok', hch', ?_⟩
        exact (rp_eq_corner_iff y m w' _).2 ⟨ηc, hηc, by ring, hh⟩
    obtain ⟨hzq, hzy', hq⟩ := (ident_iff_word hE x.1.f y.1.f _ _).2 ⟨w, hw, hok, hch, hrp⟩
    refine ⟨2 * X + η, hxt, hyr, ⟨e, hP⟩, ⟨_, ⟨hzy', rfl⟩, ⟨hzq, hq⟩⟩, ?_, ?_⟩
    · obtain ⟨z₁, z₂, h₁, h₂, hz₁, hz₂, he⟩ := hM₂
      rw [entRow_at x y.1 b hg] at h₁
      rw [exitRow_at2 x b hg] at h₂
      obtain ⟨-, h₁⟩ := h₁
      rw [← hrp, ← rp_shift y X η 1 hη] at h₁
      subst h₁ h₂
      exact ⟨_, ⟨hz₁, rfl⟩, ⟨hz₂, he.symm⟩⟩
    · rintro v v' ⟨hz₁, rfl⟩ ⟨hz₂, rfl⟩ he
      refine hN₃ ⟨_, _, (entRow_at x y.1 b hg w _ _).2 ⟨hch, ?_⟩, (exitRow_at0 x b hg _).2 rfl,
        hz₁, hz₂, he⟩
      rw [rp_shift y X η 2 hη, hrp]

end ClaudeChallenge2.State
