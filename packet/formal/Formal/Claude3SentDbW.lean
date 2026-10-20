import Formal.Claude3SentEntry

/-!
# Theorem 1a, G6: condition 3 (b) by transition witnesses

Written by a Claude worker (2026-10-20, Theorem 1a, parts G6/A).

* `TW` : a transition witness (exit branch `b`, word `w`, entry parity `η`);
* `dbR_iff_witness` : `DbR x y` iff for every witness, with the entry index computed from the
  witness (`2 (entV.1 h_x + entG.1) + η`), the output of `y` avoids the full tail of `x`;
* `outV_gen` : outputs with a general lower bound as rows.
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo

variable {S : Sig} {t : ℕ}

/-- A transition witness. -/
def TW (t : ℕ) (x y : PState S) (b : Bool) (w : List (Letter S)) (η : ℤ) : Prop :=
  x.1.term = none ∧ y.1.root = none ∧ ExitGuard x.1 b t x.2 ∧ w.length < S.C ∧
    WordOK S w x.1.f y.1.f ∧
    Meet S t (entRow x.1 y.1 b w (rotN y.1.k (dS η 1))) x.2 (exitRow x.1 b 2) x.2 ∧
    ¬ Meet S t (entRow x.1 y.1 b w (rotN y.1.k (dS η 2))) x.2 (exitRow x.1 b 0) x.2 ∧
    YPart t y η (entRow x.1 y.1 b w 0) x.2

/-- Condition 3 (b) at a given entry index. -/
def PB (t : ℕ) (x y : PState S) (i : ℤ) : Prop :=
  ∀ s e e', OwnStart t x s → ExitAt t x e → ExitAt t y e' → ∀ v, OutV t y i e' v →
    ¬ OutV t x s e v

/-- The entry index of a witness. -/
def entI (t : ℕ) (x y : PState S) (b : Bool) (w : List (Letter S)) (η : ℤ) : ℤ :=
  2 * ((entV x.1 y.1 b w).1 * x.2 + (entG x.1 y.1 b w).1.eval t) + η

theorem transCharE_iff_TW (x y : PState S) (η : ℤ) :
    TransCharE t x y η ↔ ∃ b w, TW t x y b w η := by
  constructor
  · rintro ⟨h1, h2, b, hg, w, hw, hok, hM, hN, hY⟩
    exact ⟨b, w, h1, h2, hg, hw, hok, hM, hN, hY⟩
  · rintro ⟨b, w, h1, h2, hg, hw, hok, hM, hN, hY⟩
    exact ⟨h1, h2, b, hg, w, hw, hok, hM, hN, hY⟩

/-- A witness determines the entry point. -/
theorem TW.entry (hE : Embedded S t) {x y : PState S} {b : Bool} {w : List (Letter S)} {η : ℤ}
    (hη : η = 0 ∨ η = 1) (h : TW t x y b w η) :
    ∃ X, rp y (2 * X + η) = (wordAff S w).apply t (rp x (hiS t x + 1)) ∧
      (∀ ch ∈ wordCharts S w x.1.f, ch.Mem t (rp x (hiS t x + 1))) := by
  obtain ⟨-, -, hg, -, -, -, -, hY⟩ := h
  rcases hY with ⟨-, hM⟩ | ⟨m, -, _, -, -, -, _, -, -, -, hM⟩
  · obtain ⟨X, -, hrp, hch, -⟩ := meet_entry hE hg hη hM; exact ⟨X, hrp, hch⟩
  · obtain ⟨X, -, hrp, hch, -⟩ := meet_entry hE hg hη hM; exact ⟨X, hrp, hch⟩

theorem dbR_iff_witness (hE : Embedded S t) (x y : PState S) (hy : RowsIn t y) :
    DbR t x y ↔ ∀ b w η, (η = 0 ∨ η = 1) → TW t x y b w η →
      y.2 + η = (entV x.1 y.1 b w).2 * x.2 + (entG x.1 y.1 b w).2.eval t →
        PB t x y (entI t x y b w η) := by
  have hDb : DbR t x y ↔ ∀ i, TransAt t x y i → PB t x y i := by
    constructor
    · intro H i hT s e e' hs he he'; exact H s e i e' hs he hT he'
    · intro H s e i e' hs he hT he'; exact H i hT s e e' hs he he'
  rw [hDb]
  constructor
  · intro H b w η hη hW _
    obtain ⟨X₀, hrp, hch⟩ := hW.entry hE hη
    obtain ⟨i, X, hT, rfl⟩ := (transAtE_iff hE hy hη).2 ((transCharE_iff_TW x y η).2 ⟨b, w, hW⟩)
    have hi := entry_of_witness hE hT hW.2.2.2.1 hW.2.2.2.2.1 hch hrp
    obtain ⟨hX, -⟩ := (rp_eq_entry_iff x y b hW.2.2.1 w X₀ hη).1 hrp
    rw [hi, hX] at hT
    exact H _ hT
  · intro H i hT
    obtain ⟨X, η, hη, rfl⟩ : ∃ X η : ℤ, (η = 0 ∨ η = 1) ∧ i = 2 * X + η :=
      ⟨i / 2, i % 2, by omega, by omega⟩
    obtain ⟨b, w, hW⟩ := (transCharE_iff_TW x y η).1 ((transAtE_iff hE hy hη).1 ⟨_, X, hT, rfl⟩)
    obtain ⟨X₀, hrp, hch⟩ := hW.entry hE hη
    have hi := entry_of_witness hE hT hW.2.2.2.1 hW.2.2.2.2.1 hch hrp
    obtain ⟨hX, hh⟩ := (rp_eq_entry_iff x y b hW.2.2.1 w X₀ hη).1 hrp
    have := H b w η hη hW hh
    rwa [entI, ← hX, ← hi] at this

/-- Outputs with a general lower bound as rows. -/
theorem outV_gen (y : PState S) {s : ℤ} (lows : ℤ → List Bnd)
    (hl : ∀ η : ℤ, (η = 0 ∨ η = 1) → ∀ X, s + 2 ≤ 2 * X + η ↔
      ∀ b ∈ lows η, b.σ * y.2 + b.c.eval t ≤ X)
    {ed : ED S} {e : ℤ} (he : EDOK t y ed e) (v : Vertex S t) :
    OutV t y s e v ↔ ∃ η : ℤ, (η = 0 ∨ η = 1) ∧
      ∃ z, (rowPtRow y.1.f y.1.k η (lows η) (edUps y.1 η ed)).At t y.2 z ∧
        ∃ hz : (S.chart y.1.f).Mem t z, pt S t y.1.f z hz = v := by
  constructor
  · rintro ⟨j, h₁, h₂, hz, rfl⟩
    obtain ⟨X, η, hη, rfl⟩ : ∃ X η : ℤ, (η = 0 ∨ η = 1) ∧ j = 2 * X + η :=
      ⟨j / 2, j % 2, by omega, by omega⟩
    exact ⟨η, hη, _, (rowPtRow_at _ _ hη _ _ _ _).2 ⟨X, ⟨(hl η hη X).1 h₁,
      (ed_bounds_iff y he hη X).1 h₂⟩, rfl⟩, hz, rfl⟩
  · rintro ⟨η, hη, z, hA, hz, rfl⟩
    rw [rowPtRow_at _ _ hη] at hA
    obtain ⟨X, ⟨h₁, h₂⟩, rfl⟩ := hA
    exact ⟨2 * X + η, (hl η hη X).2 h₁, (ed_bounds_iff y he hη X).2 h₂, hz, rfl⟩

/-- The output points of `y` from entry `i`, parity `η'`, exit data `ed'`. -/
def YOut (t : ℕ) (y : PState S) (i : ℤ) (ed' : ED S) (η' : ℤ) (z : ℤ × ℤ) : Prop :=
  ∃ X', i + 2 ≤ 2 * X' + η' ∧ (∀ b ∈ edUps y.1 η' ed', X' ≤ b.σ * y.2 + b.c.eval t) ∧
    z = rp y (2 * X' + η')

/-- Some output point of `y` meets a point of the row `R` at height `h`. -/
def MeetY (t : ℕ) (y : PState S) (i : ℤ) (ed' : ED S) (η' : ℤ) (R : RowSet S) (h : ℤ) : Prop :=
  ∃ z₁ z₂, YOut t y i ed' η' z₁ ∧ R.At t h z₂ ∧
    ∃ (hz₁ : (S.chart y.1.f).Mem t z₁) (hz₂ : (S.chart R.f).Mem t z₂),
      pt S t y.1.f z₁ hz₁ = pt S t R.f z₂ hz₂

theorem pb_iff_meetY (hE : Embedded S t) (x y : PState S) (i : ℤ) :
    PB t x y i ↔ ∀ p ∈ dataList x.1, (∃ s, SDOK t x p.1 s) → (∃ e, EDOK t x p.2 e) →
      ∀ ed' ∈ edList y.1, (∃ e', EDOK t y ed' e') →
        ∀ η' ∈ ([0, 1] : List ℤ), ∀ η'' ∈ ([0, 1] : List ℤ),
          ¬ MeetY t y i ed' η' (tailRow x.1 η'' p.1 p.2) x.2 := by
  constructor
  · rintro H p hp ⟨s, hs⟩ ⟨e, he⟩ ed' hed' ⟨e', he'⟩ η' hη' η'' hη''
      ⟨z₁, z₂, ⟨X', h₁, h₂, rfl⟩, hA₂, hz₁, hz₂, hq⟩
    rw [mem_dataList] at hp
    refine H s e e' ((ownStart_iff hE x s).2 ⟨_, hp.1, hs⟩)
      ((exitAt_iff_ed hE x e).2 ⟨_, hp.2, he⟩) ((exitAt_iff_ed hE y e').2 ⟨_, hed', he'⟩) _
      ⟨2 * X' + η', h₁, (ed_bounds_iff y he' ((par_mem_iff η').1 hη') X').2 h₂, hz₁, rfl⟩
      ((outV_iff x hs he _).2 ⟨η'', (par_mem_iff η'').1 hη'', z₂, hA₂, hz₂, hq.symm⟩)
  · intro H s e e' hs he he' v ⟨j, h₁, h₂, hz₁, hv⟩ hout
    obtain ⟨sd, hsd, hs₁⟩ := (ownStart_iff hE x s).1 hs
    obtain ⟨ed, hed, he₁⟩ := (exitAt_iff_ed hE x e).1 he
    obtain ⟨ed', hed', he₁'⟩ := (exitAt_iff_ed hE y e').1 he'
    obtain ⟨η'', hη'', z₂, hA₂, hz₂, hq⟩ := (outV_iff x hs₁ he₁ _).1 hout
    obtain ⟨X', η', hη', rfl⟩ : ∃ X' η' : ℤ, (η' = 0 ∨ η' = 1) ∧ j = 2 * X' + η' :=
      ⟨j / 2, j % 2, by omega, by omega⟩
    exact H (sd, ed) (mem_dataList.2 ⟨hsd, hed⟩) ⟨s, hs₁⟩ ⟨e, he₁⟩ ed' hed' ⟨e', he₁'⟩ η'
      ((par_mem_iff η').2 hη') η'' ((par_mem_iff η'').2 hη'')
      ⟨_, z₂, ⟨X', h₁, (ed_bounds_iff y he₁' hη' X').1 h₂, rfl⟩, hA₂, hz₁, hz₂, hv.trans hq.symm⟩

end ClaudeChallenge2.State
