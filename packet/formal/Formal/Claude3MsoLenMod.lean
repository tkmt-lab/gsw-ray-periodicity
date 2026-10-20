import Formal.Claude3MsoDerived
import Formal.Claude3MsoUnary

/-!
# Word length modulo `q` in MSO

`multOf q X` says that (inside the word) `X` is exactly the set of positions divisible by `q`:
`∀y (y ∈ X ↔ first y ∨ ∃x (x ∈ X ∧ y = x + q))`.
`lenMod q r` says `w.length ≡ r (mod q)`: either the word is empty and `r = 0`, or
`∃X (multOf q X ∧ ∃x ∃ℓ (x ∈ X ∧ last ℓ ∧ ℓ = x + (r' - 1)))` with `r' = if r = 0 then q else r`.
-/

namespace R002.Claude3Mso

open MSO

universe u

variable {α : Type u} {w : List α} {m k : ℕ} {ν : Fin m → ℕ} {V : Fin k → Set ℕ}

/-- the word has no positions -/
def noPos : MSO α m k := .neg (.exF (.eq 0 0))

theorem sat_noPos : Sat w (noPos : MSO α m k) ν V ↔ w.length = 0 := by
  simp only [noPos, Sat]
  constructor
  · intro h
    by_contra hne
    exact h ⟨0, by omega, trivial⟩
  · rintro h ⟨x, hx, -⟩
    omega

/-- `X` is the set of positions divisible by `q` -/
def multOf (q : ℕ) (X : Fin k) : MSO α m k :=
  allF (iff (.mem 0 X) (or (isFirst 0) (.exF (.and (.mem 0 X) (addEq q 0 (Fin.succ 0))))))

theorem sat_multOf (q : ℕ) (X : Fin k) :
    Sat w (multOf q X : MSO α m k) ν V ↔
      ∀ y, y < w.length → (y ∈ V X ↔ y = 0 ∨ ∃ x, x < w.length ∧ x ∈ V X ∧ y = x + q) := by
  simp only [multOf, sat_allF, sat_iff, sat_or, Sat]
  refine forall_congr' fun y => forall_congr' fun hy => ?_
  rw [sat_isFirst_of_lt _ (by simpa using hy)]
  simp only [Fin.cons_zero]
  refine iff_congr Iff.rfl (or_congr Iff.rfl (exists_congr fun x => and_congr_right fun _ =>
    and_congr_right fun _ => ?_))
  rw [sat_addEq q 0 (Fin.succ 0) _ (by simpa using hy)]
  simp

theorem multOf_mem_iff {q : ℕ} (hq : 0 < q) {X : Set ℕ}
    (h : ∀ y, y < w.length → (y ∈ X ↔ y = 0 ∨ ∃ x, x < w.length ∧ x ∈ X ∧ y = x + q)) :
    ∀ y, y < w.length → (y ∈ X ↔ q ∣ y) := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy
    rw [h y hy]
    rcases Nat.eq_zero_or_pos y with rfl | hpos
    · simp
    · constructor
      · rintro (h0 | ⟨x, hx, hxX, rfl⟩)
        · omega
        · exact Nat.dvd_add ((ih x (by omega) hx).1 hxX) dvd_rfl
      · intro hd
        have hqy : q ≤ y := Nat.le_of_dvd hpos hd
        exact Or.inr ⟨y - q, by omega, (ih _ (by omega) (by omega)).2 (Nat.dvd_sub hd dvd_rfl),
          by omega⟩

theorem multOf_exists {q : ℕ} (hq : 0 < q) :
    ∀ y, y < w.length → (y ∈ {i | i < w.length ∧ q ∣ i} ↔
      y = 0 ∨ ∃ x, x < w.length ∧ x ∈ {i | i < w.length ∧ q ∣ i} ∧ y = x + q) := by
  intro y hy
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨-, hd⟩
    rcases Nat.eq_zero_or_pos y with h0 | hpos
    · exact Or.inl h0
    · have hqy : q ≤ y := Nat.le_of_dvd hpos hd
      exact Or.inr ⟨y - q, by omega, ⟨by omega, Nat.dvd_sub hd dvd_rfl⟩, by omega⟩
  · rintro (rfl | ⟨x, -, ⟨-, hd⟩, rfl⟩)
    · exact ⟨hy, dvd_zero q⟩
    · exact ⟨hy, Nat.dvd_add hd dvd_rfl⟩

theorem lenMod_arith {q r n : ℕ} (hr : r < q) (hn : 0 < n) :
    (∃ x, q ∣ x ∧ n = x + (if r = 0 then q else r)) ↔ n % q = r := by
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    split_ifs with h
    · rw [Nat.mod_self, h]
    · exact Nat.mod_eq_of_lt hr
  · intro h
    have e := Nat.mod_add_div n q
    rw [h] at e
    split_ifs with h0
    · subst h0
      generalize n / q = a at e
      cases a with
      | zero => omega
      | succ a =>
        exact ⟨q * a, dvd_mul_right q a, by rw [Nat.mul_succ] at e; omega⟩
    · exact ⟨q * (n / q), dvd_mul_right q _, by omega⟩

/-- `lenMod q r`: the length of the word is `≡ r (mod q)`. -/
def lenMod (q r : ℕ) : MSO α m k :=
  or (.and noPos (if r = 0 then tt else ff))
    (.exS (.and (multOf q 0) (.exF (.exF (.and (.mem (Fin.succ 0) 0)
      (.and (isLast 0) (addEq ((if r = 0 then q else r) - 1) (Fin.succ 0) 0)))))))

theorem sat_lenMod {q r : ℕ} (hq : 0 < q) (hr : r < q) :
    Sat w (lenMod q r : MSO α m k) ν V ↔ w.length % q = r := by
  simp only [lenMod, sat_or, Sat, sat_noPos]
  rcases Nat.eq_zero_or_pos w.length with hn | hn
  · rw [hn]
    constructor
    · rintro (⟨-, h⟩ | ⟨X, -, -, x, hx, -⟩)
      · split_ifs at h with h0
        · simp [h0]
        · exact absurd h sat_ff
      · omega
    · intro h
      rw [Nat.zero_mod] at h
      subst h
      exact Or.inl ⟨rfl, by simp⟩
  · have hne : w.length ≠ 0 := by omega
    simp only [hne, false_and, false_or]
    rw [← lenMod_arith hr hn]
    set r' := if r = 0 then q else r with hr'
    have hr'pos : 0 < r' := by rw [hr']; split_ifs <;> omega
    constructor
    · rintro ⟨X, hX, hm, x, hx, ℓ, hℓ, hxX, hlast, hadd⟩
      rw [sat_multOf] at hm
      simp only [Fin.cons_zero, Fin.cons_succ] at hm hxX
      rw [sat_isLast_of_lt _ (by simpa using hℓ)] at hlast
      rw [sat_addEq _ _ _ _ (by simpa using hℓ)] at hadd
      simp only [Fin.cons_zero, Fin.cons_succ] at hlast hadd
      exact ⟨x, (multOf_mem_iff hq hm x hx).1 hxX, by omega⟩
    · rintro ⟨x, hd, hnx⟩
      refine ⟨{i | i < w.length ∧ q ∣ i}, fun i hi => hi.1, ?_, x, by omega, w.length - 1,
        by omega, ?_, ?_, ?_⟩
      · rw [sat_multOf]
        simpa only [Fin.cons_zero] using multOf_exists hq
      · simp only [Fin.cons_zero, Fin.cons_succ]
        exact ⟨by omega, hd⟩
      · rw [sat_isLast_of_lt _ (by simp; omega)]
        simp; omega
      · rw [sat_addEq _ _ _ _ (by simp; omega)]
        simp; omega

/-- `w ⊨ lenMod q r ↔ |w| ≡ r (mod q)` for the sentence version. -/
theorem models_lenMod {q r : ℕ} (hq : 0 < q) (hr : r < q) :
    Models w (lenMod q r) ↔ w.length % q = r :=
  sat_lenMod hq hr

/-- Example application of the main theorem: `{w | |w| % q = r}` is regular. -/
theorem isRegular_length_mod {q r : ℕ} (hq : 0 < q) (hr : r < q) :
    (modelsLang (lenMod q r : Sentence α)).IsRegular ∧
      ∀ w : List α, w ∈ modelsLang (lenMod q r : Sentence α) ↔ w.length % q = r :=
  ⟨isRegular_modelsLang _, fun _ => models_lenMod hq hr⟩

end R002.Claude3Mso
