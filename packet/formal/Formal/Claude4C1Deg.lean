import Formal.Claude4C1G4

/-!
# The `ℤ⁴` model of C1: degrees

Written by a Claude worker (2026-10-20, C1 bridge session).

The neighbours of `x` are the points `x + e_i - e_j` with `x_i < r + s`, `0 < x_j` and some third
coordinate in `{0, r + s}` (`NC`).  Whether `(i, j)` qualifies depends only on which coordinates
are `0` and which are `r + s`; a finite check over these patterns (`pattern_deg`) gives

* `deg_g4` : `deg (G4 r s) x = if CornerP r s x then 5 else 6` (`0 < r`, `0 < s`), where
  `CornerP` says that one coordinate is `r + s` and two are `0` (the twelve corners).
-/

namespace Claude4C1

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

/-- Corner points: one coordinate `r + s` and two coordinates `0`. -/
def CornerP (r s : ℤ) (x : Fin 4 → ℤ) : Prop :=
  (∃ a, x a = r + s) ∧ ∃ b c, b ≠ c ∧ x b = 0 ∧ x c = 0

/-- `(i, j)` gives a neighbour `x + e_i - e_j` of `x`. -/
def NC (r s : ℤ) (x : Fin 4 → ℤ) (p : Fin 4 × Fin 4) : Prop :=
  p.1 ≠ p.2 ∧ x p.1 ≠ r + s ∧ x p.2 ≠ 0 ∧ ∃ k, k ≠ p.1 ∧ k ≠ p.2 ∧ (x k = 0 ∨ x k = r + s)

/-- The same condition on the zero/top pattern. -/
def NCB (z m : Fin 4 → Bool) (p : Fin 4 × Fin 4) : Prop :=
  p.1 ≠ p.2 ∧ m p.1 = false ∧ z p.2 = false ∧ ∃ k, k ≠ p.1 ∧ k ≠ p.2 ∧ (z k = true ∨ m k = true)

instance (z m : Fin 4 → Bool) : DecidablePred (NCB z m) := fun _ => by
  unfold NCB; infer_instance

/-- Patterns that occur on the surface. -/
def Feas (z m : Fin 4 → Bool) : Prop :=
  (∀ k, ¬ (z k = true ∧ m k = true)) ∧ (∀ a b, a ≠ b → ¬ (m a = true ∧ m b = true)) ∧
    (∀ a b c, a ≠ b → a ≠ c → b ≠ c → ¬ (z a = true ∧ z b = true ∧ z c = true))

instance (z m : Fin 4 → Bool) : Decidable (Feas z m) := by unfold Feas; infer_instance

def CornerB (z m : Fin 4 → Bool) : Prop :=
  (∃ a, m a = true) ∧ ∃ b c, b ≠ c ∧ z b = true ∧ z c = true

instance (z m : Fin 4 → Bool) : Decidable (CornerB z m) := by unfold CornerB; infer_instance

instance (r s : ℤ) (x : Fin 4 → ℤ) : Decidable (CornerP r s x) := by
  unfold CornerP; infer_instance

theorem pattern_deg : ∀ z0 z1 z2 z3 m0 m1 m2 m3 : Bool,
    Feas ![z0, z1, z2, z3] ![m0, m1, m2, m3] →
    (∃ k, ![z0, z1, z2, z3] k = true ∨ ![m0, m1, m2, m3] k = true) →
    (Finset.univ.filter (NCB ![z0, z1, z2, z3] ![m0, m1, m2, m3])).card =
      if CornerB ![z0, z1, z2, z3] ![m0, m1, m2, m3] then 5 else 6 := by
  decide

/-- The zero pattern and the top pattern of `x`. -/
def zb (x : Fin 4 → ℤ) : Fin 4 → Bool := fun t => decide (x t = 0)
def mb (r s : ℤ) (x : Fin 4 → ℤ) : Fin 4 → Bool := fun t => decide (x t = r + s)

theorem zb_eq (x : Fin 4 → ℤ) : zb x = ![zb x 0, zb x 1, zb x 2, zb x 3] := by
  funext t; fin_cases t <;> rfl

theorem mb_eq (x : Fin 4 → ℤ) : mb r s x = ![mb r s x 0, mb r s x 1, mb r s x 2, mb r s x 3] := by
  funext t; fin_cases t <;> rfl

theorem sum2_le {x : Fin 4 → ℤ} (h : InS r s x) {a b : Fin 4} (hab : a ≠ b) :
    x a + x b ≤ 2 * r + s := by
  have h' := inS_iff.1 h
  fin_cases a <;> fin_cases b <;> simp_all <;> omega

theorem sum3_le {x : Fin 4 → ℤ} (h : InS r s x) {a b c : Fin 4} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : 2 * r + s ≤ x a + x b + x c + (r + s) := by
  have h' := inS_iff.1 h
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all <;> omega

theorem feas_of_inS (hr : 0 < r) (hs : 0 < s) {x : Fin 4 → ℤ} (h : InS r s x) :
    Feas (zb x) (mb r s x) := by
  refine ⟨fun k hk => ?_, fun a b hab hm => ?_, fun a b c hab hac hbc hz => ?_⟩
  · simp only [zb, mb, decide_eq_true_eq] at hk; omega
  · simp only [mb, decide_eq_true_eq] at hm
    have := sum2_le h hab; omega
  · simp only [zb, decide_eq_true_eq] at hz
    have := sum3_le h hab hac hbc; omega

theorem cornerB_iff {x : Fin 4 → ℤ} : CornerB (zb x) (mb r s x) ↔ CornerP r s x := by
  simp [CornerB, CornerP, zb, mb]

theorem nc_iff {x : Fin 4 → ℤ} (p : Fin 4 × Fin 4) : NC r s x p ↔ NCB (zb x) (mb r s x) p := by
  simp [NC, NCB, zb, mb]

theorem inS_add_rt {x : Fin 4 → ℤ} (h : InS r s x) {i j : Fin 4} (hn : NC r s x (i, j)) :
    InS r s (x + rt i j) := by
  obtain ⟨hij, hi, hj, k, hki, hkj, hk⟩ := hn
  simp only at hij hi hj hki hkj
  obtain ⟨h1, h2, -⟩ := h
  refine ⟨fun t => ?_, ?_, k, by rw [add_rt_ne x hki hkj]; exact hk⟩
  · by_cases hti : t = i
    · rw [hti, add_rt_left x hij]; have := h1 i; omega
    by_cases htj : t = j
    · rw [htj, add_rt_right x hij]; have := h1 j; omega
    rw [add_rt_ne x hti htj]; exact h1 t
  · have : ∑ t, rt i j t = 0 := by
      simp [rt, Finset.sum_sub_distrib]
    simp only [Pi.add_apply, Finset.sum_add_distrib, this, h2, add_zero]

theorem rt_inj : ∀ i j i' j' : Fin 4, i ≠ j → (∀ t, rt i j t = rt i' j' t) → i = i' ∧ j = j' := by
  unfold rt; decide

theorem deg_g4 (hr : 0 < r) (hs : 0 < s) (x : Surf r s) :
    deg (G4 r s) x = if CornerP r s x.1 then 5 else 6 := by
  have e0 : {p : Fin 4 × Fin 4 | NC r s x.1 p}.ncard = deg (G4 r s) x := by
    refine Set.ncard_congr (fun p hp => (⟨x.1 + rt p.1 p.2, inS_add_rt x.2 hp⟩ : Surf r s))
      ?_ ?_ ?_
    · rintro ⟨i, j⟩ hp
      obtain ⟨hij, -, -, k, hki, hkj, hk⟩ := hp
      exact ⟨i, j, hij, rfl, k, hki, hkj, hk⟩
    · rintro ⟨i, j⟩ ⟨i', j'⟩ hp hp' he
      have he' := congrArg Subtype.val he
      simp only [add_right_inj] at he'
      obtain ⟨h1, h2⟩ := rt_inj i j i' j' hp.1 (fun t => congrFun he' t)
      rw [h1, h2]
    · intro y hy
      obtain ⟨i, j, hij, hyx, k, hki, hkj, hk⟩ := hy
      have hyi := (y.2.1 i).2
      have hyj := (y.2.1 j).1
      rw [hyx, add_rt_left _ hij] at hyi
      rw [hyx, add_rt_right _ hij] at hyj
      exact ⟨(i, j), ⟨hij, show x.1 i ≠ r + s by omega, show x.1 j ≠ 0 by omega, k, hki, hkj, hk⟩,
        Subtype.ext hyx.symm⟩
  have e1 : {p : Fin 4 × Fin 4 | NC r s x.1 p}.ncard =
      (Finset.univ.filter (NCB (zb x.1) (mb r s x.1))).card := by
    rw [← Set.ncard_coe_finset]; congr 1; ext p; simp [nc_iff]
  have hF := feas_of_inS hr hs x.2
  obtain ⟨k, hk⟩ := x.2.2.2
  have hK : ∃ k, zb x.1 k = true ∨ mb r s x.1 k = true := ⟨k, by simp [zb, mb]; exact hk⟩
  rw [zb_eq, mb_eq] at hF hK
  have key := pattern_deg _ _ _ _ _ _ _ _ hF hK
  rw [← zb_eq, ← mb_eq] at key
  rw [← e0, e1, key]
  by_cases h : CornerP r s x.1
  · rw [if_pos h, if_pos (cornerB_iff.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (cornerB_iff.1 h'))]

end Claude4C1
