import Formal.Claude5O2Three

/-!
# O2 model: tools for degrees

Written by a Claude worker (2026-10-20, O2 bridge session).

* `corners`         : the twelve signature vertices `Aᵢ, Bᵢ, Cᵢ` (sheet 0) and `Dᵢ` (sheet 1);
* `deg_ne_five_of6` : six distinct neighbours rule out degree five;
* `adj_of_unit`, `ne_same`, `ne_01`, `ne_0R`, `ne_1R` : adjacency and distinctness of chart
  points.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

variable {t d : ℤ}

/-- The twelve corners: `Aᵢ = sp i 0`, `Bᵢ = sp i t`, `Cᵢ = sp i (2t)` on sheet 0, `Dᵢ = sp i t`
on sheet 1. -/
def corners (t d : ℤ) : List MV :=
  [(0, sp t d 0 0), (0, sp t d 0 t), (0, sp t d 0 (2 * t)), (1, sp t d 0 t),
   (0, sp t d 1 0), (0, sp t d 1 t), (0, sp t d 1 (2 * t)), (1, sp t d 1 t),
   (0, sp t d 2 0), (0, sp t d 2 t), (0, sp t d 2 (2 * t)), (1, sp t d 2 t)]

def IsCorner (t d : ℤ) (v : MV) : Prop := v ∈ corners t d

theorem deg_ne_five_of6 (v : MS t d) (w0 w1 w2 w3 w4 w5 : MV) (h0 : Valid t d w0)
    (h1 : Valid t d w1) (h2 : Valid t d w2) (h3 : Valid t d w3) (h4 : Valid t d w4)
    (h5 : Valid t d w5) (a0 : AdjM t d v.1 w0) (a1 : AdjM t d v.1 w1) (a2 : AdjM t d v.1 w2)
    (a3 : AdjM t d v.1 w3) (a4 : AdjM t d v.1 w4) (a5 : AdjM t d v.1 w5)
    (n01 : w0 ≠ w1) (n02 : w0 ≠ w2) (n03 : w0 ≠ w3) (n04 : w0 ≠ w4) (n05 : w0 ≠ w5)
    (n12 : w1 ≠ w2) (n13 : w1 ≠ w3) (n14 : w1 ≠ w4) (n15 : w1 ≠ w5) (n23 : w2 ≠ w3)
    (n24 : w2 ≠ w4) (n25 : w2 ≠ w5) (n34 : w3 ≠ w4) (n35 : w3 ≠ w5) (n45 : w4 ≠ w5) :
    deg (GM t d) v ≠ 5 := by
  intro h
  let W : Fin 6 → MV := ![w0, w1, w2, w3, w4, w5]
  have hW : ∀ k, Valid t d (W k) := by
    intro k; fin_cases k <;> simp [W] <;> assumption
  have hA : ∀ k, AdjM t d v.1 (W k) := by
    intro k; fin_cases k <;> simp [W] <;> assumption
  let f : Fin 6 → MS t d := fun k => ⟨W k, hW k⟩
  have finj : Function.Injective f := by
    intro k k' e
    have e' : W k = W k' := congrArg Subtype.val e
    fin_cases k <;> fin_cases k' <;> simp [W] at e' ⊢ <;> simp_all [eq_comm]
  have hsub : Set.range f ⊆ (GM t d).neighborSet v := by
    rintro _ ⟨k, rfl⟩
    exact hA k
  unfold deg at h
  by_cases hfin : ((GM t d).neighborSet v).Finite
  · have := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_range_of_injective finj] at this
    simp at this
    omega
  · rw [Set.Infinite.ncard hfin] at h
    omega

theorem unit_ne_zero {u : ℤ × ℤ} (h : u ∈ unitVec) : u ≠ 0 := by
  rw [unit_iff] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Prod.ext_iff]

theorem ne_same (ht : 1 ≤ t) {c : ℕ} (hc : c < 5) {ρ ρ' : ℤ × ℤ} (h1 : Dom t d c ρ)
    (h2 : Dom t d c ρ') (h : ρ ≠ ρ') : ch t d c ρ ≠ ch t d c ρ' :=
  fun e => h (ch_inj ht hc h1 h2 e)

theorem adj_of_unit (ht : 1 ≤ t) {c : ℕ} (hc : c < 5) {P u : ℤ × ℤ} {v : MV}
    (hP : Dom t d c P) (hPu : Dom t d c (P + u)) (hu : u ∈ unitVec) (hv : v = ch t d c P) :
    AdjM t d v (ch t d c (P + u)) := by
  refine ⟨?_, c, hc, P, u, hP, hPu, hu, hv.symm, rfl⟩
  rw [hv]
  exact ne_same ht hc hP hPu (fun e => unit_ne_zero hu (by
    have : P + u - P = P - P := by rw [← e]
    simpa using this))

theorem ne_01 {ρ ρ' : ℤ × ℤ} (h : ρ' ≠ ρ ∨ ¬ OnD t d ρ) : ch t d 0 ρ ≠ ch t d 1 ρ' := by
  intro e
  by_cases hD : OnD t d ρ'
  · rw [ch1_onD hD, ch0] at e
    simp only [Prod.mk.injEq, true_and] at e
    subst e
    rcases h with h | h
    · exact h rfl
    · exact h hD
  · rw [ch1_nD hD, ch0] at e
    simp at e

theorem ne_0R (ht : 1 ≤ t) (hd : 1 ≤ d) {j : ℕ} (hj : j < 3) {ρ ρ' : ℤ × ℤ}
    (h1 : Dom t d 0 ρ) (h2 : Dom t d (j + 2) ρ')
    (h : ∀ l, 0 ≤ l → l ≤ 2 * t → ρ = sp t d j l → ρ' ≠ (max (l - t) 0, min l t)) :
    ch t d 0 ρ ≠ ch t d (j + 2) ρ' := by
  intro e
  rcases ch_eq ht hd (by norm_num) (by omega) h1 h2 e with ⟨hc, -⟩ | h' | h'
  · omega
  · obtain ⟨l, a0, a1, a2, a3⟩ := h'
    exact h l a0 a1 a2 a3
  · simp [Tr] at h'

theorem ne_1R (ht : 1 ≤ t) (hd : 1 ≤ d) {j : ℕ} (hj : j < 3) {ρ ρ' : ℤ × ℤ}
    (h1 : Dom t d 1 ρ) (h2 : Dom t d (j + 2) ρ')
    (h : ∀ l, 0 ≤ l → l ≤ 2 * t → ρ = sp t d j l → ρ' ≠ (min l t, max (l - t) 0)) :
    ch t d 1 ρ ≠ ch t d (j + 2) ρ' := by
  intro e
  rcases ch_eq ht hd (by norm_num) (by omega) h1 h2 e with ⟨hc, -⟩ | h' | h'
  · omega
  · obtain ⟨l, a0, a1, a2, a3⟩ := h'
    exact h l a0 a1 a2 a3
  · simp [Tr] at h'

/-- Points with all six chart neighbours have degree at least six. -/
theorem deg_interior (ht : 1 ≤ t) (hd : 1 ≤ d) {c : ℕ} (hc : c < 5) (v : MS t d)
    {ρ : ℤ × ℤ} (hρ : Dom t d c ρ) (hv : v.1 = ch t d c ρ)
    (hall : ∀ u ∈ unitVec, Dom t d c (ρ + u)) : deg (GM t d) v ≠ 5 := by
  have hU : ∀ u ∈ unitVec, Valid t d (ch t d c (ρ + u)) := fun u hu => ch_valid ht hd hc (hall u hu)
  have hA : ∀ u ∈ unitVec, AdjM t d v.1 (ch t d c (ρ + u)) :=
    fun u hu => adj_of_unit ht hc hρ (hall u hu) hu hv
  have hN : ∀ u ∈ unitVec, ∀ u' ∈ unitVec, u ≠ u' → ch t d c (ρ + u) ≠ ch t d c (ρ + u') :=
    fun u hu u' hu' hne => ne_same ht hc (hall u hu) (hall u' hu') (by simpa using hne)
  have m : ∀ u : ℤ × ℤ, u ∈ unitVec ↔ _ := fun u => unit_iff (u := u)
  exact deg_ne_five_of6 v _ _ _ _ _ _
    (hU _ (by simp [unit_iff])) (hU _ (by simp [unit_iff])) (hU _ (by simp [unit_iff]))
    (hU _ (by simp [unit_iff])) (hU _ (by simp [unit_iff])) (hU _ (by simp [unit_iff]))
    (hA (1, 0) (by simp [unit_iff])) (hA (0, 1) (by simp [unit_iff]))
    (hA (-1, 1) (by simp [unit_iff])) (hA (-1, 0) (by simp [unit_iff]))
    (hA (0, -1) (by simp [unit_iff])) (hA (1, -1) (by simp [unit_iff]))
    (hN _ (by simp [unit_iff]) _ (by simp [unit_iff]) (by simp))
    (hN _ (by simp [unit_iff]) _ (by simp [unit_iff]) (by simp))
    (hN _ (by simp [unit_iff]) _ (by simp [unit_iff]) (by simp))
    (hN _ (by simp [unit_iff]) _ (by simp [unit_iff]) (by simp))
    (hN _ (by simp [unit_iff]) _ (by simp [unit_iff]) (by simp))
    (hN _ (by simp [unit_iff]) _ (by simp [unit_iff]) (by simp))
    (hN _ (by simp [unit_iff]) _ (by simp [unit_iff]) (by simp))
    (hN _ (by simp [unit_iff]) _ (by simp [unit_iff]) (by simp))
    (hN _ (by simp [unit_iff]) _ (by simp [unit_iff]) (by simp))
    (hN _ (by simp [unit_iff]) _ (by simp [unit_iff]) (by simp))
    (hN _ (by simp [unit_iff]) _ (by simp [unit_iff]) (by simp))
    (hN _ (by simp [unit_iff]) _ (by simp [unit_iff]) (by simp))
    (hN _ (by simp [unit_iff]) _ (by simp [unit_iff]) (by simp))
    (hN _ (by simp [unit_iff]) _ (by simp [unit_iff]) (by simp))
    (hN _ (by simp [unit_iff]) _ (by simp [unit_iff]) (by simp))

end Claude5O2
