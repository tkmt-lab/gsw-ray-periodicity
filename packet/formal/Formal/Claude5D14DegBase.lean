import Formal.Claude5D14Three

/-!
# D14 model: tools for degrees

Written by a Claude worker (2026-10-20, D14 bridge session), adapting `Claude5O2DegBase.lean`.

* `corners`         : the twelve label corners, seam points at arclength
                      `⌊j/2⌋ (r + s) + (j mod 2) s`;
* `deg_ne_five_of6` : six distinct neighbours rule out degree five;
* `adj_of_unit`, `adj_via`, `ne_same`, `ne_01` : adjacency and distinctness of chart points;
* `deg_interior`    : an interior point of a chart does not have degree five.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Claude5D14

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

/-- The twelve label corners, in label order. -/
def corners (r s : ℤ) : List MV :=
  [(2, (0, 0)), (2, (s, 0)), (2, (r + s, 0)), (2, (r + 2 * s, 0)), (2, (2 * r + 2 * s, 0)),
   (2, (2 * r + 3 * s, 0)), (2, (3 * r + 3 * s, 0)), (2, (3 * r + 4 * s, 0)),
   (2, (4 * r + 4 * s, 0)), (2, (4 * r + 5 * s, 0)), (2, (5 * r + 5 * s, 0)),
   (2, (5 * r + 6 * s, 0))]

def IsCorner (r s : ℤ) (v : MV) : Prop := v ∈ corners r s

theorem deg_ne_five_of6 (v : MS r s) (w0 w1 w2 w3 w4 w5 : MV) (h0 : Valid r s w0)
    (h1 : Valid r s w1) (h2 : Valid r s w2) (h3 : Valid r s w3) (h4 : Valid r s w4)
    (h5 : Valid r s w5) (a0 : AdjM r s v.1 w0) (a1 : AdjM r s v.1 w1) (a2 : AdjM r s v.1 w2)
    (a3 : AdjM r s v.1 w3) (a4 : AdjM r s v.1 w4) (a5 : AdjM r s v.1 w5)
    (n01 : w0 ≠ w1) (n02 : w0 ≠ w2) (n03 : w0 ≠ w3) (n04 : w0 ≠ w4) (n05 : w0 ≠ w5)
    (n12 : w1 ≠ w2) (n13 : w1 ≠ w3) (n14 : w1 ≠ w4) (n15 : w1 ≠ w5) (n23 : w2 ≠ w3)
    (n24 : w2 ≠ w4) (n25 : w2 ≠ w5) (n34 : w3 ≠ w4) (n35 : w3 ≠ w5) (n45 : w4 ≠ w5) :
    deg (GM r s) v ≠ 5 := by
  intro h
  let W : Fin 6 → MV := ![w0, w1, w2, w3, w4, w5]
  have hW : ∀ k, Valid r s (W k) := by
    intro k; fin_cases k <;> simp [W] <;> assumption
  have hA : ∀ k, AdjM r s v.1 (W k) := by
    intro k; fin_cases k <;> simp [W] <;> assumption
  let f : Fin 6 → MS r s := fun k => ⟨W k, hW k⟩
  have finj : Function.Injective f := by
    intro k k' e
    have e' : W k = W k' := congrArg Subtype.val e
    fin_cases k <;> fin_cases k' <;> simp [W] at e' ⊢ <;> simp_all [eq_comm]
  have hsub : Set.range f ⊆ (GM r s).neighborSet v := by
    rintro _ ⟨k, rfl⟩
    exact hA k
  unfold deg at h
  by_cases hfin : ((GM r s).neighborSet v).Finite
  · have := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_range_of_injective finj] at this
    simp at this
    omega
  · rw [Set.Infinite.ncard hfin] at h
    omega

theorem unit_ne_zero {u : ℤ × ℤ} (h : u ∈ unitVec) : u ≠ 0 := by
  rw [unit_iff] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Prod.ext_iff]

theorem ne_same (hr : 1 ≤ r) (hs : 1 ≤ s) {c : ℕ} (hc : c < 2) {ρ ρ' : ℤ × ℤ}
    (h1 : Dom r s c ρ) (h2 : Dom r s c ρ') (h : ρ ≠ ρ') : ch r s c ρ ≠ ch r s c ρ' :=
  fun e => h (ch_inj hr hs hc h1 h2 e)

theorem adj_of_unit (hr : 1 ≤ r) (hs : 1 ≤ s) {c : ℕ} (hc : c < 2) {P u : ℤ × ℤ} {v : MV}
    (hP : Dom r s c P) (hPu : Dom r s c (P + u)) (hu : u ∈ unitVec) (hv : v = ch r s c P) :
    AdjM r s v (ch r s c (P + u)) := by
  refine ⟨?_, c, hc, P, u, hP, hPu, hu, hv.symm, rfl⟩
  rw [hv]
  exact ne_same hr hs hc hP hPu (fun e => unit_ne_zero hu (by
    have : P + u - P = P - P := by rw [← e]
    simpa using this))

theorem adj_via (hr : 1 ≤ r) (hs : 1 ≤ s) {c : ℕ} {P Q : ℤ × ℤ} (hc : c < 2) {v w : MV}
    (hP : Dom r s c P) (hQ : Dom r s c Q) (hu : Q - P ∈ unitVec) (e1 : v = ch r s c P)
    (e2 : w = ch r s c Q) : AdjM r s v w := by
  have := adj_of_unit hr hs hc hP (by simpa using hQ) hu e1
  rw [e2]; simpa using this

theorem ne_01 {ρ ρ' : ℤ × ℤ} (h : I0 r s ρ ∨ I1 r s ρ' ∨ a0 r s ρ ≠ a1 r s ρ') :
    ch r s 0 ρ ≠ ch r s 1 ρ' := by
  intro e
  obtain ⟨a, b, c⟩ := ch_eq01 e
  rcases h with h | h | h
  exacts [a h, b h, h c]

/-- Points with all six chart neighbours have degree at least six. -/
theorem deg_interior (hr : 1 ≤ r) (hs : 1 ≤ s) {c : ℕ} (hc : c < 2) (v : MS r s)
    {ρ : ℤ × ℤ} (hρ : Dom r s c ρ) (hv : v.1 = ch r s c ρ)
    (hall : ∀ u ∈ unitVec, Dom r s c (ρ + u)) : deg (GM r s) v ≠ 5 := by
  have hU : ∀ u ∈ unitVec, Valid r s (ch r s c (ρ + u)) :=
    fun u hu => ch_valid hr hs hc (hall u hu)
  have hA : ∀ u ∈ unitVec, AdjM r s v.1 (ch r s c (ρ + u)) :=
    fun u hu => adj_of_unit hr hs hc hρ (hall u hu) hu hv
  have hN : ∀ u ∈ unitVec, ∀ u' ∈ unitVec, u ≠ u' → ch r s c (ρ + u) ≠ ch r s c (ρ + u') :=
    fun u hu u' hu' hne => ne_same hr hs hc (hall u hu) (hall u' hu') (by simpa using hne)
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

end Claude5D14
