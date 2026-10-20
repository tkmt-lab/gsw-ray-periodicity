import Formal.Claude5D14StripHelp

/-!
# D14 model: tools for the explicit paths at parameter one

Written by a Claude worker (2026-10-20, D14 bridge session), adapting `Claude5O2SuffBase.lean`.

* `deg_eq_of` : the degree of a vertex whose neighbours are exactly an explicit list;
* `fib_int0`, `fib_int1`, `fib_seam` : the chart points of a vertex;
* `deg_int0`, `deg_int1` : interior points of a chart have degree six;
* `deg_seam_eq` : the degree of a seam point from its neighbours in the two charts;
* `literal_of_strip` : a strip whose points are pairwise distinct and whose ends have the right
  degrees gives a literal path.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Equality of explicit lattice points, with sums of pairs. -/
macro "peq2" : tactic => `(tactic| (first | rfl | (simp only [Prod.mk.injEq, Prod.ext_iff,
  Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, true_and, and_true] <;> omega)))

namespace Claude5D14

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

theorem deg_eq_of (v : MS r s) (L : List MV) (hnd : L.Nodup) (hval : ∀ w ∈ L, Valid r s w)
    (hadj : ∀ w ∈ L, AdjM r s v.1 w) (hsub : ∀ w, AdjM r s v.1 w → w ∈ L) :
    deg (GM r s) v = L.length := by
  unfold deg
  have hset : (GM r s).neighborSet v = Subtype.val ⁻¹' {x | x ∈ L} := by
    ext w
    simp only [SimpleGraph.mem_neighborSet, Set.mem_preimage, Set.mem_setOf_eq]
    exact ⟨fun h => hsub _ h, fun h => hadj _ h⟩
  rw [hset]
  have himg : Subtype.val '' (Subtype.val ⁻¹' {x | x ∈ L} : Set (MS r s)) = {x | x ∈ L} := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hx; exact ⟨⟨x, hval x hx⟩, hx, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg]
  rw [show {x | x ∈ L} = (L.toFinset : Set MV) by ext; simp, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

theorem fib_int0 {c : ℕ} (hc : c < 2) {z z0 : ℤ × ℤ} (e : ch r s c z = (0, z0)) :
    c = 0 ∧ z = z0 := by
  rcases c_cases hc with rfl | rfl
  · by_cases h : I0 r s z
    · rw [ch0_I h] at e; exact ⟨rfl, congrArg Prod.snd e⟩
    · rw [ch0_B h] at e; simp at e
  · by_cases h : I1 r s z
    · rw [ch1_I h] at e; simp at e
    · rw [ch1_B h] at e; simp at e

theorem fib_int1 {c : ℕ} (hc : c < 2) {z z0 : ℤ × ℤ} (e : ch r s c z = (1, z0)) :
    c = 1 ∧ z = z0 := by
  rcases c_cases hc with rfl | rfl
  · by_cases h : I0 r s z
    · rw [ch0_I h] at e; simp at e
    · rw [ch0_B h] at e; simp at e
  · by_cases h : I1 r s z
    · rw [ch1_I h] at e; exact ⟨rfl, congrArg Prod.snd e⟩
    · rw [ch1_B h] at e; simp at e

theorem fib_seam (hr : 1 ≤ r) (hs : 1 ≤ s) {c : ℕ} (hc : c < 2) {z : ℤ × ℤ} {l : ℤ}
    (hz : Dom r s c z) (e : ch r s c z = (2, (l, 0))) :
    (c = 0 ∧ z = P0 r s l) ∨ (c = 1 ∧ z = P1 r s l) := by
  rcases c_cases hc with rfl | rfl
  · by_cases h : I0 r s z
    · rw [ch0_I h] at e; simp at e
    · rw [ch0_B h] at e
      simp only [Prod.mk.injEq, true_and, and_true] at e
      left; refine ⟨rfl, ?_⟩
      rw [← e]; exact eq_P0 hr hs hz h
  · by_cases h : I1 r s z
    · rw [ch1_I h] at e; simp at e
    · rw [ch1_B h] at e
      simp only [Prod.mk.injEq, true_and, and_true] at e
      right; refine ⟨rfl, ?_⟩
      rw [← e]; exact eq_P1 hr hs hz h

/-- The neighbours of a chart point all come from its chart points. -/
theorem adj_rep {v w : MV} (h : AdjM r s v w) :
    ∃ c, c < 2 ∧ ∃ z u, Dom r s c z ∧ Dom r s c (z + u) ∧ u ∈ unitVec ∧ ch r s c z = v ∧
      w = ch r s c (z + u) := by
  obtain ⟨-, c, hc, z, u, h1, h2, hu, e1, e2⟩ := h
  exact ⟨c, hc, z, u, h1, h2, hu, e1, e2.symm⟩

/-- An interior point of one chart has degree six. -/
theorem deg_int (hr : 1 ≤ r) (hs : 1 ≤ s) {c : ℕ} (hc : c < 2) (v : MS r s) {z : ℤ × ℤ}
    (hz : Dom r s c z) (hI : Inn r s c z) (hv : v.1 = ch r s c z)
    (hall : ∀ u ∈ unitVec, Dom r s c (z + u)) : deg (GM r s) v = 6 := by
  have hm : ∀ u : ℤ × ℤ, u ∈ unitVec ↔ _ := fun u => unit_iff (u := u)
  have h1 : (1, 0) ∈ unitVec := by simp [unit_iff]
  have h2 : (0, 1) ∈ unitVec := by simp [unit_iff]
  have h3 : (-1, 1) ∈ unitVec := by simp [unit_iff]
  have h4 : (-1, 0) ∈ unitVec := by simp [unit_iff]
  have h5 : (0, -1) ∈ unitVec := by simp [unit_iff]
  have h6 : (1, -1) ∈ unitVec := by simp [unit_iff]
  have hN : ∀ u ∈ unitVec, ∀ u' ∈ unitVec, u ≠ u' → ch r s c (z + u) ≠ ch r s c (z + u') :=
    fun u hu u' hu' hne => ne_same hr hs hc (hall u hu) (hall u' hu') (by simpa using hne)
  refine deg_eq_of v [ch r s c (z + (1, 0)), ch r s c (z + (0, 1)), ch r s c (z + (-1, 1)),
    ch r s c (z + (-1, 0)), ch r s c (z + (0, -1)), ch r s c (z + (1, -1))] ?_ ?_ ?_ ?_
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
      exact hN _ (by assumption) _ (by assumption) (by simp)
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ch_valid hr hs hc (hall _ (by assumption))
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact adj_of_unit hr hs hc hz (hall _ (by assumption)) (by assumption) hv
  · intro w hw
    obtain ⟨c', hc', z', u, hz', hzu, hu, e1, rfl⟩ := adj_rep hw
    rw [hv, ch_I hc hI] at e1
    have : c' = c ∧ z' = z := by
      rcases c_cases hc with rfl | rfl
      · exact fib_int0 hc' e1
      · exact fib_int1 hc' e1
    obtain ⟨rfl, rfl⟩ := this
    rw [unit_iff] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem deg_int0 (hr : 1 ≤ r) (hs : 1 ≤ s) (v : MS r s) {z : ℤ × ℤ} (hI : I0 r s z)
    (hv : v.1 = ch r s 0 z) : deg (GM r s) v = 6 := by
  have hz : Dom r s 0 z := by simp only [Dom, H0]; simp only [I0] at hI; omega
  refine deg_int hr hs (c := 0) (by norm_num) v hz hI hv (fun u hu => ?_)
  rw [unit_iff] at hu
  simp only [I0] at hI
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Dom, H0] <;> omega

theorem deg_int1 (hr : 1 ≤ r) (hs : 1 ≤ s) (v : MS r s) {z : ℤ × ℤ} (hI : I1 r s z)
    (hv : v.1 = ch r s 1 z) : deg (GM r s) v = 6 := by
  have hz : Dom r s 1 z := by simp only [Dom, H1]; simp only [I1] at hI; omega
  refine deg_int hr hs (c := 1) (by norm_num) v hz hI hv (fun u hu => ?_)
  rw [unit_iff] at hu
  simp only [I1] at hI
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Dom, H1] <;> omega

/-- The degree of a seam point from its chart neighbourhoods. -/
theorem deg_seam_eq (hr : 1 ≤ r) (hs : 1 ≤ s) (v : MS r s) {l : ℤ} (hv : v.1 = (2, (l, 0)))
    (L : List MV) (hnd : L.Nodup) (hval : ∀ w ∈ L, Valid r s w)
    (hadj : ∀ w ∈ L, AdjM r s v.1 w)
    (h0 : ∀ u ∈ unitVec, Dom r s 0 (P0 r s l + u) → ch r s 0 (P0 r s l + u) ∈ L)
    (h1 : ∀ u ∈ unitVec, Dom r s 1 (P1 r s l + u) → ch r s 1 (P1 r s l + u) ∈ L) :
    deg (GM r s) v = L.length := by
  refine deg_eq_of v L hnd hval hadj (fun w hw => ?_)
  obtain ⟨c, hc, z, u, hz, hzu, hu, e1, rfl⟩ := adj_rep hw
  rw [hv] at e1
  rcases fib_seam hr hs hc hz e1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h0 u hu hzu
  · exact h1 u hu hzu

theorem ch_ne_of (hr : 1 ≤ r) (hs : 1 ≤ s) {c c' : ℕ} (hc : c < 2) (hc' : c' < 2)
    {p p' : ℤ × ℤ} (h1 : Dom r s c p) (h2 : Dom r s c' p') (h : ¬ (c = c' ∧ p = p'))
    (ha : ¬ (c = 0 ∧ c' = 1 ∧ ¬ I0 r s p ∧ ¬ I1 r s p' ∧ a0 r s p = a1 r s p'))
    (hb : ¬ (c = 1 ∧ c' = 0 ∧ ¬ I1 r s p ∧ ¬ I0 r s p' ∧ a1 r s p = a0 r s p')) :
    ch r s c p ≠ ch r s c' p' := by
  intro e
  rcases ch_eq hr hs hc hc' h1 h2 e with h' | h' | h'
  exacts [h h', ha h', hb h']

/-- A strip of `N ≥ n - 1` steps with distinct points and the right end degrees is a literal
path. -/
theorem literal_of_strip {W : ℕ → MV} {N n : ℕ} (hS : StripOK r s W N) (hn : n ≤ N + 1)
    (h4 : 4 ≤ n) (hev : Even n) (hinj : ∀ i j, i < n → j < n → W i = W j → i = j)
    (p : ℕ → MS r s) (hp : ∀ k, k ≤ N → (p k).1 = W k)
    (d0 : deg (GM r s) (p 0) = 5) (d1 : deg (GM r s) (p (n - 1)) = 5)
    (d2 : deg (GM r s) (p 1) = 6) (d3 : deg (GM r s) (p (n - 2)) = 6) :
    LiteralPath (GM r s) n p := by
  refine ⟨h4, hev, fun i j hi hj e => hinj i j hi hj ?_, fun i hi => ?_, fun i hi => ?_,
    d0, d1, d2, d3⟩
  · rw [← hp i (by omega), ← hp j (by omega), e]
  · show AdjM r s (p i).1 (p (i + 1)).1
    rw [hp i (by omega), hp (i + 1) (by omega)]; exact hS.2.1 i (by omega)
  · show AdjM r s (p i).1 (p (i + 2)).1
    rw [hp i (by omega), hp (i + 2) (by omega)]; exact hS.2.2.1 i (by omega)

end Claude5D14
