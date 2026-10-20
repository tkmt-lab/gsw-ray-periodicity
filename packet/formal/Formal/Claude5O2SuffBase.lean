import Formal.Claude5O2StripHelp

/-!
# O2 model: tools for the explicit paths at parameter one

Written by a Claude worker (2026-10-20, O2 bridge session).

* `deg_eq_of` : the degree of a vertex whose neighbours are exactly an explicit list;
* `literal_of_strip` : a strip whose points are pairwise distinct and whose ends have the right
  degrees gives a literal path.
-/

set_option linter.unusedVariables false

/-- Equality of explicit lattice points, with sums of pairs. -/
macro "peq2" : tactic => `(tactic| (first | rfl | (simp only [Claude5O2.sp, Prod.mk.injEq, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, true_and, and_true] <;> omega)))

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

variable {t d : ℤ}

theorem deg_eq_of (v : MS t d) (L : List MV) (hnd : L.Nodup) (hval : ∀ w ∈ L, Valid t d w)
    (hadj : ∀ w ∈ L, AdjM t d v.1 w) (hsub : ∀ w, AdjM t d v.1 w → w ∈ L) :
    deg (GM t d) v = L.length := by
  unfold deg
  have hset : (GM t d).neighborSet v = Subtype.val ⁻¹' {x | x ∈ L} := by
    ext w
    simp only [SimpleGraph.mem_neighborSet, Set.mem_preimage, Set.mem_setOf_eq]
    exact ⟨fun h => hsub _ h, fun h => hadj _ h⟩
  rw [hset]
  have himg : Subtype.val '' (Subtype.val ⁻¹' {x | x ∈ L} : Set (MS t d)) = {x | x ∈ L} := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hx; exact ⟨⟨x, hval x hx⟩, hx, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg]
  rw [show {x | x ∈ L} = (L.toFinset : Set MV) by ext; simp, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

theorem ch_ne_of (ht : 1 ≤ t) (hd : 1 ≤ d) {c c' : ℕ} (hc : c < 5) (hc' : c' < 5)
    {p p' : ℤ × ℤ} (h1 : Dom t d c p) (h2 : Dom t d c' p') (h : ¬ (c = c' ∧ p = p'))
    (ha : ¬ Tr t d c c' p p') (hb : ¬ Tr t d c' c p' p) : ch t d c p ≠ ch t d c' p' := by
  intro e
  rcases ch_eq ht hd hc hc' h1 h2 e with h' | h' | h'
  exacts [h h', ha h', hb h']

/-- A strip of `N ≥ n` steps with distinct points and the right end degrees is a literal path. -/
theorem literal_of_strip {W : ℕ → MV} {N n : ℕ} (hS : StripOK t d W N) (hn : n ≤ N + 1)
    (h4 : 4 ≤ n) (hev : Even n) (hinj : ∀ i j, i < n → j < n → W i = W j → i = j)
    (p : ℕ → MS t d) (hp : ∀ k, k ≤ N → (p k).1 = W k)
    (d0 : deg (GM t d) (p 0) = 5) (d1 : deg (GM t d) (p (n - 1)) = 5)
    (d2 : deg (GM t d) (p 1) = 6) (d3 : deg (GM t d) (p (n - 2)) = 6) :
    LiteralPath (GM t d) n p := by
  refine ⟨h4, hev, fun i j hi hj e => hinj i j hi hj ?_, fun i hi => ?_, fun i hi => ?_,
    d0, d1, d2, d3⟩
  · rw [← hp i (by omega), ← hp j (by omega), e]
  · show AdjM t d (p i).1 (p (i + 1)).1
    rw [hp i (by omega), hp (i + 1) (by omega)]; exact hS.2.1 i (by omega)
  · show AdjM t d (p i).1 (p (i + 2)).1
    rw [hp i (by omega), hp (i + 2) (by omega)]; exact hS.2.2.1 i (by omega)

end Claude5O2
