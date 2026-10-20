import Formal.Claude3StateFwd

/-!
# Theorem 1a, G5 (⇒), part 2: a row of the decomposition meets the path only at its own passage

Written by a Claude worker (2026-10-20, Theorem 1a, parts G4/G5).

`Decomp.row_hit` : let `D` be the greedy maximal-reach decomposition of a literal path. If the
row of passage `l`, at an index `a` with `lo ≤ a ≤ e_l` (inside the triangles of the row in its
chart, up to the passage's exit), carries the vertex at the start position `pos j` of some
passage, then `j = l` and `a` is the actual entry index of passage `l` (for `l = 0`, provided
`a` is not before the root's start).

This is the key to "any extra eligible successor … contradicts …" (paper `lem:mso-path`): an
index `a` at or after the actual entry is excluded by simplicity of the path; an index before it
would let the path be followed backwards along the row of `l` (two common neighbours of an
edge) to an earlier passage start, whose reach would then exceed its own, contradicting
maximality.
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo

variable {S : Sig} {t : ℕ} {n : ℕ} {p : ℕ → Vertex S t}

theorem RV.pcongr {c : PState S} {a a' : ℤ} {P P' : ℕ} (h : RV t c a (p P)) (ha : a = a')
    (hP : P = P') : RV t c a' (p P') := by
  subst ha; subst hP; exact h

namespace Decomp

variable (D : Decomp p n)

theorem two {j : ℕ} (hj : j ≤ D.r) : 2 ≤ D.M j := (D.max j hj).2.1

theorem bound {j : ℕ} (hj : j ≤ D.r) : D.pos j + D.M j < n := (D.max j hj).2.2.1

theorem fol {j : ℕ} (hj : j ≤ D.r) : Follows p (D.pos j) (D.c j) (D.i j) (D.M j) :=
  (D.max j hj).1

theorem pos_succ_le {j l : ℕ} (hjl : j < l) (hl : l ≤ D.r) : D.pos j + D.M j - 1 ≤ D.pos l := by
  obtain ⟨d, rfl⟩ : ∃ d, l = j + 1 + d := ⟨l - j - 1, by omega⟩
  induction d with
  | zero => rw [D.next j (by omega)]
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := D.next (j + 1 + d) (by omega)
    have h3 := D.two (j := j + 1 + d) (by omega)
    rw [show j + 1 + (d + 1) = j + 1 + d + 1 by omega, h2]
    omega

theorem pos_lt {j l : ℕ} (hjl : j < l) (hl : l ≤ D.r) : D.pos j < D.pos l := by
  have := D.pos_succ_le hjl hl
  have := D.two (j := j) (by omega)
  omega

theorem lt_of_pos_lt {j l : ℕ} (hj : j ≤ D.r) (h : D.pos j < D.pos l) : j < l := by
  by_contra hc
  rcases Nat.lt_or_ge l j with h' | h'
  · have := D.pos_lt h' hj; omega
  · have : l = j := by omega
    subst this; omega

/-- Backwards along the row of passage `l`: for an index `a` with `lo ≤ a ≤ i_l`, the path
follows the row of `l` from index `i_l - m` at position `pos l - m`, for `m ≤ i_l - a` (and
`m ≤ pos l`; the bound is vacuous when `a > i_l`). -/
theorem back_follow (hp : LiteralPath (graph S t) n p) (hV : Valid S t) {l : ℕ} (hl : l ≤ D.r)
    {a : ℤ} (hlo : loS t (D.c l) ≤ a) :
    ∀ m : ℕ, m ≤ (D.i l - a).toNat → m ≤ D.pos l →
      Follows p (D.pos l - m) (D.c l) (D.i l - m) (m + D.M l) := by
  have hf := D.fol hl
  have hM := D.two hl
  have hb := D.bound hl
  obtain ⟨hrows, -, hhi, -⟩ := exit_of_max hp hV (D.max l hl)
  intro m
  induction m with
  | zero => intro _ _; simpa using hf
  | succ m ih =>
    intro h1 h2
    have F := ih (by omega) (by omega)
    have hmem := mem_of_tri (j := D.i l - m - 1) hrows (by omega) (by omega)
      (m := 0) le_rfl (by omega)
    rw [add_zero] at hmem
    have hback := follows_back hp hV (P := D.pos l - m - 1) (by omega) (c := D.c l)
      (a := D.i l - m) ((F 0 (by omega)).pcongr (by simp) (by omega))
      ((F 1 (by omega)).pcongr (by push_cast; ring) (by omega))
      ((F 2 (by omega)).pcongr (by push_cast; ring) (by omega)) (by simpa using hmem)
    intro m' hm'
    cases m' with
    | zero => exact hback.pcongr (by push_cast; ring) (by omega)
    | succ m' => exact (F m' (by omega)).pcongr (by push_cast; ring) (by omega)

/-- **The full row of a non-root passage lies on the path, after the previous passage's start.**
For `1 ≤ l`, with `d = i_l - lo_l`: `pos (l-1) < pos l - d`, and the path follows the row of
`l` from its first triangle `lo_l` at position `pos l - d`. -/
theorem prefix_follow (hp : LiteralPath (graph S t) n p) (hV : Valid S t) {l : ℕ}
    (hl1 : 1 ≤ l) (hl : l ≤ D.r) :
    D.pos (l - 1) + (D.i l - loS t (D.c l)).toNat < D.pos l ∧
      Follows p (D.pos l - (D.i l - loS t (D.c l)).toNat) (D.c l) (loS t (D.c l))
        ((D.i l - loS t (D.c l)).toNat + D.M l) := by
  obtain ⟨-, hlo, -, -⟩ := exit_of_max hp hV (D.max l hl)
  have back := D.back_follow hp hV hl (a := loS t (D.c l)) le_rfl
  have hnext := D.next (l - 1) (by omega)
  rw [show l - 1 + 1 = l by omega] at hnext
  have hM := D.two hl
  have hM' := D.two (j := l - 1) (by omega)
  have hfirst : D.pos (l - 1) + (D.i l - loS t (D.c l)).toNat < D.pos l := by
    by_contra hc
    have F := back (D.pos l - D.pos (l - 1)) (by omega) (by omega)
    have h1 := (D.max (l - 1) (by omega)).2.2.2 (D.c l) _ _
      (by rw [show D.pos l - (D.pos l - D.pos (l - 1)) = D.pos (l - 1) by omega] at F; exact F)
      (by have := D.bound hl; omega)
    omega
  refine ⟨hfirst, ?_⟩
  have F := back (D.i l - loS t (D.c l)).toNat le_rfl (by omega)
  rwa [show D.i l - ((D.i l - loS t (D.c l)).toNat : ℤ) = loS t (D.c l) by omega] at F

/-- **The row of passage `l` meets the passage starts only at its own entry.** -/
theorem row_hit (hp : LiteralPath (graph S t) n p) (hV : Valid S t) {j l : ℕ} (hj : j ≤ D.r)
    (hl : l ≤ D.r) {a : ℤ} (hlo : loS t (D.c l) ≤ a) (hae : a ≤ D.i l + D.M l - 2)
    (hcase : 1 ≤ l ∨ D.i l ≤ a) (hv : RV t (D.c l) a (p (D.pos j))) : j = l ∧ a = D.i l := by
  have hf := D.fol hl
  have hM := D.two hl
  have hb := D.bound hl
  have hbj := D.bound hj
  obtain ⟨hrows, -, hhi, -⟩ := exit_of_max hp hV (D.max l hl)
  by_cases hcmp : D.i l ≤ a
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, a = D.i l + d := ⟨(a - D.i l).toNat, by omega⟩
    have h1 := hf d (by omega)
    rw [← hd] at h1
    have hq := lp_inj hp (by omega) (by omega) (hv.unique h1)
    have hjl : j = l := by
      rcases lt_trichotomy j l with h | h | h
      · have := D.pos_lt h hl; omega
      · exact h
      · have := D.pos_succ_le h hj; omega
    subst hjl
    exact ⟨rfl, by omega⟩
  · have hl1 : 1 ≤ l := hcase.resolve_right hcmp
    have hpl : 1 ≤ D.pos l := by
      have := D.pos_lt (j := 0) (by omega) hl
      rw [D.pos0] at this
      omega
    have back := D.back_follow hp hV hl hlo
    let m₀ := min (D.i l - a).toNat (D.pos l)
    have F := back m₀ (min_le_left _ _) (min_le_right _ _)
    have hm₀ : 1 ≤ m₀ := le_min (by omega) hpl
    obtain ⟨j', hj', hpj', hj'l⟩ : ∃ j', j' ≤ D.r ∧ D.pos j' = D.pos l - m₀ ∧ j' < l := by
      by_cases hmin : (D.i l - a).toNat ≤ D.pos l
      · have hm : m₀ = (D.i l - a).toNat := min_eq_left hmin
        have h0 := F 0 (by omega)
        have e := hv.unique (h0.pcongr (by rw [hm]; push_cast; omega) rfl)
        have hq := lp_inj hp (by omega) (by omega) e
        refine ⟨j, hj, by omega, D.lt_of_pos_lt hj (by omega)⟩
      · have hm : m₀ = D.pos l := min_eq_right (by omega)
        exact ⟨0, Nat.zero_le _, by rw [D.pos0]; omega, hl1⟩
    have h1 := (D.max j' hj').2.2.2 (D.c l) (D.i l - m₀) (m₀ + D.M l) (by rw [hpj']; exact F)
      (by rw [hpj']; omega)
    have h2 := D.pos_succ_le hj'l hl
    have h3 := D.two hj'
    omega

end Decomp

end ClaudeChallenge2.State
