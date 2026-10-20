import Formal.Claude4C1Start

/-!
# C1 necessity: no literal path when `s ≥ 2`

Written by a Claude worker (2026-10-20, C1 bridge session).

A literal path starts at a corner (degree 5); a coordinate permutation moves it to `C01`
(`corner_norm`).  Its second vertex is one of `B0 … B4`, its third a common neighbour; of the ten
start triangles, five are the types I–V and five are their mirror images under the transposition
of the coordinates `2, 3` (which fixes `C01`).  For `r = 1` the starts through `B2`, `B3` are
excluded because these are corners (the second vertex must have degree 6).

* `no_path_g4` : `r ≥ 1`, `s ≥ 2` ⇒ no literal path in `G4 r s`;
* `c1_no_path` : the same for `c1Graph r s`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Claude4C1

open ClaudeChallenge Claude2Aligned

variable {r s : ℕ}

theorem corner_norm (hr : 1 ≤ r) (hs : 1 ≤ s) {x : Fin 4 → ℤ} (hx : InS r s x)
    (hc : CornerP r s x) : ∃ σ : Equiv.Perm (Fin 4), pm σ x = C01 r s := by
  obtain ⟨⟨a, ha⟩, b, c, hbc, hb, hc⟩ := hc
  have hab : a ≠ b := fun e => by subst e; omega
  have hac : a ≠ c := fun e => by subst e; omega
  obtain ⟨d, hda, hdb, hdc⟩ := fourth a b c hab hac hbc
  have hsum := sum4 x hab hac (Ne.symm hda) hbc (Ne.symm hdb) (Ne.symm hdc)
  have hx' := (inS_iff.1 hx).2.2.2.2.1
  have hd : x d = r := by omega
  let f : Fin 4 → Fin 4 := ![a, d, b, c]
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [f] at h ⊢ <;> simp_all [eq_comm]
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), ?_⟩
  funext i
  fin_cases i <;> simp [pm, f, C01, ha, hb, hc, hd]

theorem literal_pm (σ : Equiv.Perm (Fin 4)) {r s : ℤ} {n : ℕ} {p : ℕ → Surf r s}
    (hp : LiteralPath (G4 r s) n p) : LiteralPath (G4 r s) n (fun i => pmE σ (p i)) :=
  literal_of_equiv (pmE σ) (pmE_adj σ) hp

theorem not_adj_of (x y v : Fin 4 → ℤ) (hv : ∀ t, y t = x t + v t)
    (hn : ∀ i j : Fin 4, i ≠ j → ¬ ∀ t, v t = rt i j t) {r s : ℤ} : ¬ AdjR r s x y := by
  rintro ⟨i, j, hij, hy, -⟩
  refine hn i j hij fun t => ?_
  have h1 := hv t
  have h2 := congrFun hy t
  simp only [Pi.add_apply] at h2
  omega

macro "bvec" : tactic =>
  `(tactic| (intro t; fin_cases t <;> simp [B0, B1, B2, B3, B4, C01] <;> omega))

theorem na02 : ¬ AdjR (r : ℤ) s (B0 r s) (B2 r s) :=
  not_adj_of _ _ ![1, -2, 0, 1] (by bvec) (by decide)
theorem na03 : ¬ AdjR (r : ℤ) s (B0 r s) (B3 r s) :=
  not_adj_of _ _ ![1, -2, 1, 0] (by bvec) (by decide)
theorem na13 : ¬ AdjR (r : ℤ) s (B1 r s) (B3 r s) :=
  not_adj_of _ _ ![1, -1, 1, -1] (by bvec) (by decide)
theorem na24 : ¬ AdjR (r : ℤ) s (B2 r s) (B4 r s) :=
  not_adj_of _ _ ![-1, 1, 1, -1] (by bvec) (by decide)

theorem root_0011 : ∀ i j : Fin 4, i ≠ j → (∀ t, (![0, 0, 1, -1] : Fin 4 → ℤ) t = rt i j t) →
    i = 2 ∧ j = 3 := by
  unfold rt; decide

theorem na14 (hr : 1 ≤ r) (hs : 1 ≤ s) : ¬ AdjR (r : ℤ) s (B1 r s) (B4 r s) := by
  rintro ⟨i, j, hij, hy, k, hki, hkj, hk⟩
  have hv : ∀ t, (![0, 0, 1, -1] : Fin 4 → ℤ) t = rt i j t := by
    intro t
    have h2 := congrFun hy t
    simp only [Pi.add_apply] at h2
    fin_cases t <;> simp [B1, B4] at h2 ⊢ <;> omega
  obtain ⟨rfl, rfl⟩ := root_0011 i j hij hv
  fin_cases k <;> simp [B1] at hki hkj hk <;> omega

/-! ## The ten start triangles -/

theorem pt_I : (bI0 r s).pt 1 = B0 r s ∧ (bI0 r s).pt 2 = B1 r s :=
  ⟨by funext t; fin_cases t <;> simp [pt_apply, bI0, B0] <;> omega,
   by funext t; fin_cases t <;> simp [pt_apply, bI0, B1] <;> omega⟩
theorem pt_II : (bII0 r s).pt 1 = B1 r s ∧ (bII0 r s).pt 2 = B2 r s :=
  ⟨by funext t; fin_cases t <;> simp [pt_apply, bII0, B1] <;> omega,
   by funext t; fin_cases t <;> simp [pt_apply, bII0, B2] <;> omega⟩
theorem pt_III : (bIII0 r s).pt 1 = B1 r s ∧ (bIII0 r s).pt 2 = B0 r s :=
  ⟨by funext t; fin_cases t <;> simp [pt_apply, bIII0, B1] <;> omega,
   by funext t; fin_cases t <;> simp [pt_apply, bIII0, B0] <;> omega⟩
theorem pt_IV : (bIV0 r s).pt 1 = B2 r s ∧ (bIV0 r s).pt 2 = B3 r s :=
  ⟨by funext t; fin_cases t <;> simp [pt_apply, bIV0, B2] <;> omega,
   by funext t; fin_cases t <;> simp [pt_apply, bIV0, B3] <;> omega⟩
theorem pt_V : (bV0 r s).pt 1 = B2 r s ∧ (bV0 r s).pt 2 = B1 r s :=
  ⟨by funext t; fin_cases t <;> simp [pt_apply, bV0, B2] <;> omega,
   by funext t; fin_cases t <;> simp [pt_apply, bV0, B1] <;> omega⟩

theorem pt0_C01 : (bI0 r s).pt 0 = C01 r s ∧ (bII0 r s).pt 0 = C01 r s ∧
    (bIII0 r s).pt 0 = C01 r s ∧ (bIV0 r s).pt 0 = C01 r s ∧ (bV0 r s).pt 0 = C01 r s := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> funext t <;> fin_cases t <;>
    simp [pt_apply, bI0, bII0, bIII0, bIV0, bV0, C01]

/-- For `r = 1` the second vertex cannot be `B2` or `B3` (corners, degree 5). -/
theorem second_not_corner {r s : ℕ} (hs : 1 ≤ s) (hr : r = 1) {n : ℕ} {p : ℕ → Surf r s}
    (hp : LiteralPath (G4 r s) n p) (h1 : (p 1).1 = B2 r s ∨ (p 1).1 = B3 r s) : False := by
  subst hr
  obtain ⟨-, -, -, -, -, -, -, d1, -⟩ := hp
  rw [deg_g4 (by omega) (by omega), if_pos] at d1
  · omega
  · rcases h1 with h1 | h1 <;> rw [h1, cornerP_iff] <;> simp [B2, B3]

/-- The five canonical starts. -/
theorem no_canon (hr : 1 ≤ r) (hs : 2 ≤ s) {n : ℕ} {p : ℕ → Surf r s}
    (hp : LiteralPath (G4 r s) n p) (h0 : (p 0).1 = C01 r s)
    (h : ((p 1).1 = B0 r s ∧ (p 2).1 = B1 r s) ∨ ((p 1).1 = B1 r s ∧ (p 2).1 = B2 r s) ∨
      ((p 1).1 = B1 r s ∧ (p 2).1 = B0 r s) ∨ ((p 1).1 = B2 r s ∧ (p 2).1 = B3 r s) ∨
      ((p 1).1 = B2 r s ∧ (p 2).1 = B1 r s)) : False := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := pt0_C01 (r := r) (s := s)
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact no_typeI hr hs hp (h0.trans c1.symm) (h1.trans pt_I.1.symm) (h2.trans pt_I.2.symm)
  · exact no_typeII hr hs hp (h0.trans c2.symm) (h1.trans pt_II.1.symm) (h2.trans pt_II.2.symm)
  · exact no_typeIII hr hs hp (h0.trans c3.symm) (h1.trans pt_III.1.symm)
      (h2.trans pt_III.2.symm)
  · rcases Nat.lt_or_ge r 2 with hr2 | hr2
    · exact second_not_corner (by omega) (by omega) hp (Or.inl h1)
    · exact no_typeIV hr2 hs hp (h0.trans c4.symm) (h1.trans pt_IV.1.symm)
        (h2.trans pt_IV.2.symm)
  · rcases Nat.lt_or_ge r 2 with hr2 | hr2
    · exact second_not_corner (by omega) (by omega) hp (Or.inl h1)
    · exact no_typeV hr2 hs hp (h0.trans c5.symm) (h1.trans pt_V.1.symm) (h2.trans pt_V.2.symm)

end Claude4C1
