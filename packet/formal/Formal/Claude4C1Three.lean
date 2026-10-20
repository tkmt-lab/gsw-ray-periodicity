import Formal.Claude4C1Deg

/-!
# The `ℤ⁴` model of C1: no edge has three common neighbours

Written by a Claude worker (2026-10-20, C1 bridge session).

Let `y = x + e_a - e_b`.  A common neighbour `z` of `x` and `y` is `x + e_a - e_c` or
`x + e_c - e_b` with `c ∉ {a, b}` (root arithmetic, `root_cases`), and then the fourth coordinate
`d` of `x` is `0` or `r + s` (the triangle lies in the face `d`, `tri_cand`).  Three distinct
common neighbours would use both values of `c`, so `x_c ∈ {0, r + s}` for some `c` for which both
`x_c - 1 ≥ 0` and `x_c + 1 ≤ r + s` hold: impossible (`no_three`).
-/

namespace Claude4C1

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

theorem root_cases : ∀ a b i j k l : Fin 4, a ≠ b → i ≠ j → k ≠ l →
    (∀ t, rt i j t = rt a b t + rt k l t) → (i = a ∧ k = b ∧ j = l) ∨ (j = b ∧ l = a ∧ i = k) := by
  unfold rt; decide

theorem four_cases : ∀ a b c d k : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    k ≠ a → k ≠ b → k = c ∨ k = d := by decide

theorem pigeon : ∀ a b c1 c2 c3 : Fin 4, (a ≠ b ∧ c1 ≠ a ∧ c1 ≠ b ∧ c2 ≠ a ∧ c2 ≠ b ∧ c3 ≠ a ∧
    c3 ≠ b) → c1 = c2 ∨ c1 = c3 ∨ c2 = c3 := by decide

theorem fourth : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c → ∃ d, d ≠ a ∧ d ≠ b ∧ d ≠ c := by decide

theorem sum4 (x : Fin 4 → ℤ) {a b c d : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : x a + x b + x c + x d = x 0 + x 1 + x 2 + x 3 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp_all <;> omega

theorem rt_eq_of {x y : Fin 4 → ℤ} {i j : Fin 4} (h : y = x + rt i j) (t : Fin 4) :
    y t = x t + rt i j t := by rw [h]; rfl

/-- The common neighbours of an edge. -/
theorem tri_cand (hr : 0 < r) (hs : 0 < s) {x y z : Fin 4 → ℤ} (hx : InS r s x) (hy : InS r s y)
    (hz : InS r s z) {a b : Fin 4} (hab : a ≠ b) (hyx : y = x + rt a b)
    (hxy : ∃ k, k ≠ a ∧ k ≠ b ∧ (x k = 0 ∨ x k = r + s)) (hxz : AdjR r s x z)
    (hyz : AdjR r s y z) :
    ∃ c, c ≠ a ∧ c ≠ b ∧ (z = x + rt a c ∨ z = x + rt c b) ∧
      ∀ d, d ≠ a → d ≠ b → d ≠ c → (x d = 0 ∨ x d = r + s) := by
  obtain ⟨i, j, hij, hzx, k1, h1i, h1j, h1⟩ := hxz
  obtain ⟨k, l, hkl, hzy, k2, h2k, h2l, h2⟩ := hyz
  obtain ⟨k3, h3a, h3b, h3⟩ := hxy
  have hroot : ∀ t, rt i j t = rt a b t + rt k l t := by
    intro t
    have e1 := rt_eq_of hzx t
    have e2 := rt_eq_of hzy t
    have e3 := rt_eq_of hyx t
    omega
  rw [inS_iff] at hx hy hz
  rcases root_cases a b i j k l hab hij hkl hroot with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
  · subst e1 e2 e3
    refine ⟨j, hij.symm, hkl.symm, Or.inl hzx, fun d hda hdb hdj => ?_⟩
    have hs4 := sum4 x hab hij (Ne.symm hda) hkl (Ne.symm hdb) (Ne.symm hdj)
    have ya := rt_eq_of hyx i; have yb := rt_eq_of hyx k; have yd := rt_eq_of hyx d
    have za := rt_eq_of hzx i; have zj := rt_eq_of hzx j
    rw [rt_left hab] at ya; rw [rt_right hab] at yb; rw [rt_ne hda hdb] at yd
    rw [rt_left hij] at za; rw [rt_right hij] at zj
    have hy4 : ∀ t, 0 ≤ y t ∧ y t ≤ r + s := fun t => by
      fin_cases t <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega
    have hz4 : ∀ t, 0 ≤ z t ∧ z t ≤ r + s := fun t => by
      fin_cases t <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega
    have hx4 : ∀ t, 0 ≤ x t ∧ x t ≤ r + s := fun t => by
      fin_cases t <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega
    have := hy4 i; have := hy4 k; have := hz4 j; have := hx4 i; have := hx4 k; have := hx4 j
    have := hx4 d
    rcases four_cases i j k d k1 hij hab hda.symm hkl.symm hdj.symm hdb.symm h1i h1j with
      e4 | e4 <;> rw [e4] at h1 <;>
    rcases four_cases k j i d k2 hkl hab.symm hdb.symm hij.symm hdj.symm hda.symm h2k h2l with
      e5 | e5 <;> rw [e5] at h2 <;>
    rcases four_cases i k j d k3 hab hij hda.symm hkl hdb.symm hdj.symm h3a h3b with
      e6 | e6 <;> rw [e6] at h3 <;>
    omega
  · subst e1 e2 e3
    refine ⟨i, hkl, hij, Or.inr hzx, fun d hda hdb hdi => ?_⟩
    have hs4 := sum4 x hab (Ne.symm hkl) (Ne.symm hda) (Ne.symm hij) (Ne.symm hdb) (Ne.symm hdi)
    have ya := rt_eq_of hyx l; have yb := rt_eq_of hyx j; have yd := rt_eq_of hyx d
    have zi := rt_eq_of hzx i; have zb := rt_eq_of hzx j
    rw [rt_left hab] at ya; rw [rt_right hab] at yb; rw [rt_ne hda hdb] at yd
    rw [rt_left hij] at zi; rw [rt_right hij] at zb
    have hy4 : ∀ t, 0 ≤ y t ∧ y t ≤ r + s := fun t => by
      fin_cases t <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega
    have hz4 : ∀ t, 0 ≤ z t ∧ z t ≤ r + s := fun t => by
      fin_cases t <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega
    have hx4 : ∀ t, 0 ≤ x t ∧ x t ≤ r + s := fun t => by
      fin_cases t <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega
    have := hy4 l; have := hy4 j; have := hz4 i; have := hx4 i; have := hx4 l; have := hx4 j
    have := hx4 d
    rcases four_cases i j l d k1 hij hkl hdi.symm hab.symm hdb.symm hda.symm h1i h1j with
      e4 | e4 <;> rw [e4] at h1 <;>
    rcases four_cases i l j d k2 hkl hij hdi.symm hab hda.symm hdb.symm h2k h2l with
      e5 | e5 <;> rw [e5] at h2 <;>
    rcases four_cases l j i d k3 hab hkl.symm hda.symm hij.symm hdb.symm hdi.symm h3a h3b with
      e6 | e6 <;> rw [e6] at h3 <;>
    omega

theorem pair_contra {x zA zB zC : Fin 4 → ℤ} (hA : InS r s zA) (hB : InS r s zB)
    {a b c cC : Fin 4} (hca : c ≠ a) (hcb : c ≠ b)
    (sA : zA = x + rt a c ∨ zA = x + rt c b) (sB : zB = x + rt a c ∨ zB = x + rt c b)
    (sC : zC = x + rt a cC ∨ zC = x + rt cC b)
    (PC : ∀ d, d ≠ a → d ≠ b → d ≠ cC → (x d = 0 ∨ x d = r + s))
    (hAB : zA ≠ zB) (hAC : zA ≠ zC) (hBC : zB ≠ zC) : False := by
  by_cases hcc : cC = c
  · subst hcc
    rcases sA with rfl | rfl <;> rcases sB with rfl | rfl <;> rcases sC with rfl | rfl <;>
      simp_all
  · have hxc := PC c hca hcb (Ne.symm hcc)
    rcases sA with rfl | rfl <;> rcases sB with rfl | rfl
    · exact hAB rfl
    · have h1 := (hA.1 c).1; have h2 := (hB.1 c).2
      rw [add_rt_right x hca.symm] at h1; rw [add_rt_left x hcb] at h2; omega
    · have h1 := (hB.1 c).1; have h2 := (hA.1 c).2
      rw [add_rt_right x hca.symm] at h1; rw [add_rt_left x hcb] at h2; omega
    · exact hAB rfl

/-- **No three common neighbours.** -/
theorem no_three (hr : 0 < r) (hs : 0 < s) {x y z1 z2 z3 : Fin 4 → ℤ} (hx : InS r s x)
    (hy : InS r s y) (hz1 : InS r s z1) (hz2 : InS r s z2) (hz3 : InS r s z3)
    (hxy : AdjR r s x y) (a1 : AdjR r s x z1) (b1 : AdjR r s y z1) (a2 : AdjR r s x z2)
    (b2 : AdjR r s y z2) (a3 : AdjR r s x z3) (b3 : AdjR r s y z3)
    (h12 : z1 ≠ z2) (h13 : z1 ≠ z3) (h23 : z2 ≠ z3) : False := by
  obtain ⟨a, b, hab, hyx, hface⟩ := hxy
  obtain ⟨c1, c1a, c1b, s1, P1⟩ := tri_cand hr hs hx hy hz1 hab hyx hface a1 b1
  obtain ⟨c2, c2a, c2b, s2, P2⟩ := tri_cand hr hs hx hy hz2 hab hyx hface a2 b2
  obtain ⟨c3, c3a, c3b, s3, P3⟩ := tri_cand hr hs hx hy hz3 hab hyx hface a3 b3
  rcases pigeon a b c1 c2 c3 ⟨hab, c1a, c1b, c2a, c2b, c3a, c3b⟩ with e | e | e
  · subst e; exact pair_contra hz1 hz2 c1a c1b s1 s2 s3 P3 h12 h13 h23
  · subst e; exact pair_contra hz1 hz3 c1a c1b s1 s3 s2 P2 h13 h12 (Ne.symm h23)
  · subst e; exact pair_contra hz2 hz3 c2a c2b s2 s3 s1 P1 h23 (Ne.symm h12) (Ne.symm h13)

/-- The forced continuation: a common neighbour of an edge other than one known apex is the
other known apex. -/
theorem next_unique (hr : 0 < r) (hs : 0 < s) {u v w t q : Surf r s} (hvw : (G4 r s).Adj v w)
    (hu : (G4 r s).Adj v u ∧ (G4 r s).Adj w u) (ht : (G4 r s).Adj v t ∧ (G4 r s).Adj w t)
    (hq : (G4 r s).Adj v q ∧ (G4 r s).Adj w q) (hut : u ≠ t) (hqu : q ≠ u) : q = t := by
  by_contra hqt
  exact no_three hr hs v.2 w.2 u.2 t.2 q.2 hvw hu.1 hu.2 ht.1 ht.2 hq.1 hq.2
    (fun e => hut (Subtype.ext e)) (fun e => hqu (Subtype.ext e).symm)
    (fun e => hqt (Subtype.ext e).symm)

end Claude4C1
