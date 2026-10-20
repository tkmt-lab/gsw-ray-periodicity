import Formal.Claude2K3NecGcd
import Formal.Claude2K3Sufficient

/-!
# K3 necessity (assuming two common neighbours per edge)

Written by a Claude worker (2026-10-19, K3 necessity session).

Along a literal path, the triangle `(p i, p (i+1), p (i+2))` is a lattice triangle `(a, b, e)` of
a cell `c` (`Claude2K3NecGcd.lean`).  Write `d = e - a` for the walk direction and `o` for the
odd-indexed member.  The invariant (`GoodR`) is

  `cross d o ≡ ε + k s (mod r)`,  `ε = ±1`,  `k ∈ {0, ks c d}`,

with the explicit shift table `ks` (values `-1, 0, 1`, `Claude2K3Apex.lean`).  It holds at the
start (the path starts at a corner, where `cross d a ≡ j s` with `j ∈ {0, ks c d}`), and it is
carried across every gluing the walk can use (the generated field of `ApexData`: for the two walk
directions that cross the glued edge, `k ↦ k'` with `cross (R d) τ + k s - k' s ≡ 0`).  At a
corner `cross d o ≡ j s`, so a corner at an odd index forces `ε + (k - j) s ≡ 0` with
`k - j ∈ {-1, 0, 1}`, i.e. `r ∣ 1`, `s ≡ 1` or `s ≡ -1 (mod r)`.

* `k3_necessary`     : `TwoCommonNeighbors (k3Graph r s)`, `r, s ≥ 2`, a literal path ⇒
                       `s ≡ ±1 (mod r)`;
* `k3_statement_of_two_common` : the full `K3Statement`, given `TwoCommonNeighbors` for all
                       `r, s ≥ 2` (sufficiency is `k3_sufficient`).

This is the verifier's argument (R004 `k3-necessity-proof.md`) in chart-local form: the cap
passages are replaced by the finite closure table `ks`.  The hypothesis `TwoCommonNeighbors` is
the external fact (S1504) that the verifier also uses; it is not proved here.
-/

namespace Claude2K3
open ClaudeChallenge Claude2Aligned
variable {r s : ℤ}

theorem ks_range (c : Fin 11) (d : ℤ × ℤ) : ks c d = 0 ∨ ks c d = 1 ∨ ks c d = -1 := by
  unfold ks; split_ifs <;> simp

theorem mod_cross (d z : ℤ × ℤ) (α β : ℤ) (h1 : r ∣ z.1 - α * s) (h2 : r ∣ z.2 - β * s) :
    r ∣ cross d z - (d.1 * β - d.2 * α) * s := by
  have : cross d z - (d.1 * β - d.2 * α) * s = d.1 * (z.2 - β * s) - d.2 * (z.1 - α * s) := by
    simp [cross]; ring
  rw [this]; exact dvd_sub (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1 _)

/-- At a corner, the cross product with any unit direction is `j s (mod r)`, `j ∈ {0, ks c d}`. -/
theorem corner_shift {c : Fin 11} {z : ℤ × ℤ} (h : IsCorner r s c z) {d : ℤ × ℤ}
    (hd : d ∈ unitVec) : ∃ j, (j = 0 ∨ j = ks c d) ∧ r ∣ cross d z - j * s := by
  obtain ⟨i, rfl⟩ := h
  by_cases hc : c.val < 8
  · refine ⟨0, Or.inl rfl, ?_⟩
    have := mod_cross (r := r) (s := s) d ((k3Sig r s).pt c i) 0 0
    simp only [mul_zero, sub_zero, zero_mul] at this ⊢
    rcases pt_tri (r := r) (s := s) c hc i with h | h | h <;> rw [h] at this ⊢ <;>
      exact this (by simp) (by simp)
  · have hks : ks c d = d.1 + d.2 := by
      simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hd
      unfold ks
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hc] <;> omega
    rcases pt_hex (r := r) (s := s) c hc i with h | h | h | h | h | h <;> rw [h]
    · refine ⟨0, Or.inl rfl, ?_⟩
      have := mod_cross (r := r) (s := s) d (0, 0) 0 0 (by simp) (by simp)
      simpa using this
    · refine ⟨0, Or.inl rfl, ?_⟩
      have := mod_cross (r := r) (s := s) d (r, 0) 0 0 (by simp) (by simp)
      simpa using this
    · refine ⟨0, Or.inl rfl, ?_⟩
      have := mod_cross (r := r) (s := s) d (r, r) 0 0 (by simp) (by simp)
      simpa using this
    · refine ⟨ks c d, Or.inr rfl, ?_⟩
      have := mod_cross (r := r) (s := s) d (r - s, r + s) (-1) 1
        (by simp) (by simp)
      rw [hks]; convert this using 2; ring
    · refine ⟨ks c d, Or.inr rfl, ?_⟩
      have := mod_cross (r := r) (s := s) d (-s, r + s) (-1) 1
        (by simp) (by simp)
      rw [hks]; convert this using 2; ring
    · refine ⟨ks c d, Or.inr rfl, ?_⟩
      have := mod_cross (r := r) (s := s) d (-s, s) (-1) 1
        (by simp) (by simp)
      rw [hks]; convert this using 2; ring

/-- The necessity invariant at index `i`. -/
def GoodR (r s : ℤ) (p : ℕ → (k3Sig r s).Vertex) (i : ℕ) : Prop :=
  ∃ (c : Fin 11) (a b e : ℤ × ℤ), CellIn r s c a ∧ CellIn r s c b ∧ CellIn r s c e ∧
    b - a ∈ unitVec ∧ e - b ∈ unitVec ∧ e - a ∈ unitVec ∧
    V r s c a = p i ∧ V r s c b = p (i + 1) ∧ V r s c e = p (i + 2) ∧
    ∃ k ε : ℤ, (k = 0 ∨ k = ks c (e - a)) ∧ (ε = 1 ∨ ε = -1) ∧
      r ∣ cross (e - a) (oddPt i a b) - ε - k * s

theorem goodR_advance {p : ℕ → (k3Sig r s).Vertex} {i : ℕ}
    {a b e : ℤ × ℤ} (hba : b - a ∈ unitVec) (heb : e - b ∈ unitVec)
    (hea : e - a ∈ unitVec) {k ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hinv : r ∣ cross (e - a) (oddPt i a b) - ε - k * s)
    {f : Fin 11} {m : ℕ} {τ : ℤ × ℤ} {k' : ℤ} (hk' : k' = 0 ∨ k' = ks f (rotN m (e - a)))
    (hdiv : r ∣ cross (rotN m (e - a)) τ + k * s - k' * s)
    (n0 : ℤ × ℤ) (hn0 : n0 - b = e - a)
    (k1 : CellIn r s f (gmap m τ b)) (k2 : CellIn r s f (gmap m τ e))
    (k3 : CellIn r s f (gmap m τ n0))
    (vb : V r s f (gmap m τ b) = p (i + 1)) (ve : V r s f (gmap m τ e) = p (i + 2))
    (vn : V r s f (gmap m τ n0) = p (i + 3)) : GoodR r s p (i + 1) := by
  have hne : n0 - e = b - a := by
    have : n0 - e = (n0 - b) - (e - b) := by abel
    rw [this, hn0]; abel
  refine ⟨f, gmap m τ b, gmap m τ e, gmap m τ n0, k1, k2, k3, ?_, ?_, ?_, vb, ve, vn,
    k', ε, ?_, hε, ?_⟩
  · rw [gmap_sub]; exact rotN_unit m heb
  · rw [gmap_sub, hne]; exact rotN_unit m hba
  · rw [gmap_sub, hn0]; exact rotN_unit m hea
  · rw [gmap_sub, hn0]; exact hk'
  · rw [gmap_sub, hn0]
    have : oddPt (i + 1) (gmap m τ b) (gmap m τ e) = gmap m τ (oddPt (i + 1) b e) := by
      unfold oddPt; split_ifs <;> rfl
    rw [this, cross_gmap, cross_odd]
    have := dvd_add hinv hdiv
    convert this using 1; ring

section path

variable {n : ℕ} {p : ℕ → (k3Sig r s).Vertex}

theorem goodR_succ (hT : R002.TwoCommonNeighbors (k3Graph r s)) (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hp : LiteralPath (k3Graph r s) n p) {i : ℕ} (hi : i + 3 < n)
    (hG : GoodR r s p i) : GoodR r s p (i + 1) := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  obtain ⟨-, -, hinj, hadj1, hadj2, -⟩ := hp
  obtain ⟨c, a, b, e, ha, hb, he, hba, heb, hea, va, vb, ve, k, ε, hk, hε, hinv⟩ := hG
  have hbe : (k3Graph r s).Adj (p (i + 1)) (p (i + 2)) := hadj1 (i + 1) (by omega)
  have hca : (k3Graph r s).Adj (p (i + 1)) (p i) ∧ (k3Graph r s).Adj (p (i + 2)) (p i) :=
    ⟨(hadj1 i (by omega)).symm, (hadj2 i (by omega)).symm⟩
  have hc3 : (k3Graph r s).Adj (p (i + 1)) (p (i + 3)) ∧
      (k3Graph r s).Adj (p (i + 2)) (p (i + 3)) :=
    ⟨hadj2 (i + 1) (by omega), hadj1 (i + 2) (by omega)⟩
  have h3a : p (i + 3) ≠ p i := fun h => by
    have := hinj (i + 3) i (by omega) (by omega) h; omega
  set u := e - b with hu_def
  have heu : e = b + u := by rw [hu_def]; abel
  rcases tri_cases hba heb hea with hA | hB
  · have hbm : CellIn r s c (e + -u) := by rw [hu_def]; simpa using hb
    obtain ⟨f, m, τ, hτ, k1, k2, k3, v1, v2, hne, -, hsh⟩ :=
      apex_left hr hs c e (-u) (unitVec_neg heb) he hbm
    have hd : e - a = rot (-u) - -u := by rw [hA, rot_neg', heu]; abel
    obtain ⟨k', hk', hdiv⟩ := hsh (e - a) (Or.inr hd) k hk
    have eb : e + -u = b := by rw [hu_def]; abel
    have ea : e + -u - rot (-u) = a := by rw [hA, rot_neg', eb]; abel
    rw [eb] at k2 v2
    rw [ea] at hne
    have hN : V r s f (gmap m τ (e + rot (-u))) = p (i + 3) := by
      refine (other_common hT hbe hca hc3 ?_ h3a (hne ha ∘ fun h => h.trans va.symm)).symm
      refine ⟨?_, ?_⟩
      · rw [← vb, v2]
        refine adj_of_unit hr0 hs0 k2 k3 ?_
        rw [gmap_sub, show e + rot (-u) - b = u + rot (-u) by rw [heu]; abel, rot_neg']
        exact rotN_unit m (by simpa [sub_eq_add_neg] using sub_rot_unit heb)
      · rw [← ve, v1]
        refine adj_of_unit hr0 hs0 k1 k3 ?_
        rw [gmap_sub, show e + rot (-u) - e = rot (-u) by abel]
        exact rotN_unit m (rot_unit (unitVec_neg heb))
    exact goodR_advance hba heb hea hε hinv hk' hdiv (e + rot (-u))
      (by rw [hA, rot_neg', heu]; abel) k2 k1 k3 (v2.symm.trans vb) (v1.symm.trans ve) hN
  · have hbm : CellIn r s c (b + u) := by rw [← heu]; exact he
    obtain ⟨f, m, τ, hτ, k1, k2, k3, v1, v2, hne, -, hsh⟩ := apex_left hr hs c b u heb hb hbm
    have hd : e - a = rot u := by rw [hB, heu]; abel
    obtain ⟨k', hk', hdiv⟩ := hsh (e - a) (Or.inl hd) k hk
    have ea : b + u - rot u = a := by rw [hB]
    rw [← heu] at k2 v2
    rw [ea] at hne
    have hN : V r s f (gmap m τ (b + rot u)) = p (i + 3) := by
      refine (other_common hT hbe hca hc3 ?_ h3a (hne ha ∘ fun h => h.trans va.symm)).symm
      refine ⟨?_, ?_⟩
      · rw [← vb, v1]
        refine adj_of_unit hr0 hs0 k1 k3 ?_
        rw [gmap_sub, show b + rot u - b = rot u by abel]
        exact rotN_unit m (rot_unit heb)
      · rw [← ve, v2]
        refine adj_of_unit hr0 hs0 k2 k3 ?_
        rw [gmap_sub, show b + rot u - e = rot u - u by rw [heu]; abel]
        exact rotN_unit m (rot_sub_unit heb)
    exact goodR_advance hba heb hea hε hinv hk' hdiv (b + rot u)
      (by rw [hB]; abel) k1 k2 k3 (v1.symm.trans vb) (v2.symm.trans ve) hN

/-- A start triangle at a degree-5 vertex satisfies the invariant. -/
theorem goodR_of_start (hr : 2 ≤ r) (hs : 2 ≤ s) {c : Fin 11} {a b e : ℤ × ℤ}
    (ha : CellIn r s c a) (hb : CellIn r s c b) (he : CellIn r s c e)
    (hba : b - a ∈ unitVec) (heb : e - b ∈ unitVec) (hea : e - a ∈ unitVec)
    (va : V r s c a = p 0) (vb : V r s c b = p 1) (ve : V r s c e = p 2)
    (hd0 : deg (k3Graph r s) (p 0) = 5) : GoodR r s p 0 := by
  obtain ⟨j, hj, hdj⟩ := corner_shift (corner_of_deg5 hr hs ha (by rw [va]; exact hd0)) hea
  refine ⟨c, a, b, e, ha, hb, he, hba, heb, hea, va, vb, ve, j, cross (e - a) (b - a), hj,
    unit_cross_aux _ hea _ hba (by rw [show e - a - (b - a) = e - b by abel]; exact heb), ?_⟩
  simp only [oddPt, Nat.zero_mod, if_true]
  rw [show cross (e - a) b = cross (e - a) a + cross (e - a) (b - a) by
    rw [← cross_add]; congr 1; abel]
  convert hdj using 1; ring

theorem goodR_zero (hT : R002.TwoCommonNeighbors (k3Graph r s)) (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hp : LiteralPath (k3Graph r s) n p) : GoodR r s p 0 := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  obtain ⟨h4, -, -, hadj1, hadj2, hd0, -⟩ := hp
  have h01 := hadj1 0 (by omega)
  obtain ⟨f, w0, u, hu, hw0, hw1, e0, e1⟩ := first_edge hr0 hs0 h01
  have hc2 : (k3Graph r s).Adj (p 0) (p 2) ∧ (k3Graph r s).Adj (p 1) (p 2) :=
    ⟨hadj2 0 (by omega), hadj1 1 (by omega)⟩
  have hm1 : CellIn r s f (w0 + u + -u) := by simpa using hw0
  obtain ⟨f2, m2, τ2, -, l1, l2, l3, x1, x2, hne2, hin2, -⟩ :=
    apex_left hr hs f (w0 + u) (-u) (unitVec_neg hu) hw1 hm1
  obtain ⟨f1, m1, τ1, -, j1, j2, j3, y1, y2, hne1, hin1, -⟩ := apex_left hr hs f w0 u hu hw0 hw1
  have ew : w0 + u + -u = w0 := by abel
  rw [ew] at l2 x2
  have er : w0 + u + -u - rot (-u) = w0 + rot u := by rw [rot_neg', ew]; abel
  rw [er] at hne2
  have er2 : w0 + u + rot (-u) = w0 + u - rot u := by rw [rot_neg']; abel
  rw [er2] at l3 hne2 hin2
  have hA1 : (k3Graph r s).Adj (p 0) (V r s f1 (gmap m1 τ1 (w0 + rot u))) ∧
      (k3Graph r s).Adj (p 1) (V r s f1 (gmap m1 τ1 (w0 + rot u))) := by
    refine ⟨?_, ?_⟩
    · rw [← e0, y1]; refine adj_of_unit hr0 hs0 j1 j3 ?_
      rw [gmap_sub, show w0 + rot u - w0 = rot u by abel]; exact rotN_unit m1 (rot_unit hu)
    · rw [← e1, y2]; refine adj_of_unit hr0 hs0 j2 j3 ?_
      rw [gmap_sub, show w0 + rot u - (w0 + u) = rot u - u by abel]
      exact rotN_unit m1 (rot_sub_unit hu)
  have hA2 : (k3Graph r s).Adj (p 0) (V r s f2 (gmap m2 τ2 (w0 + u - rot u))) ∧
      (k3Graph r s).Adj (p 1) (V r s f2 (gmap m2 τ2 (w0 + u - rot u))) := by
    refine ⟨?_, ?_⟩
    · rw [← e0, x2]; refine adj_of_unit hr0 hs0 l2 l3 ?_
      rw [gmap_sub, show w0 + u - rot u - w0 = u - rot u by abel]
      exact rotN_unit m2 (sub_rot_unit hu)
    · rw [← e1, x1]; refine adj_of_unit hr0 hs0 l1 l3 ?_
      rw [gmap_sub, show w0 + u - rot u - (w0 + u) = -rot u by abel]
      exact rotN_unit m2 (unitVec_neg (rot_unit hu))
  have hne : V r s f1 (gmap m1 τ1 (w0 + rot u)) ≠ V r s f2 (gmap m2 τ2 (w0 + u - rot u)) := by
    rcases apex_some_in hr hs f w0 u hu hw0 hw1 with hin | hin
    · rw [hin1 hin]; exact fun h => hne2 hin h.symm
    · rw [hin2 hin]; exact hne1 hin
  rcases two_common hT h01 hA1 hA2 hne hc2 with h2 | h2
  · refine goodR_of_start hr hs j1 j2 j3 ?_ ?_ ?_ (y1.symm.trans e0) (y2.symm.trans e1) h2.symm
      hd0
    · rw [gmap_sub, show w0 + u - w0 = u by abel]; exact rotN_unit m1 hu
    · rw [gmap_sub, show w0 + rot u - (w0 + u) = rot u - u by abel]
      exact rotN_unit m1 (rot_sub_unit hu)
    · rw [gmap_sub, show w0 + rot u - w0 = rot u by abel]; exact rotN_unit m1 (rot_unit hu)
  · refine goodR_of_start hr hs l2 l1 l3 ?_ ?_ ?_ (x2.symm.trans e0) (x1.symm.trans e1) h2.symm
      hd0
    · rw [gmap_sub, show w0 + u - w0 = u by abel]; exact rotN_unit m2 hu
    · rw [gmap_sub, show w0 + u - rot u - (w0 + u) = -rot u by abel]
      exact rotN_unit m2 (unitVec_neg (rot_unit hu))
    · rw [gmap_sub, show w0 + u - rot u - w0 = u - rot u by abel]
      exact rotN_unit m2 (sub_rot_unit hu)

theorem goodR_end (hr : 2 ≤ r) (hs : 2 ≤ s) (h1 : ¬ s ≡ 1 [ZMOD r]) (h2 : ¬ s ≡ -1 [ZMOD r])
    (hp : LiteralPath (k3Graph r s) n p) (hG : GoodR r s p (n - 3)) : False := by
  obtain ⟨h4, ⟨k0, hk0⟩, -, -, -, -, hdn, -⟩ := hp
  obtain ⟨c, a, b, e, ha, hb, he, -, -, hea, -, -, ve, k, ε, hk, hε, hinv⟩ := hG
  have hodd : (n - 3) % 2 = 1 := by omega
  simp only [oddPt, hodd, one_ne_zero, if_false] at hinv
  have hn : n - 3 + 2 = n - 1 := by omega
  rw [hn] at ve
  obtain ⟨j, hj, hdj⟩ :=
    corner_shift (corner_of_deg5 hr hs he (by rw [ve]; exact hdn)) hea
  rw [cross_sub_self] at hdj
  have hsub := dvd_sub hdj hinv
  have hkey : r ∣ ε + (k - j) * s := by convert hsub using 1; ring
  have hkr := ks_range c (e - a)
  have hr1 : ¬ r ∣ 1 := fun h => by have := Int.le_of_dvd one_pos h; omega
  have hrm1 : ¬ r ∣ -1 := fun h => hr1 (dvd_neg.1 h)
  have m1 : ¬ r ∣ 1 - s := fun h => h1 (Int.modEq_iff_dvd.2 h)
  have m2 : ¬ r ∣ -1 - s := fun h => h2 (Int.modEq_iff_dvd.2 h)
  have hdiff : k - j = 0 ∨ k - j = 1 ∨ k - j = -1 := by
    rcases hk with rfl | rfl <;> rcases hj with rfl | rfl <;> omega
  rcases hε with rfl | rfl <;> rcases hdiff with hd | hd | hd <;> rw [hd] at hkey
  · exact hr1 (by simpa using hkey)
  · exact m2 (by have := dvd_neg.2 hkey; convert this using 1; ring)
  · exact m1 (by convert hkey using 1; ring)
  · exact hrm1 (by simpa using hkey)
  · exact m1 (by have := dvd_neg.2 hkey; convert this using 1; ring)
  · exact m2 (by convert hkey using 1; ring)

/-- **K3 necessity** (assuming two common neighbours per edge): a literal path in K3(r,s),
`r, s ≥ 2`, forces `s ≡ ±1 (mod r)`. -/
theorem k3_necessary (hT : R002.TwoCommonNeighbors (k3Graph r s)) (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hp : LiteralPath (k3Graph r s) n p) : s ≡ 1 [ZMOD r] ∨ s ≡ -1 [ZMOD r] := by
  by_contra h
  rw [not_or] at h
  have hall : ∀ i, i + 2 < n → GoodR r s p i := by
    intro i
    induction i with
    | zero => intro _; exact goodR_zero hT hr hs hp
    | succ k ih => intro hk; exact goodR_succ hT hr hs hp (by omega) (ih (by omega))
  exact goodR_end hr hs h.1 h.2 hp (hall (n - 3) (by have := hp.1; omega))

end path

/-- **The K3 classification, given two common neighbours per edge.** -/
theorem k3_statement_of_two_common
    (hT : ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → R002.TwoCommonNeighbors (k3Graph r s)) :
    K3Statement := by
  intro r s hr hs
  refine ⟨?_, fun h => k3_sufficient r s hr hs h⟩
  rintro ⟨n, p, hp⟩
  exact k3_necessary (hT r s hr hs) (by exact_mod_cast hr) (by exact_mod_cast hs) hp

end Claude2K3

#print axioms Claude2K3.k3_necessary
#print axioms Claude2K3.k3_statement_of_two_common
