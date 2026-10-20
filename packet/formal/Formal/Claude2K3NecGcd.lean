import Formal.Claude2K3Classify
import Formal.Claude2K3Apex
import Formal.ForcedContinuation
import Mathlib.Algebra.Ring.Divisibility.Basic

/-!
# K3 necessity when `gcd(r, s) ≥ 2` (assuming two common neighbours per edge)

Written by a Claude worker (2026-10-19, K3 necessity session).

Let `g ≥ 2` divide both `r` and `s`.  Every cell corner of K3(r,s) then has coordinates in
`gℤ²`, and every gluing is `z ↦ rotN m z + τ` with `τ ∈ gℤ²`.  Along a literal path, the
triangle `(p i, p (i+1), p (i+2))` is a lattice triangle `(a, b, e)` of some cell, the next vertex
is the reflection of `a` in the edge `be` (this is where the hypothesis
`R002.TwoCommonNeighbors` is used), and the cross product `cross (e - a) o` of the direction with
the odd-indexed member `o` is preserved modulo `g` (lattice rotations preserve `cross`, and `τ`
contributes a multiple of `g`).  It starts as `±1` (the path starts at a corner, in `gℤ²`), so the
odd-indexed last vertex `p (n-1)` can never be a corner, i.e. never has degree 5.

* `k3_no_path_of_dvd`  : `2 ≤ g`, `g ∣ r`, `g ∣ s` ⇒ no literal path;
* `k3_necessity_gcd`   : the same for `2 ≤ Nat.gcd r s` (natural-number form, as in `K3Statement`);
* `k3_necessity_dvd`   : the case `r ∣ s` (`u = 0` in `s = q r + u`).

The hypothesis `R002.TwoCommonNeighbors (k3Graph r s)` (every edge has exactly two common
neighbours) is the external fact also used by the verifier (R004 `k3-necessity-proof.md`, S1504);
it is not proved here.
-/

namespace Claude2K3
open ClaudeChallenge Claude2Aligned
variable {r s : ℤ}

/-- The odd-indexed members of the triangle `(p i, p (i+1), p (i+2)) = (a, b, e)` lie on the line
through this point. -/
def oddPt (i : ℕ) (a b : ℤ × ℤ) : ℤ × ℤ := if i % 2 = 0 then b else a

theorem tri_cases_aux : ∀ u ∈ unitVec, ∀ w ∈ unitVec, u + w ∈ unitVec →
    -w = rot u ∨ -w = u - rot u := by
  simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false]
  rintro u (rfl | rfl | rfl | rfl | rfl | rfl) w (rfl | rfl | rfl | rfl | rfl | rfl) h <;>
    simp [rot, Prod.ext_iff] at h ⊢

theorem tri_cases {a b e : ℤ × ℤ} (h1 : b - a ∈ unitVec) (h2 : e - b ∈ unitVec)
    (h3 : e - a ∈ unitVec) : a = b + rot (e - b) ∨ a = b + (e - b) - rot (e - b) := by
  have := tri_cases_aux (e - b) h2 (b - a) h1 (by rw [show e - b + (b - a) = e - a by abel]; exact h3)
  rcases this with h | h
  · left; rw [← h]; abel
  · right; rw [add_sub_assoc, ← h]; abel

theorem unit_cross_aux : ∀ u ∈ unitVec, ∀ w ∈ unitVec, u - w ∈ unitVec →
    cross u w = 1 ∨ cross u w = -1 := by
  simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false]
  rintro u (rfl | rfl | rfl | rfl | rfl | rfl) w (rfl | rfl | rfl | rfl | rfl | rfl) h <;>
    simp [cross, Prod.ext_iff] at h ⊢

theorem cross_add (d z w : ℤ × ℤ) : cross d (z + w) = cross d z + cross d w := by
  simp [cross]; ring

theorem cross_self (d : ℤ × ℤ) : cross d d = 0 := by simp [cross]; ring

theorem cross_sub_self (a e : ℤ × ℤ) : cross (e - a) e = cross (e - a) a := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring

theorem cross_gmap (m : ℕ) (τ d z : ℤ × ℤ) :
    cross (rotN m d) (gmap m τ z) = cross d z + cross (rotN m d) τ := by
  rw [gmap, cross_add, cross_rotN]

theorem gmap_sub (m : ℕ) (τ z w : ℤ × ℤ) : gmap m τ z - gmap m τ w = rotN m (z - w) := by
  simp only [gmap, rotN_sub_pt]; abel

theorem rot_neg' (u : ℤ × ℤ) : rot (-u) = -rot u := rotN_neg_pt 1 u

theorem dvd_cross {g : ℤ} (d : ℤ × ℤ) {z : ℤ × ℤ} (h1 : g ∣ z.1) (h2 : g ∣ z.2) :
    g ∣ cross d z := by
  unfold cross; exact dvd_sub (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1 _)

theorem span_dvd {g : ℤ} (hgr : g ∣ r) (hgs : g ∣ s) {τ : ℤ × ℤ} (hτ : InSpan r s τ) :
    g ∣ τ.1 ∧ g ∣ τ.2 := by
  obtain ⟨a, b, c, d, rfl⟩ := hτ
  exact ⟨dvd_add (dvd_mul_of_dvd_right hgr _) (dvd_mul_of_dvd_right hgs _),
    dvd_add (dvd_mul_of_dvd_right hgr _) (dvd_mul_of_dvd_right hgs _)⟩

theorem cross_transport {g : ℤ} (hgr : g ∣ r) (hgs : g ∣ s) {τ : ℤ × ℤ} (hτ : InSpan r s τ)
    (m : ℕ) (d o : ℤ × ℤ) : g ∣ cross (rotN m d) (gmap m τ o) ↔ g ∣ cross d o := by
  rw [cross_gmap]
  have := span_dvd hgr hgs hτ
  exact dvd_add_left (dvd_cross _ this.1 this.2)

theorem corner_dvd {g : ℤ} (hgr : g ∣ r) (hgs : g ∣ s) {c : Fin 11} {z : ℤ × ℤ}
    (h : IsCorner r s c z) : g ∣ z.1 ∧ g ∣ z.2 := by
  obtain ⟨i, rfl⟩ := h
  by_cases hc : c.val < 8
  · rcases pt_tri (r := r) (s := s) c hc i with h | h | h <;> rw [h] <;>
      exact ⟨by simp [hgr], by simp [hgr]⟩
  · rcases pt_hex (r := r) (s := s) c hc i with h | h | h | h | h | h <;> rw [h] <;>
      refine ⟨?_, ?_⟩ <;> dsimp only <;>
      first
        | exact dvd_zero g | exact hgr | exact hgs | exact (dvd_neg).2 hgs
        | exact dvd_sub hgr hgs | exact dvd_add hgr hgs

theorem corner_of_deg5 (hr : 2 ≤ r) (hs : 2 ≤ s) {c : Fin 11} {z : ℤ × ℤ} (hz : CellIn r s c z)
    (h : deg (k3Graph r s) (V r s c z) = 5) : IsCorner r s c z := by
  rcases deg_site hr hs c z hz with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact h1
  · omega

/-- Pinning a vertex by two common neighbours. -/
theorem other_common {W : Type} {G : SimpleGraph W} (hT : R002.TwoCommonNeighbors G)
    {u v a w x : W} (huv : G.Adj u v) (ha : G.Adj u a ∧ G.Adj v a) (hw : G.Adj u w ∧ G.Adj v w)
    (hx : G.Adj u x ∧ G.Adj v x) (hwa : w ≠ a) (hxa : x ≠ a) : w = x := by
  obtain ⟨y, z, hyz, h⟩ := hT u v huv
  rcases (h a).1 ha with e1 | e1 <;> rcases (h w).1 hw with e2 | e2 <;>
    rcases (h x).1 hx with e3 | e3 <;> subst e1 <;> simp_all

/-- Two distinct common neighbours are all the common neighbours. -/
theorem two_common {W : Type} {G : SimpleGraph W} (hT : R002.TwoCommonNeighbors G)
    {u v a b w : W} (huv : G.Adj u v) (ha : G.Adj u a ∧ G.Adj v a) (hb : G.Adj u b ∧ G.Adj v b)
    (hab : a ≠ b) (hw : G.Adj u w ∧ G.Adj v w) : w = a ∨ w = b := by
  by_cases h : w = a
  · exact Or.inl h
  · exact Or.inr (other_common hT huv ha hw hb h hab.symm)

/-- The state of a literal path at index `i`: a lattice triangle of a cell representing
`p i, p (i+1), p (i+2)`, with the odd-side cross product not divisible by `g`. -/
def Good (r s g : ℤ) (p : ℕ → (k3Sig r s).Vertex) (i : ℕ) : Prop :=
  ∃ (c : Fin 11) (a b e : ℤ × ℤ), CellIn r s c a ∧ CellIn r s c b ∧ CellIn r s c e ∧
    b - a ∈ unitVec ∧ e - b ∈ unitVec ∧ e - a ∈ unitVec ∧
    V r s c a = p i ∧ V r s c b = p (i + 1) ∧ V r s c e = p (i + 2) ∧
    ¬ g ∣ cross (e - a) (oddPt i a b)

theorem cross_odd (i : ℕ) (a b e : ℤ × ℤ) :
    cross (e - a) (oddPt (i + 1) b e) = cross (e - a) (oddPt i a b) := by
  unfold oddPt
  by_cases h : i % 2 = 0
  · rw [if_neg (by omega), if_pos h]
  · rw [if_pos (by omega), if_neg h]
    exact cross_sub_self a e

/-- Transport of a state across a gluing (or the identity). -/
theorem good_advance {g : ℤ} (hgr : g ∣ r) (hgs : g ∣ s) {p : ℕ → (k3Sig r s).Vertex} {i : ℕ}
    {a b e : ℤ × ℤ} (hba : b - a ∈ unitVec) (heb : e - b ∈ unitVec) (hea : e - a ∈ unitVec)
    (hinv : ¬ g ∣ cross (e - a) (oddPt i a b))
    {f : Fin 11} {m : ℕ} {τ : ℤ × ℤ} (hτ : InSpan r s τ) (n0 : ℤ × ℤ) (hn0 : n0 - b = e - a)
    (k1 : CellIn r s f (gmap m τ b)) (k2 : CellIn r s f (gmap m τ e))
    (k3 : CellIn r s f (gmap m τ n0))
    (vb : V r s f (gmap m τ b) = p (i + 1)) (ve : V r s f (gmap m τ e) = p (i + 2))
    (vn : V r s f (gmap m τ n0) = p (i + 3)) : Good r s g p (i + 1) := by
  have hne : n0 - e = b - a := by
    have : n0 - e = (n0 - b) - (e - b) := by abel
    rw [this, hn0]; abel
  refine ⟨f, gmap m τ b, gmap m τ e, gmap m τ n0, k1, k2, k3, ?_, ?_, ?_, vb, ve, vn, ?_⟩
  · rw [gmap_sub]; exact rotN_unit m heb
  · rw [gmap_sub, hne]; exact rotN_unit m hba
  · rw [gmap_sub, hn0]; exact rotN_unit m hea
  · rw [gmap_sub, hn0]
    have : oddPt (i + 1) (gmap m τ b) (gmap m τ e) = gmap m τ (oddPt (i + 1) b e) := by
      unfold oddPt; split_ifs <;> rfl
    rw [this, cross_transport hgr hgs hτ, cross_odd]
    exact hinv

theorem adj_of_unit (hr : 0 < r) (hs : 0 < s) {f : Fin 11} {z w : ℤ × ℤ} (hz : CellIn r s f z)
    (hw : CellIn r s f w) (hu : w - z ∈ unitVec) : (k3Graph r s).Adj (V r s f z) (V r s f w) :=
  V_adj_cell hr hs hz hw hu

theorem rot_sub_unit {u : ℤ × ℤ} (hu : u ∈ unitVec) : rot u - u ∈ unitVec := by
  simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hu ⊢
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rot]

theorem sub_rot_unit {u : ℤ × ℤ} (hu : u ∈ unitVec) : u - rot u ∈ unitVec := by
  simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hu ⊢
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rot]

section path

variable {g : ℤ} {n : ℕ} {p : ℕ → (k3Sig r s).Vertex}

theorem good_succ (hT : R002.TwoCommonNeighbors (k3Graph r s)) (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hgr : g ∣ r) (hgs : g ∣ s) (hp : LiteralPath (k3Graph r s) n p) {i : ℕ} (hi : i + 3 < n)
    (hG : Good r s g p i) : Good r s g p (i + 1) := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  obtain ⟨-, -, hinj, hadj1, hadj2, -⟩ := hp
  obtain ⟨c, a, b, e, ha, hb, he, hba, heb, hea, va, vb, ve, hinv⟩ := hG
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
  · -- `a` is the left apex of `b → e`; the next vertex is the left apex of `e → b`
    have hbm : CellIn r s c (e + -u) := by rw [hu_def]; simpa using hb
    obtain ⟨f, m, τ, hτ, k1, k2, k3, v1, v2, hne, -, -⟩ :=
      apex_left hr hs c e (-u) (unitVec_neg heb) he hbm
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
    exact good_advance hgr hgs hba heb hea hinv hτ (e + rot (-u))
      (by rw [hA, rot_neg', heu]; abel) k2 k1 k3 (v2.symm.trans vb) (v1.symm.trans ve) hN
  · -- `a` is the right apex of `b → e`; the next vertex is the left apex of `b → e`
    have hbm : CellIn r s c (b + u) := by rw [← heu]; exact he
    obtain ⟨f, m, τ, hτ, k1, k2, k3, v1, v2, hne, -, -⟩ := apex_left hr hs c b u heb hb hbm
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
    exact good_advance hgr hgs hba heb hea hinv hτ (b + rot u)
      (by rw [hB]; abel) k1 k2 k3 (v1.symm.trans vb) (v2.symm.trans ve) hN

/-- The first edge of the path: a unit step `w0 → w0 + u` of one cell. -/
theorem first_edge {x y : (k3Sig r s).Vertex} (hr : 0 < r) (hs : 0 < s)
    (h : (k3Graph r s).Adj x y) :
    ∃ (f : Fin 11) (w0 u : ℤ × ℤ), u ∈ unitVec ∧ CellIn r s f w0 ∧ CellIn r s f (w0 + u) ∧
      V r s f w0 = x ∧ V r s f (w0 + u) = y := by
  obtain ⟨-, s0, s1, hs0, hs1, hst⟩ := h
  rcases hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨s0.1.1, s0.1.2, s1.1.2 - s0.1.2, h2, (inCell_iff hr hs _ _).1 s0.2, ?_, ?_, ?_⟩
    · rw [add_sub_cancel, ← h1]; exact (inCell_iff hr hs _ _).1 s1.2
    · rw [← hs0, vtx_eq_V]
    · rw [add_sub_cancel, ← h1, ← hs1, vtx_eq_V]
  · refine ⟨s0.1.1, s0.1.2, -(s0.1.2 - s1.1.2), unitVec_neg h2, (inCell_iff hr hs _ _).1 s0.2,
      ?_, ?_, ?_⟩
    · rw [neg_sub, add_sub_cancel, h1]; exact (inCell_iff hr hs _ _).1 s1.2
    · rw [← hs0, vtx_eq_V]
    · rw [neg_sub, add_sub_cancel, h1, ← hs1, vtx_eq_V]

theorem good_zero (hT : R002.TwoCommonNeighbors (k3Graph r s)) (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hg : 2 ≤ g) (hgr : g ∣ r) (hgs : g ∣ s) (hp : LiteralPath (k3Graph r s) n p) :
    Good r s g p 0 := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  obtain ⟨h4, -, -, hadj1, hadj2, hd0, -⟩ := hp
  have h01 := hadj1 0 (by omega)
  obtain ⟨f, w0, u, hu, hw0, hw1, e0, e1⟩ := first_edge hr0 hs0 h01
  have hcor := corner_dvd hgr hgs (corner_of_deg5 hr hs hw0 (by rw [e0]; exact hd0))
  have hc2 : (k3Graph r s).Adj (p 0) (p 2) ∧ (k3Graph r s).Adj (p 1) (p 2) :=
    ⟨hadj2 0 (by omega), hadj1 1 (by omega)⟩
  -- the invariant at the start: `cross d (w0 + u) ≡ cross d u = ±1`
  have start : ∀ d : ℤ × ℤ, d ∈ unitVec → d - u ∈ unitVec → ¬ g ∣ cross d (w0 + u) := by
    intro d hd hdu hdv
    rw [cross_add] at hdv
    have h2 := (dvd_add_right (dvd_cross d hcor.1 hcor.2)).1 hdv
    rcases unit_cross_aux d hd u hu hdu with h | h <;> rw [h] at h2
    · exact absurd (Int.le_of_dvd one_pos h2) (by omega)
    · exact absurd (Int.le_of_dvd one_pos (dvd_neg.1 h2)) (by omega)
  -- the left apex (in a cell `f1`) and the right apex (in a cell `f2`) of `w0 → w0 + u`
  have hm1 : CellIn r s f (w0 + u + -u) := by simpa using hw0
  obtain ⟨f2, m2, τ2, hτ2, l1, l2, l3, x1, x2, hne2, hin2, -⟩ :=
    apex_left hr hs f (w0 + u) (-u) (unitVec_neg hu) hw1 hm1
  obtain ⟨f1, m1, τ1, hτ1, j1, j2, j3, y1, y2, hne1, hin1, -⟩ := apex_left hr hs f w0 u hu hw0 hw1
  have ew : w0 + u + -u = w0 := by abel
  rw [ew] at l2 x2
  have er : w0 + u + -u - rot (-u) = w0 + rot u := by rw [rot_neg', ew]; abel
  rw [er] at hne2
  have er2 : w0 + u + rot (-u) = w0 + u - rot u := by rw [rot_neg']; abel
  rw [er2] at l3 hne2 hin2
  -- both apexes are common neighbours of `p 0`, `p 1`
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
  · refine ⟨f1, gmap m1 τ1 w0, gmap m1 τ1 (w0 + u), gmap m1 τ1 (w0 + rot u), j1, j2, j3,
      ?_, ?_, ?_, y1.symm.trans e0, y2.symm.trans e1, h2.symm, ?_⟩
    · rw [gmap_sub, show w0 + u - w0 = u by abel]; exact rotN_unit m1 hu
    · rw [gmap_sub, show w0 + rot u - (w0 + u) = rot u - u by abel]
      exact rotN_unit m1 (rot_sub_unit hu)
    · rw [gmap_sub, show w0 + rot u - w0 = rot u by abel]; exact rotN_unit m1 (rot_unit hu)
    · rw [gmap_sub, show w0 + rot u - w0 = rot u by abel]
      simp only [oddPt, Nat.zero_mod, if_true]
      rw [cross_transport hgr hgs hτ1]
      exact start _ (rot_unit hu) (rot_sub_unit hu)
  · refine ⟨f2, gmap m2 τ2 w0, gmap m2 τ2 (w0 + u), gmap m2 τ2 (w0 + u - rot u), l2, l1, l3,
      ?_, ?_, ?_, x2.symm.trans e0, x1.symm.trans e1, h2.symm, ?_⟩
    · rw [gmap_sub, show w0 + u - w0 = u by abel]; exact rotN_unit m2 hu
    · rw [gmap_sub, show w0 + u - rot u - (w0 + u) = -rot u by abel]
      exact rotN_unit m2 (unitVec_neg (rot_unit hu))
    · rw [gmap_sub, show w0 + u - rot u - w0 = u - rot u by abel]
      exact rotN_unit m2 (sub_rot_unit hu)
    · rw [gmap_sub, show w0 + u - rot u - w0 = u - rot u by abel]
      simp only [oddPt, Nat.zero_mod, if_true]
      rw [cross_transport hgr hgs hτ2]
      exact start _ (sub_rot_unit hu) (by
        rw [show u - rot u - u = -rot u by abel]; exact unitVec_neg (rot_unit hu))

theorem good_end (hr : 2 ≤ r) (hs : 2 ≤ s) (hgr : g ∣ r) (hgs : g ∣ s)
    (hp : LiteralPath (k3Graph r s) n p) (hG : Good r s g p (n - 3)) : False := by
  obtain ⟨h4, ⟨k, hk⟩, -, -, -, -, hdn, -⟩ := hp
  obtain ⟨c, a, b, e, ha, hb, he, -, -, -, -, -, ve, hinv⟩ := hG
  have hodd : (n - 3) % 2 = 1 := by omega
  simp only [oddPt, hodd, one_ne_zero, if_false] at hinv
  have hn : n - 3 + 2 = n - 1 := by omega
  rw [hn] at ve
  have hcor := corner_dvd hgr hgs (corner_of_deg5 hr hs he (by rw [ve]; exact hdn))
  apply hinv
  have h1 := dvd_cross (e - a) hcor.1 hcor.2
  rwa [cross_sub_self] at h1

/-- **K3 necessity, common-divisor case.**  If an integer `g ≥ 2` divides both `r` and `s`, and
every edge of K3(r,s) has exactly two common neighbours, then K3(r,s) has no literal path. -/
theorem k3_no_path_of_dvd (hT : R002.TwoCommonNeighbors (k3Graph r s)) (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hg : 2 ≤ g) (hgr : g ∣ r) (hgs : g ∣ s) (n : ℕ) (p : ℕ → (k3Sig r s).Vertex) :
    ¬ LiteralPath (k3Graph r s) n p := by
  intro hp
  have hall : ∀ i, i + 2 < n → Good r s g p i := by
    intro i
    induction i with
    | zero => intro _; exact good_zero hT hr hs hg hgr hgs hp
    | succ k ih => intro hk; exact good_succ hT hr hs hgr hgs hp (by omega) (ih (by omega))
  exact good_end hr hs hgr hgs hp (hall (n - 3) (by have := hp.1; omega))

end path

/-- **K3 necessity when `gcd(r, s) ≥ 2`** (natural-number form, as in `K3Statement`), assuming
two common neighbours per edge. -/
theorem k3_necessity_gcd : ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → 2 ≤ Nat.gcd r s →
    R002.TwoCommonNeighbors (k3Graph r s) → ¬ ∃ n p, LiteralPath (k3Graph r s) n p := by
  intro r s hr hs hg hT ⟨n, p, hp⟩
  exact k3_no_path_of_dvd hT (by exact_mod_cast hr) (by exact_mod_cast hs)
    (g := (Nat.gcd r s : ℤ)) (by exact_mod_cast hg)
    (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left r s))
    (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right r s)) n p hp

/-- **K3 necessity, case `r ∣ s`** (`u = 0`), assuming two common neighbours per edge. -/
theorem k3_necessity_dvd : ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → r ∣ s →
    R002.TwoCommonNeighbors (k3Graph r s) → ¬ ∃ n p, LiteralPath (k3Graph r s) n p := by
  intro r s hr hs hrs hT ⟨n, p, hp⟩
  exact k3_no_path_of_dvd hT (by exact_mod_cast hr) (by exact_mod_cast hs)
    (g := (r : ℤ)) (by exact_mod_cast hr) dvd_rfl (Int.natCast_dvd_natCast.2 hrs) n p hp

end Claude2K3

#print axioms Claude2K3.k3_no_path_of_dvd
#print axioms Claude2K3.k3_necessity_gcd
#print axioms Claude2K3.k3_necessity_dvd
