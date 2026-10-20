import Formal.Claude3StateLemmas

/-!
# Theorem 1a, G5 (⇒), part 1: maximal face passages of a literal path

Written by a Claude worker (2026-10-20, Theorem 1a, parts G4/G5).

Fix a literal path `p 0, …, p (n-1)`. A *row choice* at position `Q` is a state `c` (only its
chart, direction and height matter) and an index `i`; it *follows* the path for `M` steps if
`p (Q + m)` is the vertex of `rp c (i + m)` for `m ≤ M` (`Follows`).

* `Follows.extend` : a row that stays in the chart keeps following (forced continuation).
* `follows_back` : one step backwards (the two common neighbours of an edge).
* `exists_maxFollow` : under `Valid` and `TrianglesInCharts`, at every position with a triangle
  there is a row choice of **maximal reach** (paper: "split any literal path into maximal
  consecutive passages").
* `exit_of_max` : a maximal choice that does not reach the end of the path ends exactly at the
  last triangle `hi` of its row in the chart.
* `Decomp`, `exists_decomp` : the greedy decomposition into maximal-reach passages; consecutive
  passages share two vertices.
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo

variable {S : Sig} {t : ℕ}

/-- The row choice `(c, i)` follows the walk `p` from position `Q` for `M` steps. -/
def Follows (p : ℕ → Vertex S t) (Q : ℕ) (c : PState S) (i : ℤ) (M : ℕ) : Prop :=
  ∀ m : ℕ, m ≤ M → RV t c (i + m) (p (Q + m))

/-- A row choice of maximal reach at position `Q`. -/
def MaxF (p : ℕ → Vertex S t) (n Q : ℕ) (c : PState S) (i : ℤ) (M : ℕ) : Prop :=
  Follows p Q c i M ∧ 2 ≤ M ∧ Q + M < n ∧
    ∀ c' i' M', Follows p Q c' i' M' → Q + M' < n → M' ≤ M

theorem rv_of_eq {σ : PState S} {i : ℤ} {z : ℤ × ℤ} (hz : (S.chart σ.1.f).Mem t z)
    (e : rp σ i = z) : RV t σ i (pt S t σ.1.f z hz) := by
  subst e
  exact ⟨hz, rfl⟩

section Path

variable {n : ℕ} {p : ℕ → Vertex S t} (hp : LiteralPath (graph S t) n p)
include hp

theorem lp_adj1 {i : ℕ} (hi : i + 1 < n) : (graph S t).Adj (p i) (p (i + 1)) :=
  hp.2.2.2.1 i hi

theorem lp_adj2 {i : ℕ} (hi : i + 2 < n) : (graph S t).Adj (p i) (p (i + 2)) :=
  hp.2.2.2.2.1 i hi

theorem lp_inj {i j : ℕ} (hi : i < n) (hj : j < n) (e : p i = p j) : i = j :=
  hp.2.2.1 i j hi hj e

/-- A row that stays in the chart keeps following the path. -/
theorem Follows.extend (hV : Valid S t) {Q : ℕ} {c : PState S} {i : ℤ} {M : ℕ}
    (hf : Follows p Q c i M) (hM : 2 ≤ M) (hn : Q + M + 1 < n)
    (hmem : (S.chart c.1.f).Mem t (rp c (i + ((M + 1 : ℕ) : ℤ)))) :
    Follows p Q c i (M + 1) := by
  intro m hm
  rcases Nat.lt_or_ge m (M + 1) with h | h
  · exact hf m (by omega)
  obtain rfl : m = M + 1 := by omega
  have hv := rv_of_mem hmem
  have k0 := hf (M - 2) (by omega)
  have k1 := hf (M - 1) (by omega)
  have k2 := hf M le_rfl
  have hnext := RV.next hV k0 (k1.congr (by omega)) (k2.congr (by omega)) (hv.congr (by omega))
  have hfor := LiteralPath.isForced hp (Q + (M - 2)) (by omega)
  rw [show Q + (M - 2) + 1 = Q + (M - 1) by omega, show Q + (M - 2) + 2 = Q + M by omega,
    show Q + (M - 2) + 3 = Q + (M + 1) by omega] at hfor
  have a01 := lp_adj1 hp (i := Q + (M - 2)) (by omega)
  have a02 := lp_adj2 hp (i := Q + (M - 2)) (by omega)
  have a12 := lp_adj1 hp (i := Q + (M - 1)) (by omega)
  rw [show Q + (M - 2) + 1 = Q + (M - 1) by omega] at a01
  rw [show Q + (M - 2) + 2 = Q + M by omega] at a02
  rw [show Q + (M - 1) + 1 = Q + M by omega] at a12
  have := (exists_unique_next hV.1 a01 a02 a12).unique hnext hfor
  rw [← this]
  exact hv

/-- One step backwards along a row: the predecessor in the path is the predecessor in the
row, if that row point lies in the chart. -/
theorem follows_back (hV : Valid S t) {P : ℕ} (hP : P + 3 < n) {c : PState S} {a : ℤ}
    (h1 : RV t c a (p (P + 1))) (h2 : RV t c (a + 1) (p (P + 2)))
    (h3 : RV t c (a + 2) (p (P + 3))) (hmem : (S.chart c.1.f).Mem t (rp c (a - 1))) :
    RV t c (a - 1) (p P) := by
  have hv := rv_of_mem hmem
  have b1 : (graph S t).Adj (pt S t c.1.f (rp c (a - 1)) hmem) (p (P + 1)) :=
    hv.adj1 hV (h1.congr (by ring))
  have b2 : (graph S t).Adj (pt S t c.1.f (rp c (a - 1)) hmem) (p (P + 2)) :=
    hv.adj2 hV (h2.congr (by ring))
  have hne : p P ≠ p (P + 3) := fun e => by
    have := lp_inj hp (by omega) hP e
    omega
  have c0 : (graph S t).Adj (p (P + 1)) (p P) ∧ (graph S t).Adj (p (P + 2)) (p P) :=
    ⟨(lp_adj1 hp (by omega)).symm, (lp_adj2 hp (by omega)).symm⟩
  have c3 : (graph S t).Adj (p (P + 1)) (p (P + 3)) ∧ (graph S t).Adj (p (P + 2)) (p (P + 3)) :=
    ⟨lp_adj2 hp (i := P + 1) (by omega), lp_adj1 hp (i := P + 2) (by omega)⟩
  have hiff := common_iff_of_two hV.1 (lp_adj1 hp (i := P + 1) (by omega)) hne c0 c3
    (pt S t c.1.f (rp c (a - 1)) hmem)
  rcases (hiff.1 ⟨b1.symm, b2.symm⟩) with e | e
  · rw [← e]; exact hv
  · exfalso
    rw [e] at hv
    have := hv.inj hV h3
    omega

/-- Under `Valid` and `TrianglesInCharts`, every position with a triangle has a row choice of
maximal reach. -/
theorem exists_maxFollow (hTC : ClaudeChallenge2.TrianglesInCharts S t) {Q : ℕ}
    (hQ : Q + 2 < n) : ∃ c i M, MaxF p n Q c i M := by
  classical
  have P2 : ∃ c i, Follows p Q c i 2 ∧ Q + 2 < n := by
    obtain ⟨f, za, zb, zc, ha, hb, hc, ea, eb, ec, u1, u2, u3⟩ :=
      hTC _ _ _ (lp_adj1 hp (by omega)) (lp_adj2 hp hQ) (lp_adj1 hp (i := Q + 1) (by omega))
    obtain ⟨k, hk, h, i₀, e1, e2, e3⟩ := unitTri_cover u1 u2 u3
    let c : PState S := (⟨f, ⟨k, hk⟩, none, none, false⟩, h)
    refine ⟨c, i₀, ?_, hQ⟩
    intro m hm
    rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl
    · rw [Nat.add_zero, ← ea]; exact rv_of_eq ha (by simp [rp, c, e1])
    · rw [← eb]; exact rv_of_eq hb (by simp [rp, c, e2])
    · rw [← ec]; exact rv_of_eq hc (by simp [rp, c, e3])
  let P := fun M => ∃ c i, Follows p Q c i M ∧ Q + M < n
  have hM : P (Nat.findGreatest P n) := Nat.findGreatest_spec (m := 2) (by omega) P2
  have hle : ∀ M', P M' → M' ≤ Nat.findGreatest P n := fun M' h =>
    Nat.le_findGreatest (by obtain ⟨_, _, _, h⟩ := h; omega) h
  obtain ⟨c, i, hf, hb⟩ := hM
  exact ⟨c, i, _, hf, hle 2 P2, hb, fun c' i' M' h h' => hle M' ⟨c', i', h, h'⟩⟩

/-- A maximal choice: its passage is valid, and if it does not reach the end of the path it ends
exactly at the last triangle `hi` of its row. -/
theorem exit_of_max (hV : Valid S t) {Q : ℕ} {c : PState S} {i : ℤ} {M : ℕ}
    (hmax : MaxF p n Q c i M) :
    RowsIn t c ∧ loS t c ≤ i ∧ i + M - 2 ≤ hiS t c ∧ (Q + M + 1 < n → i + M - 2 = hiS t c) := by
  obtain ⟨hf, hM, hQ, hle⟩ := hmax
  have m0 := (hf 0 (by omega)).mem
  have m1 := (hf 1 (by omega)).mem
  have m2 := (hf 2 hM).mem
  have T0 := tri_of_mem (σ := c) (j := i) (by simpa using m0) (by simpa using m1)
    (by simpa [add_comm] using m2)
  have n0 := (hf (M - 2) (by omega)).mem
  have n1 := (hf (M - 1) (by omega)).mem
  have n2 := (hf M le_rfl).mem
  rw [show i + ((M - 2 : ℕ) : ℤ) = i + M - 2 by omega] at n0
  rw [show i + ((M - 1 : ℕ) : ℤ) = i + M - 2 + 1 by omega] at n1
  rw [show i + (M : ℤ) = i + M - 2 + 2 by omega] at n2
  have T1 := tri_of_mem n0 n1 n2
  refine ⟨T0.1, T0.2.1, T1.2.2, fun hn => ?_⟩
  by_contra hne
  have hmem := mem_of_tri (j := i + M - 1) T0.1 (by omega) (by omega) (m := 2) (by omega) le_rfl
  rw [show i + M - 1 + 2 = i + ((M + 1 : ℕ) : ℤ) by push_cast; ring] at hmem
  have := hle c i (M + 1) (hf.extend hp hV hM hn hmem) (by omega)
  omega

end Path

/-- The greedy decomposition of a walk of length `n` into maximal-reach passages. -/
structure Decomp (p : ℕ → Vertex S t) (n : ℕ) where
  r : ℕ
  pos : ℕ → ℕ
  c : ℕ → PState S
  i : ℕ → ℤ
  M : ℕ → ℕ
  max : ∀ j, j ≤ r → MaxF p n (pos j) (c j) (i j) (M j)
  last : pos r + M r = n - 1
  notlast : ∀ j, j < r → pos j + M j < n - 1
  next : ∀ j, j < r → pos (j + 1) = pos j + M j - 1
  pos0 : pos 0 = 0

/-- **The greedy decomposition exists.** -/
theorem exists_decomp {n : ℕ} {p : ℕ → Vertex S t} (hp : LiteralPath (graph S t) n p)
    (hTC : ClaudeChallenge2.TrianglesInCharts S t) : Nonempty (Decomp p n) := by
  classical
  have hn4 := hp.1
  have H : ∀ Q, ∃ x : PState S × ℤ × ℕ, Q + 2 < n → MaxF p n Q x.1 x.2.1 x.2.2 := by
    intro Q
    obtain ⟨c0, i0, M0, h0⟩ := exists_maxFollow hp hTC (Q := 0) (by omega)
    by_cases hQ : Q + 2 < n
    · obtain ⟨c, i, M, h⟩ := exists_maxFollow hp hTC hQ
      exact ⟨(c, i, M), fun _ => h⟩
    · exact ⟨(c0, i0, M0), fun h => absurd h hQ⟩
  choose B hB using H
  let Mf : ℕ → ℕ := fun Q => (B Q).2.2
  let posF : ℕ → ℕ := fun j => Nat.rec 0 (fun _ q => q + Mf q - 1) j
  have posF_succ : ∀ j, posF (j + 1) = posF j + Mf (posF j) - 1 := fun _ => rfl
  have good : ∀ j, (∀ l, l < j → posF l + Mf (posF l) < n - 1) → posF j + 2 < n ∧ j ≤ posF j := by
    intro j
    induction j with
    | zero => intro _; exact ⟨show (0 : ℕ) + 2 < n by omega, Nat.zero_le _⟩
    | succ j ih =>
      intro hl
      obtain ⟨h1, h2⟩ := ih (fun l hl' => hl l (by omega))
      have h3 : 2 ≤ Mf (posF j) := (hB _ h1).2.1
      have h4 := hl j (by omega)
      rw [posF_succ]
      exact ⟨by omega, by omega⟩
  have hex : ∃ j, n - 1 ≤ posF j + Mf (posF j) := by
    by_contra h
    push Not at h
    have := good n (fun l _ => h l)
    omega
  have hrmin : ∀ l, l < Nat.find hex → posF l + Mf (posF l) < n - 1 := fun l hl => by
    have := Nat.find_min hex hl
    omega
  have hgood : ∀ j, j ≤ Nat.find hex → posF j + 2 < n := fun j hj =>
    (good j (fun l hl => hrmin l (by omega))).1
  exact ⟨{ r := Nat.find hex
           pos := posF
           c := fun j => (B (posF j)).1
           i := fun j => (B (posF j)).2.1
           M := fun j => Mf (posF j)
           max := fun j hj => hB _ (hgood j hj)
           last := by
             have h1 := Nat.find_spec hex
             have h2 := (hB _ (hgood _ le_rfl)).2.2.1
             simp only [Mf] at h1 h2 ⊢
             omega
           notlast := hrmin
           next := fun j _ => posF_succ j
           pos0 := rfl }⟩

end ClaudeChallenge2.State
