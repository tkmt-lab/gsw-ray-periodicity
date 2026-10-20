import Formal.Claude3GeoRot

/-!
# Theorem 1a, geometric foundation (6): literal paths as forced walks; passage cover

Written by a Claude worker (2026-10-20, Theorem 1a geometric session).

* `literalPath_iff_forced` : a literal path is exactly a forced walk
  whose first three vertices form a triangle, with the size, distinctness and degree conditions;
  under `TwoCommonNeighbors` it is determined by its first triangle and its length
  (`LiteralPath.eq_of_start`).
* `TrianglesInCharts S t` : every 3-clique of the surface graph is the image of a unit triangle
  of one chart. **This is not part of the spec's `Valid`** (the spec allows "holes": e.g. an
  icosahedron decomposed into 19 of its 20 faces satisfies `Valid`), but it follows from the
  paper's hypotheses (a decomposition of a fullerene dual all of whose 3-cycles are faces).
* `passage_cover` : under `Valid` and `TrianglesInCharts`, every triangle of a forced walk starts
  a maximal face passage: from that index on, the walk is a rotated row walk of one chart for as
  long as that row walk stays in the chart.
-/

namespace ClaudeChallenge2.Geo

open ClaudeChallenge2

variable {S : Sig} {t : ℕ}

section Literal

variable {V : Type} {G : SimpleGraph V}

/-- Literal paths are exactly the forced walks that start on a triangle and satisfy the size,
distinctness and degree conditions (no hypothesis on `G`). -/
theorem literalPath_iff_forced (n : ℕ) (p : ℕ → V) :
    LiteralPath G n p ↔
      4 ≤ n ∧ Even n ∧ (∀ i j, i < n → j < n → p i = p j → i = j) ∧
        G.Adj (p 0) (p 1) ∧ G.Adj (p 0) (p 2) ∧ G.Adj (p 1) (p 2) ∧ IsForced G p n ∧
          deg G (p 0) = 5 ∧ deg G (p (n - 1)) = 5 ∧ deg G (p 1) = 6 ∧ deg G (p (n - 2)) = 6 := by
  constructor
  · intro hp
    have hf := LiteralPath.isForced hp
    obtain ⟨h4, he, hinj, h1, h2, d0, d1, d2, d3⟩ := hp
    exact ⟨h4, he, hinj, h1 0 (by omega), h2 0 (by omega), h1 1 (by omega), hf, d0, d1, d2, d3⟩
  · rintro ⟨h4, he, hinj, a01, a02, a12, hf, d0, d1, d2, d3⟩
    have hadj := hf.adj a01 a02 a12
    refine ⟨h4, he, hinj, ?_, fun i hi => (hadj i hi).2.1, d0, d1, d2, d3⟩
    intro i hi
    by_cases h : i + 2 < n
    · exact (hadj i h).1
    · obtain ⟨-, -, h'⟩ := hadj (n - 3) (by omega)
      rwa [show n - 3 + 1 = i by omega, show n - 3 + 2 = i + 1 by omega] at h'

/-- Two literal paths of the same length with the same first three vertices coincide. -/
theorem LiteralPath.eq_of_start (hT : TwoCommonNeighbors G) {n : ℕ} {p p' : ℕ → V}
    (hp : LiteralPath G n p) (hp' : LiteralPath G n p') (e0 : p 0 = p' 0) (e1 : p 1 = p' 1)
    (e2 : p 2 = p' 2) : ∀ k, k < n → p k = p' k := by
  obtain ⟨-, -, -, a01, a02, a12, -⟩ := (literalPath_iff_forced n p).1 hp
  exact (LiteralPath.isForced hp).unique hT (LiteralPath.isForced hp') a01 a02 a12 e0 e1 e2

/-- A suffix of a forced walk is a forced walk. -/
theorem IsForced.shift {p : ℕ → V} {N : ℕ} (hp : IsForced G p N) (k : ℕ) :
    IsForced G (fun m => p (k + m)) (N - k) := by
  intro m hm
  have := hp (k + m) (by omega)
  simpa only [Nat.add_assoc] using this

end Literal

/-! ## Triangles in charts and the passage cover -/

/-- Every 3-clique of the surface graph is the image of a unit triangle of one chart (an extra
hypothesis, see the module docstring). -/
def TrianglesInCharts (S : Sig) (t : ℕ) : Prop :=
  ∀ a b c : Vertex S t, (graph S t).Adj a b → (graph S t).Adj a c → (graph S t).Adj b c →
    ∃ f : Fin S.C, ∃ za zb zc : ℤ × ℤ, ∃ (ha : (S.chart f).Mem t za)
      (hb : (S.chart f).Mem t zb) (hc : (S.chart f).Mem t zc),
      pt S t f za ha = a ∧ pt S t f zb hb = b ∧ pt S t f zc hc = c ∧
        zb - za ∈ unitVec ∧ zc - za ∈ unitVec ∧ zc - zb ∈ unitVec

/-- **Passage cover.** Under `Valid` and `TrianglesInCharts`, every triangle
`(p k, p (k+1), p (k+2))` of a forced walk starting on a triangle begins a face passage: for some
chart `f`, direction `k' < 6`, row `h` and index `i₀`, the first triangle of the rotated row walk
`rotN k' (q_{i₀+m})` lies in `f`, and `p (k + m)` is its `m`-th point for as long as it stays
in `f`. -/
theorem passage_cover (hV : Valid S t) (hTC : TrianglesInCharts S t) {p : ℕ → Vertex S t}
    {N : ℕ} (hp : IsForced (graph S t) p N) (a01 : (graph S t).Adj (p 0) (p 1))
    (a02 : (graph S t).Adj (p 0) (p 2)) (a12 : (graph S t).Adj (p 1) (p 2)) (k : ℕ)
    (hk : k + 2 < N) :
    ∃ f : Fin S.C, ∃ k', k' < 6 ∧ ∃ h i₀ : ℤ,
      (∀ m : ℕ, m ≤ 2 → (S.chart f).Mem t (rotN k' (rowPt h (i₀ + m)))) ∧
      ∀ m : ℕ, k + m < N →
        (∀ m' : ℕ, m' ≤ m → (S.chart f).Mem t (rotN k' (rowPt h (i₀ + m')))) →
          ∃ hz, p (k + m) = pt S t f (rotN k' (rowPt h (i₀ + m))) hz := by
  obtain ⟨b01, b02, b12⟩ := hp.adj a01 a02 a12 k hk
  obtain ⟨f, za, zb, zc, ha, hb, hc, ea, eb, ec, u1, u2, u3⟩ := hTC _ _ _ b01 b02 b12
  have hs := hp.shift k
  obtain ⟨k', hk', h, i₀, ea', eb', ec', H⟩ :=
    forced_walk_in_chart hV ha hb hc u1 u2 u3 (N := N - k) (by omega) hs
      (by simpa using ea.symm) eb.symm ec.symm
  refine ⟨f, k', hk', h, i₀, ?_, fun m hm hin => H m (by omega) hin⟩
  intro m hm
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl
  · simpa [← ea'] using ha
  · simpa [← eb'] using hb
  · simpa [← ec'] using hc

end ClaudeChallenge2.Geo
