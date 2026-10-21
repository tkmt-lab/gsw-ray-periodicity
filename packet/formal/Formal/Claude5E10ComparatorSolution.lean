import Formal.ClaudeChallengeSpec
import Formal.Claude2AlignedSpec
import Formal.Claude5E10Spec
import Formal.Claude5E10RayB
import Formal.Claude5E10T1a

/-! Solution module for `lake comparator`: proves the challenge theorems
`ClaudeChallengeE10.classification` and `ClaudeChallengeE10.main` of
`Formal/Claude5E10ComparatorChallenge.lean` (E10 = Graver's E10(p,r,s)).  The definitions come
from `Formal.ClaudeChallengeSpec`, `Formal.Claude2AlignedSpec` and `Formal.Claude5E10Spec`, which
have the same definitions as the challenge; `PathExists` is restated here verbatim.

Proof (Claude worker, 2026-10-21): `e10Graph p r s` is isomorphic to a tube model (two hexagonal
caps, a tube of circumference `3m` and height `2p`, twist `p mod 3m`; `Claude5E10.e10_iff_gm`).
For `r ≥ 2` a line-state invariant excludes all starts except six residues of `p mod m`, where
explicit tube zigzags are literal paths (`Claude5E10.e10_classify`, `Claude5E10.classification_int`);
rays along which `r` is eventually at least 2 follow by divisibility (`Claude5E10.rays_A`).  Rays with
`r = 1` are handled by Theorem 1a (`ClaudeChallenge2.State.main_statement`) applied, on each residue
class of the ray, to a signature with affine charts and records whose graph is the model
(`Claude5E10.e10S`, `Claude5E10.valid_e10S`, `Claude5E10.rays_B`). -/

namespace ClaudeChallengeE10

open ClaudeChallenge Claude2Aligned

/-- A literal path exists in E10(p,r,s). -/
def PathExists (p r s : ℤ) : Prop := ∃ n q, LiteralPath (e10Graph p r s) n q

/-- **E10 classification**: for `p, s ≥ 1` and `r ≥ 2`, a literal path exists iff
`p ≡ d + 1` or `p ≡ d - 1 (mod 2r + s)` for some `d ∈ {0, r, r + s}`. -/
theorem classification (p r s : ℕ) (hp : 1 ≤ p) (hr : 2 ≤ r) (hs : 1 ≤ s) :
    PathExists p r s ↔
      ∃ d : ℤ, (d = 0 ∨ d = r ∨ d = r + s) ∧
        ((p : ℤ) ≡ d + 1 [ZMOD 2 * r + s] ∨ (p : ℤ) ≡ d - 1 [ZMOD 2 * r + s]) := by
  exact Claude5E10.classification_int (p := (p : ℤ)) (r := (r : ℤ)) (s := (s : ℤ))
    (by exact_mod_cast hp) (by exact_mod_cast hr) (by exact_mod_cast hs)

/-- **E10 on rays**: on every integer ray `(p₀ + a n, r₀ + b n, s₀ + c n)` with
`p₀, r₀, s₀ ≥ 1`, `a, b, c ≥ 0`, literal-path existence in E10 is eventually periodic. -/
theorem main (p₀ r₀ s₀ a b c : ℕ) (hp : 1 ≤ p₀) (hr : 1 ≤ r₀) (hs : 1 ≤ s₀) :
    ∃ n₀ P : ℕ, 0 < P ∧ ∀ n : ℕ, n₀ ≤ n →
      (PathExists (p₀ + a * n) (r₀ + b * n) (s₀ + c * n) ↔
        PathExists (p₀ + a * (n + P)) (r₀ + b * (n + P)) (s₀ + c * (n + P))) := by
  obtain ⟨n₀, P, hP, h⟩ := Claude5E10.e10_rays Claude5E10.t1a_gm p₀ r₀ s₀ a b c hp hr hs
  refine ⟨n₀, P, hP, fun n hn => ?_⟩
  have h' := h n hn
  simp only [Claude5E10.PR] at h'
  push_cast at h'
  exact h'

end ClaudeChallengeE10
