import Formal.GCPrimitiveLink
import Formal.GCChallengePaths
import Mathlib.Data.Int.Interval

namespace R002.GCPrimitiveSurface
open Icosahedron GCPrimitive
variable {k l : ℤ}

abbrev SliceBox (k l : ℤ) := {x : ℤ // x ∈ Finset.Icc 0 (norm k l)}

def encodePoint (p : Point k l) : SliceBox k l × SliceBox k l := by
  have hp := p.property
  dsimp [Interior,c] at hp
  exact (⟨a k l p.val,by simp only [Finset.mem_Icc]; omega⟩,
    ⟨b k l p.val,by simp only [Finset.mem_Icc]; omega⟩)

theorem encodePoint_injective (hk : 0<k) (hl : 0<l) : Function.Injective (@encodePoint k l) := by
  intro p q h
  apply Subtype.ext
  apply slices_injective k l hk hl.le
  exact congrArg (fun z : SliceBox k l × SliceBox k l => (z.1.val,z.2.val)) h

noncomputable def pointFintype (hk : 0<k) (hl : 0<l) : Fintype (Point k l) :=
  Fintype.ofInjective encodePoint (encodePoint_injective hk hl)

noncomputable def vertexFintype (hk : 0<k) (hl : 0<l) : Fintype (Vertex k l) := by
  letI := pointFintype hk hl
  exact Fintype.ofEquiv (Canonical k l) (vertexEquiv k l).symm

/-- The older finite literal-path decision now applies to the actual general
primitive chart graph, with its two-common-neighbor premise discharged. This is
a mathematical existence theorem, not correctness of the Python/C classifier. -/
theorem primitive_finite_decision (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (t : R002.OrderedTriangle (graph k l))
    (hc : ClaudeChallenge.deg (graph k l) t.a=5)
    (hb : ClaudeChallenge.deg (graph k l) t.b=6) :
    let hG := two_common_neighbors hkl hl hprim
    let cone := fun v => ClaudeChallenge.deg (graph k l) v=5
    ∃ r≤Nat.card (Vertex k l), R002.FirstRepeat (R002.forcedWalk (graph k l) hG t) r ∧
      ((∃ n p, R002.LiteralPathFrom (graph k l) cone t p n) ↔
        ∃ e<r, R002.LegalConeEndpoint cone (R002.forcedWalk (graph k l) hG t) e) := by
  letI := vertexFintype (show 0<k by omega) hl
  have hb' : ¬ClaudeChallenge.deg (graph k l) t.b=5 := by omega
  simpa only [Nat.card_eq_fintype_card] using
    R002.finite_literal_path_decision (graph k l) (two_common_neighbors hkl hl hprim)
      (fun v => ClaudeChallenge.deg (graph k l) v=5) t hc hb'

end R002.GCPrimitiveSurface
