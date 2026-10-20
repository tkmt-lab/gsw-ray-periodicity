import Formal.GCPrimitiveSpec
import Formal.IcosahedronGluing
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! General discrete 20-face specification. Only local lattice definitions and
the fixed parent table are imported; no array, solver, path or classification.
The correspondence theorems require k>l>0 and primitive parent sides. -/
namespace R002.GCPrimitive
open Icosahedron (Corner)

def corner (k l : ℤ) : Corner → Lattice := ![(0,0),A k l,B k l]
def frame (k l : ℤ) (e : Corner) (p : Lattice) : Lattice :=
  if e=0 then p else if e=1 then turn k l (turn k l p) else turn k l p
def unframe (k l : ℤ) (e : Corner) (p : Lattice) : Lattice :=
  if e=0 then p else if e=1 then turn k l p else turn k l (turn k l p)
end R002.GCPrimitive

namespace R002.GCPrimitiveSurface
open Icosahedron GCPrimitive

abbrev Point (k l : ℤ) := {p : Lattice // Interior k l p}
abbrev Raw (k l : ℤ) := Face × (Corner ⊕ Point k l)
abbrev Canonical (k l : ℤ) := ParentVertex ⊕ (Face × Point k l)

def Glue (k l : ℤ) (u v : Raw k l) : Prop :=
  ∃ d : Dart, u=(d.1,.inl d.2) ∧ v=((mate d).1,.inl ((mate d).2+1))
abbrev Vertex (k l : ℤ) := Quotient (Relation.EqvGen.setoid (Glue k l))
def vertex {k l : ℤ} (u : Raw k l) : Vertex k l := Quotient.mk _ u
def canonical {k l : ℤ} (u : Raw k l) : Canonical k l :=
  match u.2 with
  | .inl e => .inl (faceVertex u.1 e)
  | .inr p => .inr (u.1,p)
def position {k l : ℤ} (u : Raw k l) : Lattice :=
  match u.2 with
  | .inl e => corner k l e
  | .inr p => p.val

/-- Both endpoints are in the open faces on opposite sides of the chosen seam. -/
def Across {k l : ℤ} (u v : Raw k l) : Prop :=
  ∃ (d : Dart) (p q : Point k l), u=(d.1,.inr p) ∧ v=((mate d).1,.inr q) ∧
    Unit (frame k l d.2 p.val) (opposite k l (frame k l (mate d).2 q.val))
def RawEdge {k l : ℤ} (u v : Raw k l) : Prop :=
  (u.1=v.1 ∧ Unit (position u) (position v)) ∨ Across u v ∨ Across v u
def Adj {k l : ℤ} (x y : Vertex k l) : Prop :=
  x≠y ∧ ∃ u v, vertex u=x ∧ vertex v=y ∧ RawEdge u v

end R002.GCPrimitiveSurface
