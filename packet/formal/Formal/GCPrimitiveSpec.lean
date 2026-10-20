import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin

/-! Local discrete specification, independent of arrays, paths and classification.
The basis has angle 60 degrees. No global gluing or continuous realization is
asserted in this file. The OA seam is developed by a half turn of the other face. -/
namespace R002.GCPrimitive

abbrev Lattice := ℤ × ℤ

def norm (k l : ℤ) : ℤ := k*k+k*l+l*l
def A (k l : ℤ) : Lattice := (k,l)
def B (k l : ℤ) : Lattice := (-l,k+l)
def a (k l : ℤ) (p : Lattice) : ℤ := (k+l)*p.1+l*p.2
def b (k l : ℤ) (p : Lattice) : ℤ := -l*p.1+k*p.2
def c (k l : ℤ) (p : Lattice) : ℤ := norm k l-a k l p-b k l p

def Closed (k l : ℤ) (p : Lattice) : Prop :=
  0 ≤ a k l p ∧ 0 ≤ b k l p ∧ 0 ≤ c k l p
def Interior (k l : ℤ) (p : Lattice) : Prop :=
  0 < a k l p ∧ 0 < b k l p ∧ 0 < c k l p

/-- The primitive condition only; positivity/order are separate theorem hypotheses. -/
def Primitive (k l : ℤ) : Prop := Int.gcd k l=1

def turn (k l : ℤ) (p : Lattice) : Lattice := (k-p.1-p.2,l+p.1)
def opposite (k l : ℤ) (p : Lattice) : Lattice := (k-p.1,l-p.2)

/-- The six primitive triangular-lattice steps in cyclic order. -/
def direction : Fin 6 → Lattice := ![(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)]
def Unit (p q : Lattice) : Prop := ∃ i : Fin 6, q=p+direction i

/-- The endpoints belong to the two *open* parent faces on either side of OA.
The second endpoint q is in the common developed chart, not its own face chart. -/
def SeamEdge (k l : ℤ) (p q : Lattice) : Prop :=
  Interior k l p ∧ Interior k l (opposite k l q) ∧ Unit p q

end R002.GCPrimitive
