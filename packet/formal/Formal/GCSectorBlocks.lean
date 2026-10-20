import Formal.GCSectorNegative

/-! Exact R004 S4/S6 parent-face certificates for the other three sectors.
These finite patch facts do not yet assert coverage of their horizontal strips. -/
namespace R002.GCSector
open Icosahedron GCPrimitive

def receiptLabel : ParentVertex → ParentVertex := ![10,6,7,8,9,1,2,3,4,5,11,0]
def phi : ParentVertex → ParentVertex := ![1,10,4,9,5,2,3,8,11,6,0,7]
def psi : ParentVertex → ParentVertex := ![2,10,0,5,6,3,4,9,11,7,1,8]
def chi : ParentVertex → ParentVertex := ![10,4,9,5,1,3,8,11,6,2,0,7]

theorem receiptLabel_bijective : Function.Bijective receiptLabel := by decide +kernel
theorem phi_order : ∀ v, phi (phi (phi v))=v := by decide +kernel
theorem psi_order : ∀ v, psi (psi v)=v := by decide +kernel
theorem chi_order : ∀ v, chi (chi v)=v := by decide +kernel
theorem phi_rotation : ∀ v, receiptLabel (phi v)=rotateLabel (11,0) (receiptLabel v) := by decide +kernel
theorem psi_rotation : ∀ v, receiptLabel (psi v)=rotateLabel (12,0) (receiptLabel v) := by decide +kernel
theorem chi_rotation : ∀ v, receiptLabel (chi v)=rotateLabel (7,0) (receiptLabel v) := by decide +kernel

abbrev Patch := Corner → ParentVertex × Lattice
def s4 : Fin 4 → Patch := ![
  ![(5,(0,0)),(1,(1,-1)),(6,(1,0))],
  ![(1,(1,-1)),(2,(2,-1)),(6,(1,0))],
  ![(6,(1,0)),(2,(2,-1)),(7,(2,0))],
  ![(2,(2,-1)),(3,(3,-1)),(7,(2,0))]]
def s6plus : Fin 6 → Patch := ![
  s4 0,s4 1,s4 2,s4 3,
  ![(7,(2,0)),(3,(3,-1)),(8,(3,0))],
  ![(3,(3,-1)),(4,(4,-1)),(8,(3,0))]]
def s6minus : Fin 6 → Patch := ![
  ![(6,(0,0)),(2,(1,-1)),(7,(1,0))],
  ![(2,(1,-1)),(3,(2,-1)),(7,(1,0))],
  ![(2,(1,-1)),(10,(2,-2)),(3,(2,-1))],
  ![(3,(2,-1)),(10,(2,-2)),(4,(3,-2))],
  ![(3,(2,-1)),(4,(3,-2)),(8,(3,-1))],
  ![(4,(3,-2)),(9,(4,-2)),(8,(3,-1))]]
def s4Dart : Fin 4 → Dart := ![(5,0),(10,1),(6,0),(11,1)]
def s6plusDart : Fin 6 → Dart := ![(5,0),(10,1),(6,0),(11,1),(7,0),(12,1)]
def s6minusDart : Fin 6 → Dart := ![(6,0),(11,1),(16,2),(17,2),(12,1),(8,1)]

def LabeledFace (f : Patch) (d : Dart) : Prop :=
  ∀ e, receiptLabel (f e).1=faceVertex d.1 (e+d.2)
instance (f : Patch) (d : Dart) : Decidable (LabeledFace f d) := inferInstanceAs (Decidable (∀ _,_))
theorem s4_faces : ∀ i, LabeledFace (s4 i) (s4Dart i) := by decide +kernel
theorem s6plus_faces : ∀ i, LabeledFace (s6plus i) (s6plusDart i) := by decide +kernel
theorem s6minus_faces : ∀ i, LabeledFace (s6minus i) (s6minusDart i) := by decide +kernel

def movePatch (r : ParentVertex → ParentVertex) (delta : Lattice) (f : Patch) : Patch :=
  fun e => (r (f e).1,(f e).2+delta)

/-- Reverse shared edge with identical labels and coordinates; third corners reflect across it. -/
def Joined (f : Patch) (e : Corner) (g : Patch) (m : Corner) : Prop :=
  f e=g (m+1) ∧ f (e+1)=g m ∧ (f (e+2)).2+(g (m+2)).2=(f e).2+(f (e+1)).2
instance (f g : Patch) (e m : Corner) : Decidable (Joined f e g m) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem s4_seams : Joined (s4 0) 1 (s4 1) 2 ∧ Joined (s4 1) 1 (s4 2) 0 ∧
    Joined (s4 2) 1 (s4 3) 2 := by decide +kernel
theorem s6plus_seams : Joined (s6plus 0) 1 (s6plus 1) 2 ∧ Joined (s6plus 1) 1 (s6plus 2) 0 ∧
    Joined (s6plus 2) 1 (s6plus 3) 2 ∧ Joined (s6plus 3) 1 (s6plus 4) 0 ∧
    Joined (s6plus 4) 1 (s6plus 5) 2 := by decide +kernel
theorem s6minus_seams : Joined (s6minus 0) 1 (s6minus 1) 2 ∧ Joined (s6minus 1) 0 (s6minus 2) 2 ∧
    Joined (s6minus 2) 1 (s6minus 3) 0 ∧ Joined (s6minus 3) 2 (s6minus 4) 0 ∧
    Joined (s6minus 4) 1 (s6minus 5) 2 := by decide +kernel
theorem s4_wrap : Joined (s4 3) 0 (movePatch phi (2,-1) (s4 0)) 2 := by decide +kernel
theorem s6plus_wrap : Joined (s6plus 5) 0 (movePatch psi (3,-1) (s6plus 0)) 2 := by decide +kernel
theorem s6minus_wrap : Joined (s6minus 5) 1 (movePatch chi (3,-1) (s6minus 0)) 0 := by decide +kernel

/-- A label permutation and a translation preserve the entire seam certificate. -/
theorem joined_move (r : ParentVertex → ParentVertex) (delta : Lattice)
    (f g : Patch) (e m : Corner) (h : Joined f e g m) :
    Joined (movePatch r delta f) e (movePatch r delta g) m := by
  refine ⟨congrArg (fun v : ParentVertex × Lattice => (r v.1,v.2+delta)) h.1,
    congrArg (fun v : ParentVertex × Lattice => (r v.1,v.2+delta)) h.2.1,?_⟩
  have hx := congrArg Prod.fst h.2.2
  have hy := congrArg Prod.snd h.2.2
  ext <;> dsimp [movePatch] at * <;> omega

theorem moved_face (r : ParentVertex → ParentVertex) (R : Rotation)
    (hr : ∀ v, receiptLabel (r v)=rotateLabel R (receiptLabel v))
    (delta : Lattice) (f : Patch) (d : Dart) (h : LabeledFace f d) :
    LabeledFace (movePatch r delta f) (rotateDart R d) := by
  intro e
  change receiptLabel (r (f e).1)=_
  rw [hr,h]
  have hh := rotate_labels R d.1 (e+d.2)
  simpa only [rotateDart,add_assoc,add_comm,add_left_comm] using hh.symm

end R002.GCSector
