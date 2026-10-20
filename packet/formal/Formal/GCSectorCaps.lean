import Formal.GCSectorNearDouble

/-! The terminal three faces and their general labeled return identities in coarse coordinates. -/
namespace R002.GCSector
open Icosahedron GCPrimitive

def gCaps : Fin 4 → Patch := ![
  ![(5,(0,0)),(6,(1,0)),(11,(0,1))],
  ![(6,(1,0)),(7,(1,1)),(11,(0,1))],
  ![(2,(2,0)),(7,(1,1)),(6,(1,0))],
  ![(1,(2,-1)),(2,(2,0)),(6,(1,0))]]
def hCaps : Fin 4 → Patch := ![
  ![(1,(0,0)),(2,(1,0)),(6,(0,1))],
  ![(1,(0,0)),(10,(1,-1)),(2,(1,0))],
  ![(2,(1,0)),(10,(1,-1)),(3,(2,-1))],
  ![(2,(1,0)),(3,(2,-1)),(7,(2,0))]]
def gCapsDart : Fin 4 → Dart := ![(0,1),(1,1),(6,1),(10,1)]
def hCapsDart : Fin 4 → Dart := ![(10,1),(15,2),(16,2),(11,1)]
theorem gCaps_faces : ∀ i, LabeledFace (gCaps i) (gCapsDart i) := by decide +kernel
theorem hCaps_faces : ∀ i, LabeledFace (hCaps i) (hCapsDart i) := by decide +kernel
theorem gCaps_seams : Joined (gCaps 0) 1 (gCaps 1) 2 ∧ Joined (gCaps 1) 0 (gCaps 2) 1 ∧
    Joined (gCaps 2) 2 (gCaps 3) 1 := by decide +kernel
theorem hCaps_seams : Joined (hCaps 0) 0 (hCaps 1) 2 ∧ Joined (hCaps 1) 1 (hCaps 2) 0 ∧
    Joined (hCaps 2) 2 (hCaps 3) 0 := by decide +kernel

theorem phi_period (n : ℕ) (v : ParentVertex) : (phi^[n+3]) v=(phi^[n]) v := by
  rw [Function.iterate_add_apply]
  exact congrArg (phi^[n]) (phi_order v)
theorem psi_period (n : ℕ) (v : ParentVertex) : (psi^[n+2]) v=(psi^[n]) v := by
  rw [Function.iterate_add_apply]
  exact congrArg (psi^[n]) (psi_order v)
theorem chi_period (n : ℕ) (v : ParentVertex) : (chi^[n+2]) v=(chi^[n]) v := by
  rw [Function.iterate_add_apply]
  exact congrArg (chi^[n]) (chi_order v)

def rotatePatch (delta : Lattice) (f : Patch) : Patch :=
  fun e => ((f e).1, (-(f e).2.2,(f e).2.1+(f e).2.2)+delta)
def invRotatePatch (delta : Lattice) (f : Patch) : Patch :=
  fun e => ((f e).1, ((f e).2.1+(f e).2.2,-(f e).2.1)+delta)

/-- q=n+3. All three labels and both coordinates agree, for arbitrary block count. -/
theorem comp_patch_return (n : ℕ) :
    rotatePatch ((n:ℤ)+7,-2*(n+2)) (movePatch (phi^[n]) (2*n,-(n:ℤ)) (s4 1))=
      movePatch (phi^[n+3]) (2*(n+3),-((n:ℤ)+3)) (gCaps 3) := by
  funext e
  fin_cases e <;> apply Prod.ext
  all_goals simp [rotatePatch,movePatch,s4,gCaps,phi_period] <;> constructor <;> ring

/-- a=n+1; the old F2 and F3 return to the last two cap faces. -/
theorem plus_patch_return (n : ℕ) :
    rotatePatch (2*(n:ℤ)+7,-3*(n+1)) (movePatch (psi^[n]) (3*n,-(n:ℤ)) (s6plus 1))=
      movePatch (psi^[n+2]) (3*(n+2),-((n:ℤ)+2)) (gCaps 3) := by
  funext e
  fin_cases e <;> apply Prod.ext
  all_goals simp [rotatePatch,movePatch,s6plus,s4,gCaps,psi_period] <;> constructor <;> ring

theorem plus_second_patch_return (n : ℕ) (e : Corner) :
    rotatePatch (2*(n:ℤ)+7,-3*(n+1)) (movePatch (psi^[n]) (3*n,-(n:ℤ)) (s6plus 2)) e=
      movePatch (psi^[n+2]) (3*(n+2),-((n:ℤ)+2)) (gCaps 2) (e+2) := by
  fin_cases e <;> apply Prod.ext
  all_goals simp [rotatePatch,movePatch,s6plus,s4,gCaps,psi_period] <;> constructor <;> ring

/-- a=n+2. This is the H-type return used on the lower side of k=2l. -/
theorem minus_patch_return (n : ℕ) :
    invRotatePatch ((n:ℤ)+7,2*n-1) (movePatch (chi^[n]) (3*n+1,-(n:ℤ)) (s6minus 1))=
      movePatch (chi^[n+2]) (3*(n+2)+1,-((n:ℤ)+3)) (hCaps 3) := by
  funext e
  fin_cases e <;> apply Prod.ext
  all_goals simp [invRotatePatch,movePatch,s6minus,hCaps,chi_period] <;> constructor <;> ring

end R002.GCSector
