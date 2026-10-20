import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Relation

/-! A fixed oriented combinatorial icosahedron. The table has no parameters.
Each dart is a face and the index of its outgoing edge. No geometric or
classification theorem is assumed. -/
namespace R002.Icosahedron

abbrev Face := Fin 20
abbrev Corner := Fin 3
abbrev ParentVertex := Fin 12
abbrev Dart := Face × Corner

def faceVertex : Face → Corner → ParentVertex := ![
  ![0,1,2],
  ![0,2,3],
  ![0,3,4],
  ![0,4,5],
  ![1,0,5],
  ![1,6,2],
  ![2,7,3],
  ![3,8,4],
  ![4,9,5],
  ![5,10,1],
  ![2,6,7],
  ![3,7,8],
  ![4,8,9],
  ![5,9,10],
  ![1,10,6],
  ![11,7,6],
  ![11,8,7],
  ![11,9,8],
  ![11,10,9],
  ![11,6,10]]

def mate : Dart → Dart := fun d => (![
  ![(4,0),(5,2),(1,0)],
  ![(0,2),(6,2),(2,0)],
  ![(1,2),(7,2),(3,0)],
  ![(2,2),(8,2),(4,1)],
  ![(0,0),(3,2),(9,2)],
  ![(14,2),(10,0),(0,1)],
  ![(10,2),(11,0),(1,1)],
  ![(11,2),(12,0),(2,1)],
  ![(12,2),(13,0),(3,1)],
  ![(13,2),(14,0),(4,2)],
  ![(5,1),(15,1),(6,0)],
  ![(6,1),(16,1),(7,0)],
  ![(7,1),(17,1),(8,0)],
  ![(8,1),(18,1),(9,0)],
  ![(9,1),(19,1),(5,0)],
  ![(16,2),(10,1),(19,0)],
  ![(17,2),(11,1),(15,0)],
  ![(18,2),(12,1),(16,0)],
  ![(19,2),(13,1),(17,0)],
  ![(15,2),(14,1),(18,0)]] : Face → Corner → Dart) d.1 d.2

def turn (d : Dart) : Dart := ((mate d).1, (mate d).2 + 1)

theorem faceVertex_injective : ∀ f, Function.Injective (faceVertex f) := by decide +kernel

theorem mate_involutive : ∀ d, mate (mate d) = d := by decide +kernel

theorem mate_other_face : ∀ d, (mate d).1 ≠ d.1 := by decide +kernel

theorem mate_reverses : ∀ d,
    faceVertex (mate d).1 (mate d).2 = faceVertex d.1 (d.2 + 1) ∧
    faceVertex (mate d).1 ((mate d).2 + 1) = faceVertex d.1 d.2 := by decide +kernel

theorem five_corners : ∀ v : ParentVertex,
    (Finset.univ.filter (fun d : Dart => faceVertex d.1 d.2 = v)).card = 5 := by decide +kernel

theorem turn_preserves_vertex : ∀ d,
    faceVertex (turn d).1 (turn d).2 = faceVertex d.1 d.2 := by decide +kernel

theorem turn_five : ∀ d, (turn^[5]) d = d := by decide +kernel

theorem turn_no_early_return : ∀ d, ∀ i : Fin 4, (turn^[i.val+1]) d ≠ d := by decide +kernel

theorem different_neighbors : ∀ f : Face,
    (mate (f,0)).1 ≠ (mate (f,2)).1 := by decide +kernel

theorem selected_seam : mate (0,0) = (4,0) := by decide +kernel

theorem parent_euler : (12 : ℤ) - 30 + 20 = 2 := by decide +kernel

theorem turn_covers_vertex : ∀ d e : Dart,
    faceVertex d.1 d.2=faceVertex e.1 e.2 → ∃ i : Fin 5, (turn^[i.val]) d=e := by
  decide +kernel

def FaceAdjacent (f g : Face) : Prop := ∃ e : Corner, (mate (f,e)).1=g

theorem face_descent : ∀ f : Face, f≠0 → ∃ e : Corner, (mate (f,e)).1.val < f.val := by
  decide +kernel

theorem faces_connected (f : Face) : Relation.ReflTransGen FaceAdjacent f 0 := by
  have aux : ∀ m : ℕ, ∀ f : Face, f.val=m → Relation.ReflTransGen FaceAdjacent f 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro f hf
      by_cases hz : f=0
      · subst f; exact .refl
      obtain ⟨e,he⟩ := face_descent f hz
      exact (ih (mate (f,e)).1.val (hf ▸ he) (mate (f,e)).1 rfl).head ⟨e,rfl⟩
  exact aux f.val f rfl

end R002.Icosahedron
