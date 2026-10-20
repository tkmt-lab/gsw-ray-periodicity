import Formal.GCPrimitiveBoundary

/-! Certificate for the first boundary type, OA. All directions are checked as
integer coefficient data in the kernel; parameter arithmetic is proved once.
This proves coverage of the two open-face endpoints in this developed chart,
not coverage of all edges of a globally glued GC surface. -/
namespace R002.GCPrimitive

abbrev Coeff := ℤ × ℤ
def eval (k l : ℤ) (v : Coeff) : ℤ := v.1*k+v.2*l
def shiftA : Fin 6 → Coeff := ![(1,1),(0,1),(-1,0),(-1,-1),(0,-1),(1,0)]
def shiftB : Fin 6 → Coeff := ![(0,-1),(1,0),(1,1),(0,1),(-1,0),(-1,-1)]

/-- This predicate is purely finite integer data, not the claimed geometry. -/
def DirectionRowValid (i : Fin 6) : Prop :=
  (shiftA i).1=(direction i).1 ∧
  (shiftA i).2=(direction i).1+(direction i).2 ∧
  (shiftB i).1=(direction i).2 ∧ (shiftB i).2= -(direction i).1

instance (i : Fin 6) : Decidable (DirectionRowValid i) := inferInstanceAs
  (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem direction_table_checked : ∀ i, DirectionRowValid i := by decide +kernel

theorem slice_add (k l : ℤ) (p v : Lattice) :
    a k l (p+v)=a k l p+a k l v ∧ b k l (p+v)=b k l p+b k l v := by
  dsimp [a,b]
  constructor <;> ring

/-- Generic soundness: any coefficient row meeting the finite check is valid. -/
theorem direction_row_sound (k l : ℤ) (p : Lattice) (i : Fin 6)
    (h : DirectionRowValid i) :
    a k l (p+direction i)=a k l p+eval k l (shiftA i) ∧
    b k l (p+direction i)=b k l p+eval k l (shiftB i) := by
  rw [(slice_add k l p _).1,(slice_add k l p _).2]
  rcases h with ⟨ha,hb,hc,hd⟩
  dsimp [a,b,eval]
  rw [ha,hb,hc,hd]
  constructor <;> ring

theorem step_slices (k l : ℤ) (p : Lattice) (i : Fin 6) :
    a k l (p+direction i)=a k l p+eval k l (shiftA i) ∧
    b k l (p+direction i)=b k l p+eval k l (shiftB i) :=
  direction_row_sound k l p i (direction_table_checked i)

theorem opposite_involution (k l : ℤ) (p : Lattice) :
    opposite k l (opposite k l p)=p := by
  ext <;> dsimp [opposite] <;> ring

theorem opposite_slices (k l : ℤ) (p : Lattice) :
    a k l (opposite k l p)=norm k l-a k l p ∧
    b k l (opposite k l p)= -b k l p ∧
    c k l (opposite k l p)=a k l p+b k l p := by
  dsimp [a,b,c,norm,opposite]
  constructor
  · ring
  constructor <;> ring

theorem opposite_interior (k l : ℤ) (p : Lattice) :
    Interior k l (opposite k l p) ↔
    a k l p<norm k l ∧ b k l p<0 ∧ 0<a k l p+b k l p := by
  simp only [Interior,(opposite_slices k l p).1,(opposite_slices k l p).2.1,
    (opposite_slices k l p).2.2]
  omega

def exitDirection : Fin 3 → Fin 6 := ![0,4,5]
def width : Fin 3 → Coeff := ![(0,1),(1,0),(1,1)]

def ExitRowValid (r : Fin 3) : Prop :=
  (shiftB (exitDirection r)).1= -(width r).1 ∧
  (shiftB (exitDirection r)).2= -(width r).2
instance (r : Fin 3) : Decidable (ExitRowValid r) := inferInstanceAs
  (Decidable (_ ∧ _))

theorem exit_table_checked : ∀ r, ExitRowValid r := by decide +kernel

/-- A three-row half-open cut certificate, with both lateral bounds retained. -/
def Cut (k l : ℤ) (p : Lattice) (r : Fin 3) : Prop :=
  Interior k l p ∧
  b k l p<eval k l (width r) ∧
  a k l p+eval k l (shiftA (exitDirection r))<norm k l ∧
  0<a k l p+b k l p+eval k l (shiftA (exitDirection r))-eval k l (width r)

theorem exit_shift (k l : ℤ) (r : Fin 3) :
    eval k l (shiftB (exitDirection r))= -eval k l (width r) := by
  obtain ⟨h1,h2⟩ := exit_table_checked r
  dsimp [eval]
  rw [h1,h2]
  ring

theorem cut_iff (k l : ℤ) (p : Lattice) (r : Fin 3) :
    Cut k l p r ↔ SeamEdge k l p (p+direction (exitDirection r)) := by
  have hunit : Unit p (p+direction (exitDirection r)) := ⟨_,rfl⟩
  simp only [SeamEdge,hunit,and_true,opposite_interior,Cut,
    (step_slices k l p (exitDirection r)).1,
    (step_slices k l p (exitDirection r)).2,exit_shift]
  constructor <;> rintro ⟨hp,h1,h2,h3⟩ <;> exact ⟨hp,by omega,by omega,by omega⟩

theorem negative_shift_is_exit (k l : ℤ) (hk : 0<k) (hl : 0<l)
    (i : Fin 6) (hi : eval k l (shiftB i)<0) : ∃ r, exitDirection r=i := by
  fin_cases i
  · exact ⟨0,rfl⟩
  · norm_num [shiftB,eval] at hi; omega
  · norm_num [shiftB,eval] at hi; omega
  · norm_num [shiftB,eval] at hi; omega
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩

/-- Sound and complete for OA, with no positivity shortcut or omitted side test. -/
theorem seam_iff_certificate (k l : ℤ) (hk : 0<k) (hl : 0<l) (p q : Lattice) :
    SeamEdge k l p q ↔ ∃ r, q=p+direction (exitDirection r) ∧ Cut k l p r := by
  constructor
  · rintro ⟨hp,hq,i,rfl⟩
    have hb := ((opposite_interior k l _).mp hq).2.1
    rw [(step_slices k l p i).2] at hb
    have hneg : eval k l (shiftB i)<0 := by have := hp.2.1; omega
    obtain ⟨r,hr⟩ := negative_shift_is_exit k l hk hl i hneg
    refine ⟨r,by rw [hr],?_⟩
    apply (cut_iff k l p r).mpr
    rw [hr]
    exact ⟨hp,hq,i,rfl⟩
  · rintro ⟨r,rfl,h⟩
    exact (cut_iff k l p r).mp h

/-- Integer cut positions are bounded by width-1, rather than sampled. -/
theorem cut_height (k l : ℤ) (p : Lattice) (r : Fin 3) (h : Cut k l p r) :
    1≤b k l p ∧ b k l p≤eval k l (width r)-1 := by
  obtain ⟨hp,hb,_,_⟩ := h
  have := hp.2.1
  omega

end R002.GCPrimitive
