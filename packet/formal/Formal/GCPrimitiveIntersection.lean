import Formal.GCPrimitiveCuts

/-! Exact integer homogeneous coordinates of the seam intersection.
The rational crossing point is intersectionNumerator / width, with segment
parameter b(p) / width. The strict inequalities exclude the parent corners. -/
namespace R002.GCPrimitive

def intersectionNumerator (k l : ℤ) (p : Lattice) (r : Fin 3) : Lattice :=
  (eval k l (width r)*p.1+b k l p*(direction (exitDirection r)).1,
   eval k l (width r)*p.2+b k l p*(direction (exitDirection r)).2)

theorem intersection_slices (k l : ℤ) (p : Lattice) (r : Fin 3) :
    a k l (intersectionNumerator k l p r)=
      eval k l (width r)*a k l p+b k l p*eval k l (shiftA (exitDirection r)) ∧
    b k l (intersectionNumerator k l p r)=0 := by
  have ha : a k l (direction (exitDirection r))=eval k l (shiftA (exitDirection r)) := by
    simpa [a] using (step_slices k l (0,0) (exitDirection r)).1
  have hb : b k l (direction (exitDirection r))= -eval k l (width r) := by
    have h := (step_slices k l (0,0) (exitDirection r)).2
    simpa [b,exit_shift] using h
  constructor
  · calc
      _ = eval k l (width r)*a k l p+b k l p*a k l (direction (exitDirection r)) := by
        dsimp [intersectionNumerator,a,b]; ring
      _ = _ := by rw [ha]
  · calc
      _ = eval k l (width r)*b k l p+b k l p*b k l (direction (exitDirection r)) := by
        dsimp [intersectionNumerator,b]; ring
      _ = 0 := by rw [hb]; ring

/-- Every accepted certificate crosses the relative interior of OA,
at a strict interior parameter of its unit segment. -/
theorem cut_intersection (k l : ℤ) (p : Lattice) (r : Fin 3) (h : Cut k l p r) :
    0<b k l p ∧ b k l p<eval k l (width r) ∧
    b k l (intersectionNumerator k l p r)=0 ∧
    0<a k l (intersectionNumerator k l p r) ∧
    a k l (intersectionNumerator k l p r)<norm k l*eval k l (width r) := by
  let w := eval k l (width r)
  let ap := a k l p
  let bp := b k l p
  let aq := a k l p+eval k l (shiftA (exitDirection r))
  have hbp : 0<bp := h.1.2.1
  have hwa : 0<w-bp := by have := h.2.1; dsimp [w,bp]; omega
  have hap : 0<ap := h.1.1
  have haq : 0<aq := by have := h.2.2.2; dsimp [aq,ap,bp,w] at *; omega
  have hapt : 0<norm k l-ap := by
    have hb := h.1.2.1
    have hc := h.1.2.2
    dsimp [c] at hc
    dsimp [ap]
    omega
  have haqt : 0<norm k l-aq := by have := h.2.2.1; dsimp [aq]; omega
  have hn : a k l (intersectionNumerator k l p r)=(w-bp)*ap+bp*aq := by
    rw [(intersection_slices k l p r).1]
    dsimp [w,bp,ap,aq]
    ring
  have hnt : norm k l*w-a k l (intersectionNumerator k l p r)=
      (w-bp)*(norm k l-ap)+bp*(norm k l-aq) := by rw [hn]; ring
  refine ⟨h.1.2.1,h.2.1,(intersection_slices k l p r).2,?_,?_⟩
  · rw [hn]
    exact add_pos (mul_pos hwa hap) (mul_pos hbp haq)
  · have hpos := add_pos (mul_pos hwa hapt) (mul_pos hbp haqt)
    rw [← hnt] at hpos
    exact sub_pos.mp hpos

end R002.GCPrimitive
