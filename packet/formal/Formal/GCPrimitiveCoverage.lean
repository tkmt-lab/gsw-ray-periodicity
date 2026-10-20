import Formal.GCPrimitiveInterior
import Formal.GCPrimitiveIntersection

/-! Every lattice step starting inside a parent face lands in that face or
in a single adjacent face. The crucial lateral bounds are proved, not assumed.
This is a discrete chart statement; no continuous surface is imported. -/
namespace R002.GCPrimitive

theorem integer_strip (t z : ℤ) (ht : 0<t) (hlo : -t<t*z) (hhi : t*z<t) : z=0 := by
  have h0 : z≤0 := by
    by_contra h
    have : 1≤z := by omega
    nlinarith
  have h1 : 0≤z := by
    by_contra h
    have : z≤ -1 := by omega
    nlinarith
  omega

theorem no_positive_strip (t z : ℤ) (ht : 0<t) (hlo : 0<t*z) (hhi : t*z<t) : False := by
  have hz := integer_strip t z ht (by omega) hhi
  simp [hz] at hlo

theorem unit_turn (k l : ℤ) (p q : Lattice) (h : Unit p q) :
    Unit (turn k l p) (turn k l q) := by
  obtain ⟨i,rfl⟩ := h
  refine ⟨i+2,?_⟩
  fin_cases i <;> ext <;> simp [turn,direction] <;> ring

theorem unit_opposite (k l : ℤ) (p q : Lattice) (h : Unit p q) :
    Unit (opposite k l p) (opposite k l q) := by
  obtain ⟨i,rfl⟩ := h
  refine ⟨i+3,?_⟩
  fin_cases i <;> ext <;> simp [opposite,direction] <;> ring

theorem unit_symm (p q : Lattice) (h : Unit p q) : Unit q p := by
  obtain ⟨i,rfl⟩ := h
  refine ⟨i+3,?_⟩
  fin_cases i <;> ext <;> simp [direction]

theorem unit_ne (p q : Lattice) (h : Unit p q) : p≠q := by
  rintro rfl
  obtain ⟨i,h⟩ := h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases i <;> simp [direction] at hx hy

/-- The first exiting direction cannot pass beyond the A corner. -/
theorem oa_right_bound (k l : ℤ) (hk : 0<k) (hl : 0<l)
    (p : Lattice) (hp : Interior k l p) (hb : b k l p<l) :
    a k l p+k+l<norm k l := by
  by_contra h
  have hs : b k l p+c k l p≤k+l := by dsimp [c] at *; omega
  have hT := norm_pos k l hk hl.le
  have hy : norm k l*(p.2-l)=k*b k l p-l*c k l p := by dsimp [norm,a,b,c]; ring
  have hup : norm k l*(p.2-l)<norm k l := by
    have hb' := mul_lt_mul_of_pos_left hb hk
    have hc' := mul_pos hl hp.2.2
    dsimp [norm] at *
    nlinarith [sq_pos_of_pos hk, sq_nonneg l]
  have hlo : -norm k l<norm k l*(p.2-l) := by
    have hc : c k l p<k+l := by have := hp.2.1; omega
    have hc' := mul_lt_mul_of_pos_left hc hl
    have hb' := mul_pos hk hp.2.1
    dsimp [norm] at *
    nlinarith [sq_pos_of_pos hk]
  have hz := integer_strip _ _ hT hlo hup
  have he : b k l p=l*(k-p.1) := by dsimp [b]; nlinarith
  exact no_positive_strip l (k-p.1) hl (by rw [← he]; exact hp.2.1) (by rw [← he]; exact hb)

/-- The downward step cannot continue past the O corner after crossing OA. -/
theorem oa_left_bound (k l : ℤ) (hk : 0<k) (hl : 0<l)
    (p : Lattice) (hp : Interior k l p) (hb : b k l p<k) :
    k+l<a k l p+b k l p := by
  by_contra h
  have hs : a k l p+b k l p≤k+l := by omega
  have hy := (recover_coordinates k l p).2
  have lo : 0<norm k l*p.2 := by
    rw [hy]
    exact add_pos (mul_pos hl hp.1) (mul_pos (by omega) hp.2.1)
  have hi : norm k l*p.2<norm k l := by
    have hs' := mul_le_mul_of_nonneg_left hs hl.le
    have hb' := mul_lt_mul_of_pos_left hb hk
    dsimp [norm] at *
    nlinarith
  exact no_positive_strip _ _ (norm_pos k l hk hl.le) lo hi

theorem diagonal_right_bound (k l : ℤ) (hk : 0<k) (hl : 0<l)
    (p : Lattice) (hp : Interior k l p) : a k l p+k<norm k l := by
  by_contra h
  have hs : b k l p+c k l p≤k := by dsimp [c] at *; omega
  have hx : norm k l*(k-p.1)=k*c k l p+(k+l)*b k l p := by dsimp [norm,a,b,c]; ring
  have lo : 0<norm k l*(k-p.1) := by
    rw [hx]
    exact add_pos (mul_pos hk hp.2.2) (mul_pos (by omega) hp.2.1)
  have hi : norm k l*(k-p.1)<norm k l := by
    have hs' := mul_le_mul_of_nonneg_left hs (show 0≤k+l by omega)
    have hc' := mul_pos hl hp.2.2
    dsimp [norm] at *
    nlinarith [sq_pos_of_pos hl]
  exact no_positive_strip _ _ (norm_pos k l hk hl.le) lo hi

theorem diagonal_left_bound (k l : ℤ) (hk : 0<k) (hl : 0<l)
    (p : Lattice) (hp : Interior k l p) : l<a k l p+b k l p := by
  by_contra h
  have hs : a k l p+b k l p≤l := by omega
  have hy := (recover_coordinates k l p).2
  have lo : 0<norm k l*p.2 := by
    rw [hy]
    exact add_pos (mul_pos hl hp.1) (mul_pos (by omega) hp.2.1)
  have hi : norm k l*p.2<norm k l := by
    have hs' := mul_le_mul_of_nonneg_left hs (show 0≤k+l by omega)
    have ha' := mul_pos hk hp.1
    dsimp [norm] at *
    nlinarith [sq_pos_of_pos hk]
  exact no_positive_strip _ _ (norm_pos k l hk hl.le) lo hi

/-- All lateral inequalities follow from an actual lattice interior point. -/
theorem exit_width_complete (k l : ℤ) (hk : 0<k) (hl : 0<l)
    (p : Lattice) (hp : Interior k l p) (r : Fin 3)
    (hb : b k l p<eval k l (width r)) : Cut k l p r := by
  refine ⟨hp,hb,?_,?_⟩
  · fin_cases r <;> norm_num [width,shiftA,exitDirection,eval] at hb ⊢
    · simpa only [add_assoc] using oa_right_bound k l hk hl p hp hb
    · have := hp.2.1; have := hp.2.2; dsimp [c] at *; omega
    · exact diagonal_right_bound k l hk hl p hp
  · fin_cases r <;> norm_num [width,shiftA,exitDirection,eval] at hb ⊢
    · have := hp.1; have := hp.2.1; omega
    · have := oa_left_bound k l hk hl p hp hb; omega
    · have := diagonal_left_bound k l hk hl p hp; omega

/-- A step through OA always ends in its immediate neighbor, never beyond it. -/
theorem negative_b_lands (k l : ℤ) (hk : 0<k) (hl : 0<l)
    (p q : Lattice) (hp : Interior k l p) (hu : Unit p q) (hb : b k l q<0) :
    Interior k l (opposite k l q) := by
  obtain ⟨i,rfl⟩ := hu
  have hn : eval k l (shiftB i)<0 := by
    rw [(step_slices k l p i).2] at hb
    have := hp.2.1; omega
  obtain ⟨r,hr⟩ := negative_shift_is_exit k l hk hl i hn
  subst i
  have hb' : b k l p<eval k l (width r) := by
    rw [(step_slices k l p (exitDirection r)).2,exit_shift] at hb
    omega
  exact ((cut_iff k l p r).mp (exit_width_complete k l hk hl p hp r hb')).2.1

end R002.GCPrimitive
