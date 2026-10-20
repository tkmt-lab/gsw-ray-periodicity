import Formal.ClaudeBeltPath
import Mathlib.Tactic.LinearCombination

/-!
# Positive side of A3, part 1: coarse triangles and their charts

Written by a Claude worker (2026-10-19). Generic machinery for developing a strip of
parent faces into the plane.

The parent (coarse) lattice is spanned by `z=(k,l)` and `w=rot z=(-l,k+l)`;
`pos k l (i,j)=i z+j w`. A coarse triangle `CT` is an up triangle
`(i,j),(i+1,j),(i,j+1)` or a down triangle `(i+1,j),(i+1,j+1),(i,j+1)` (vertices listed
counterclockwise). A lattice point is *in* a coarse triangle when it is strictly inside.
For each coarse triangle and each `r : Fin 3` there is a chart (an orientation preserving
lattice isometry) sending its `m`-th vertex to `ClaudeChallenge.corner k l (r+m)`.
-/

namespace ClaudePos
open R002 R002.Icosahedron R002.GCPrimitive R002.GCPrimitiveSurface R002.GCChallengeBridge
open ClaudeChallenge (rot rotN)

variable {k l : ℤ}

/-! ## Rotations -/

theorem rot_add (x y : Lattice) : rot (x+y)=rot x+rot y := by
  ext <;> simp only [rot,Prod.fst_add,Prod.snd_add] <;> ring

theorem rotN_add (n : ℕ) (x y : Lattice) : rotN n (x+y)=rotN n x+rotN n y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rotN,ih,rot_add]

theorem rotN_sub (n : ℕ) (x y : Lattice) : rotN n (x-y)=rotN n x-rotN n y := by
  rw [eq_sub_iff_add_eq,← rotN_add,sub_add_cancel]

theorem rotN_rotN (m n : ℕ) (x : Lattice) : rotN m (rotN n x)=rotN (m+n) x := by
  induction m with
  | zero => simp [rotN]
  | succ m ih => rw [show m+1+n=(m+n)+1 by omega]; simp only [rotN,ih]

theorem rotN_six (x : Lattice) : rotN 6 x=x := by
  ext <;> simp [rotN,rot] <;> ring

theorem rotN_six_mul (q : ℕ) (x : Lattice) : rotN (6*q) x=x := by
  induction q with
  | zero => rfl
  | succ q ih => rw [show 6*(q+1)=6+6*q by ring,← rotN_rotN,ih,rotN_six]

theorem rotN_mod (n : ℕ) (x : Lattice) : rotN n x=rotN (n%6) x := by
  conv_lhs => rw [← Nat.mod_add_div n 6]
  rw [← rotN_rotN,rotN_six_mul]

theorem rot_direction : ∀ i : Fin 6, rot (direction i)=direction (i+1) := by decide

theorem rotN_direction (m : ℕ) (i : Fin 6) : ∃ j, rotN m (direction i)=direction j := by
  induction m with
  | zero => exact ⟨i,rfl⟩
  | succ m ih =>
    obtain ⟨j,hj⟩ := ih
    exact ⟨j+1,by simp only [rotN,hj,rot_direction]⟩

theorem unit_aff (m : ℕ) (t x y : Lattice) (h : GCPrimitive.Unit x y) :
    GCPrimitive.Unit (rotN m x+t) (rotN m y+t) := by
  obtain ⟨i,rfl⟩ := h
  obtain ⟨j,hj⟩ := rotN_direction m i
  exact ⟨j,by rw [rotN_add,hj,add_right_comm]⟩

theorem rotN_injective (m : ℕ) : Function.Injective (rotN m) := by
  intro x y h
  have := congrArg (rotN ((6-m%6))) h
  rw [rotN_rotN,rotN_rotN,rotN_mod _ x,rotN_mod _ y,show (6-m%6+m)%6=0 by omega] at this
  exact this

/-! ## Coarse triangles -/

structure CT where
  up : Bool
  i : ℤ
  j : ℤ
  deriving DecidableEq

def CT.vert (D : CT) : Fin 3 → ℤ × ℤ :=
  if D.up then ![(D.i,D.j),(D.i+1,D.j),(D.i,D.j+1)]
  else ![(D.i+1,D.j),(D.i+1,D.j+1),(D.i,D.j+1)]

/-- Position of a coarse vertex: `i z + j w`. -/
def pos (k l : ℤ) (c : ℤ × ℤ) : Lattice := (c.1*k-c.2*l,c.1*l+c.2*(k+l))

theorem pos_add (c d : ℤ × ℤ) : pos k l (c+d)=pos k l c+pos k l d := by
  ext <;> simp [pos] <;> ring

theorem pos_sub (c d : ℤ × ℤ) : pos k l (c-d)=pos k l c-pos k l d := by
  ext <;> simp [pos] <;> ring

theorem a_pos (c : ℤ × ℤ) : a k l (pos k l c)=c.1*norm k l := by
  simp only [a,pos,norm]; ring

theorem b_pos (c : ℤ × ℤ) : b k l (pos k l c)=c.2*norm k l := by
  simp only [b,pos,norm]; ring

theorem a_add (x y : Lattice) : a k l (x+y)=a k l x+a k l y := by
  simp only [a,Prod.fst_add,Prod.snd_add]; ring
theorem b_add (x y : Lattice) : b k l (x+y)=b k l x+b k l y := by
  simp only [b,Prod.fst_add,Prod.snd_add]; ring
theorem a_sub (x y : Lattice) : a k l (x-y)=a k l x-a k l y := by
  simp only [a,Prod.fst_sub,Prod.snd_sub]; ring
theorem b_sub (x y : Lattice) : b k l (x-y)=b k l x-b k l y := by
  simp only [b,Prod.fst_sub,Prod.snd_sub]; ring

/-- Strictly inside a coarse triangle (in the coarse coordinates `a/T`, `b/T`). -/
def InCT (k l : ℤ) (D : CT) (x : Lattice) : Prop :=
  if D.up then
    D.i*norm k l<a k l x ∧ D.j*norm k l<b k l x ∧ a k l x+b k l x<(D.i+D.j+1)*norm k l
  else
    a k l x<(D.i+1)*norm k l ∧ b k l x<(D.j+1)*norm k l ∧
      (D.i+D.j+1)*norm k l<a k l x+b k l x

theorem lt_of_mul_lt_mul_T {T m n : ℤ} (hT : 0<T) (h : m*T<n*T) : m<n :=
  lt_of_mul_lt_mul_right h hT.le

/-- The slots of a coarse triangle. -/
theorem inCT_slots (hk : 0<k) (hl : 0<l) (D : CT) (x : Lattice) (h : InCT k l D x) :
    D.i*norm k l<a k l x ∧ a k l x<(D.i+1)*norm k l ∧
    D.j*norm k l<b k l x ∧ b k l x<(D.j+1)*norm k l ∧
    (D.i+D.j+(if D.up then 0 else 1))*norm k l<a k l x+b k l x ∧
    a k l x+b k l x<(D.i+D.j+(if D.up then 0 else 1)+1)*norm k l := by
  rcases D with ⟨_|_,i,j⟩ <;> simp only [InCT,Bool.false_eq_true,ite_false,ite_true] at h ⊢ <;>
    obtain ⟨h1,h2,h3⟩ := h <;> refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith

theorem slot_eq {T x m n : ℤ} (hT : 0<T) (h1 : m*T<x) (h2 : x<(m+1)*T)
    (h3 : n*T<x) (h4 : x<(n+1)*T) : m=n := by
  have : m<n+1 := lt_of_mul_lt_mul_T hT (h1.trans h4)
  have : n<m+1 := lt_of_mul_lt_mul_T hT (h3.trans h2)
  omega

theorem inCT_unique (hk : 0<k) (hl : 0<l) (D D' : CT) (x : Lattice)
    (h : InCT k l D x) (h' : InCT k l D' x) : D=D' := by
  have hT := norm_pos k l hk hl.le
  obtain ⟨a1,a2,b1,b2,c1,c2⟩ := inCT_slots hk hl D x h
  obtain ⟨a1',a2',b1',b2',c1',c2'⟩ := inCT_slots hk hl D' x h'
  have ei := slot_eq hT a1 a2 a1' a2'
  have ej := slot_eq hT b1 b2 b1' b2'
  have ec := slot_eq hT c1 (by simpa [add_assoc] using c2) c1' (by simpa [add_assoc] using c2')
  rcases D with ⟨_|_,i,j⟩ <;> rcases D' with ⟨_|_,i',j'⟩ <;> simp at ei ej ec ⊢ <;> omega

theorem not_inCT_pos (hk : 0<k) (hl : 0<l) (D : CT) (c : ℤ × ℤ) : ¬InCT k l D (pos k l c) := by
  intro h
  have hT := norm_pos k l hk hl.le
  obtain ⟨a1,a2,b1,b2,c1,c2⟩ := inCT_slots hk hl D _ h
  rw [a_pos] at a1 a2 c1 c2; rw [b_pos] at b1 b2 c1 c2
  rw [← add_mul] at c1 c2
  have := lt_of_mul_lt_mul_T hT a1
  have := lt_of_mul_lt_mul_T hT a2
  have := lt_of_mul_lt_mul_T hT b1
  have := lt_of_mul_lt_mul_T hT b2
  omega

/-! ## Primitive lines and existence of the coarse triangle -/

theorem bezout (hprim : Primitive k l) : ∃ u v : ℤ, u*k+v*l=1 :=
  ⟨Int.gcdA k l,Int.gcdB k l,by
    have h1 : (Int.gcd k l : ℤ)=1 := by exact_mod_cast hprim
    linarith [Int.gcd_eq_gcd_ab k l]⟩

theorem line_a (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) (y : Lattice) (h : a k l y=0) :
    ∃ t, y=pos k l (0,t) := by
  obtain ⟨u,v,huv⟩ := bezout hprim
  simp only [a] at h
  refine ⟨u*y.2-(v-u)*y.1,Prod.ext ?_ ?_⟩ <;> simp only [pos]
  · linear_combination u*h-y.1*huv
  · linear_combination (v-u)*h-y.2*huv

theorem line_c (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) (y : Lattice)
    (h : a k l y+b k l y=0) : ∃ t, y=pos k l (-t,t) := by
  obtain ⟨u,v,huv⟩ := bezout hprim
  simp only [a,b] at h
  refine ⟨(u-v)*y.2-v*y.1,Prod.ext ?_ ?_⟩ <;> simp only [pos]
  · linear_combination (u-v)*h-y.1*huv
  · linear_combination v*h-y.2*huv

/-- A lattice point which is not a coarse vertex lies in a coarse triangle. -/
theorem inCT_exists (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) (x : Lattice)
    (hx : ∀ c, x≠pos k l c) : ∃ D, InCT k l D x := by
  have hT := norm_pos k l hk hl.le
  set T := norm k l
  set i := a k l x/T
  set j := b k l x/T
  have hi1 : i*T≤a k l x := Int.ediv_mul_le _ hT.ne'
  have hi2 : a k l x<(i+1)*T := Int.lt_ediv_add_one_mul_self _ hT
  have hj1 : j*T≤b k l x := Int.ediv_mul_le _ hT.ne'
  have hj2 : b k l x<(j+1)*T := Int.lt_ediv_add_one_mul_self _ hT
  have hi : i*T<a k l x := by
    refine lt_of_le_of_ne hi1 fun he => ?_
    obtain ⟨t,ht⟩ := line_a hk hl hprim (x-pos k l (i,0)) (by rw [a_sub,a_pos]; simp only; rw [← he]; ring)
    exact hx (i,t) (by
      have := sub_eq_iff_eq_add.mp ht
      rw [this]; ext <;> simp [pos] <;> ring)
  have hj : j*T<b k l x := by
    refine lt_of_le_of_ne hj1 fun he => ?_
    obtain ⟨t,ht⟩ := primitive_line k l hk hprim (x-pos k l (0,j)) (by rw [b_sub,b_pos]; simp only; rw [← he]; ring)
    exact hx (t,j) (by
      have := sub_eq_iff_eq_add.mp ht
      rw [this]; ext <;> simp [pos] <;> ring)
  rcases lt_trichotomy (a k l x+b k l x) ((i+j+1)*T) with hs | hs | hs
  · exact ⟨⟨true,i,j⟩,by simp only [InCT,ite_true]; exact ⟨hi,hj,hs⟩⟩
  · exfalso
    obtain ⟨t,ht⟩ := line_c hk hl hprim (x-pos k l (i+j+1,0)) (by
      rw [a_sub,b_sub,a_pos,b_pos]; simp only; linarith)
    exact hx (i+j+1-t,t) (by
      have := sub_eq_iff_eq_add.mp ht
      rw [this]; ext <;> simp [pos] <;> ring)
  · exact ⟨⟨false,i,j⟩,by simp only [InCT,Bool.false_eq_true,ite_false]; exact ⟨hi2,hj2,hs⟩⟩

end ClaudePos
