import Formal.ClaudePosPath

/-!
# Positive side of A3, part 4: periodic strip labelings

Written by a Claude worker (2026-10-19).

The developed strip of parent faces runs along `V = v z - w` (coarse vector `(v,-1)`).
A coarse vertex `(i,j)` gets the label `Lab (i+v*j) (j % p)`: it depends on the row
`s=i+v*j` (constant along `V`) and on `j` modulo the period `p`.
Hence whether a coarse triangle is a face, and which face, depends only on its
*type* `tri D=(up, s, j % p)`, a finite amount of data checked by `decide`.
Two triangles of the same type differ by a multiple of `p V`.
-/

namespace ClaudePos
open R002 R002.Icosahedron R002.GCPrimitive R002.GCPrimitiveSurface R002.GCChallengeBridge
open ClaudeChallenge (rot rotN)

variable {k l : ℤ}

/-- The strip labeling of coarse vertices. -/
def SL (v p : ℤ) (Lab : ℤ → ℤ → Fin 12) (c : ℤ × ℤ) : Fin 12 := Lab (c.1+v*c.2) (c.2%p)

/-- The labels of a coarse triangle of type `(up,s,c)`. -/
def triLab (v p : ℤ) (Lab : ℤ → ℤ → Fin 12) (up : Bool) (s c : ℤ) : Fin 3 → Fin 12 :=
  if up then ![Lab s c,Lab (s+1) c,Lab (s+v) ((c+1)%p)]
  else ![Lab (s+1) c,Lab (s+1+v) ((c+1)%p),Lab (s+v) ((c+1)%p)]

def triF (v p : ℤ) (Lab : ℤ → ℤ → Fin 12) (up : Bool) (s c : ℤ) : Fin 20 × Fin 3 :=
  findFR (triLab v p Lab up s c 0) (triLab v p Lab up s c 1) (triLab v p Lab up s c 2)

def TriOK (v p : ℤ) (Lab : ℤ → ℤ → Fin 12) (up : Bool) (s c : ℤ) : Prop :=
  ∀ m : Fin 3, ClaudeChallenge.face (triF v p Lab up s c).1 ((triF v p Lab up s c).2+m)=
    triLab v p Lab up s c m

instance (v p : ℤ) (Lab : ℤ → ℤ → Fin 12) (up : Bool) (s c : ℤ) :
    Decidable (TriOK v p Lab up s c) := by unfold TriOK; infer_instance

def sOf (v : ℤ) (D : CT) : ℤ := D.i+v*D.j

theorem emod_succ (p j : ℤ) : (j+1)%p=(j%p+1)%p := by
  rw [Int.add_emod j 1 p,Int.add_emod (j%p) 1 p,Int.emod_emod]

theorem SL_vert (v p : ℤ) (Lab : ℤ → ℤ → Fin 12) (D : CT) (m : Fin 3) :
    SL v p Lab (D.vert m)=triLab v p Lab D.up (sOf v D) (D.j%p) m := by
  rcases D with ⟨_|_,i,j⟩ <;> fin_cases m <;>
    simp [SL,triLab,CT.vert,sOf] <;> first | rfl | (congr 1 <;> first | ring | exact emod_succ p j)

theorem fr_SL (v p : ℤ) (Lab : ℤ → ℤ → Fin 12) (D : CT) :
    fr (SL v p Lab) D=triF v p Lab D.up (sOf v D) (D.j%p) := by
  simp only [fr,triF,SL_vert]

theorem faceOK_of_tri (v p : ℤ) (Lab : ℤ → ℤ → Fin 12) (D : CT)
    (h : TriOK v p Lab D.up (sOf v D) (D.j%p)) : FaceOK (SL v p Lab) D := by
  intro m
  rw [fr_SL,SL_vert]
  exact h m

/-! ## Same type means a translate by a multiple of `p V` -/

theorem chart_shift (D D' : CT) (hup : D'.up=D.up) (r : Fin 3) (y : Lattice) :
    chart k l D' r y=chart k l D r (y-pos k l (D'.i-D.i,D'.j-D.j)) := by
  have hv : pos k l (D'.vert 0)=pos k l (D.vert 0)+pos k l (D'.i-D.i,D'.j-D.j) := by
    rw [← pos_add]; congr 1
    rcases D with ⟨_|_,i,j⟩ <;> rcases D' with ⟨_|_,i',j'⟩ <;> simp at hup <;>
      ext <;> simp [CT.vert] <;> ring
  have hM : chartM D' r=chartM D r := by simp [chartM,hup]
  simp only [chart,hM,hv]
  congr 2; abel

/-- Two developed points whose sites have the same face and chart point, in triangles of the
same type, differ by a multiple of `p V`. -/
theorem same_type_translate (v p : ℤ) (Lab : ℤ → ℤ → Fin 12) (D D' : CT) (x x' : Lattice)
    (hup : D.up=D'.up) (hs : sOf v D=sOf v D') (hc : D.j%p=D'.j%p)
    (hch : chart k l D (fr (SL v p Lab) D).2 x=chart k l D' (fr (SL v p Lab) D').2 x') :
    ∃ m : ℤ, x'=x+pos k l (-(v*(m*p)),m*p) := by
  have hfr : fr (SL v p Lab) D'=fr (SL v p Lab) D := by rw [fr_SL,fr_SL,hup,hs,hc]
  rw [hfr,chart_shift D D' hup.symm] at hch
  have := chart_injective D _ hch
  obtain ⟨m,hm⟩ : p ∣ D'.j-D.j := ⟨D'.j/p-D.j/p,by
    have h1 := Int.emod_add_mul_ediv D.j p; have h2 := Int.emod_add_mul_ediv D'.j p
    rw [mul_sub]; linarith⟩
  refine ⟨m,?_⟩
  have hi : D'.i-D.i=-(v*(p*m)) := by simp only [sOf] at hs; rw [← hm]; linarith
  rw [this,hi,hm,show m*p=p*m from mul_comm m p]
  exact (sub_add_cancel _ _).symm

/-! ## The row functional `σ = a + v b` -/

theorem sigma_bounds (hk : 0<k) (hl : 0<l) (v : ℤ) (hv : 1≤v) (D : CT) (x : Lattice)
    (h : InCT k l D x) :
    (sOf v D+(if D.up then 0 else 1))*norm k l<a k l x+v*b k l x ∧
    a k l x+v*b k l x<(sOf v D+(if D.up then 0 else 1)+v)*norm k l := by
  have hT := norm_pos k l hk hl.le
  rcases D with ⟨_|_,i,j⟩ <;> simp only [InCT,sOf,Bool.false_eq_true,ite_false,ite_true] at h ⊢ <;>
    obtain ⟨h1,h2,h3⟩ := h <;> refine ⟨?_,?_⟩ <;> nlinarith

/-- Points with `σ` between `σ0 T` and `(σ0+1) T` lie in triangles of the strip
`σ0+1-v ≤ (lowest row) ≤ σ0`. -/
theorem strip_rows (hk : 0<k) (hl : 0<l) (v σ0 : ℤ) (hv : 1≤v) (D : CT) (x : Lattice)
    (h : InCT k l D x) (h0 : σ0*norm k l≤a k l x+v*b k l x)
    (h1 : a k l x+v*b k l x≤(σ0+1)*norm k l) :
    σ0+1-v≤sOf v D+(if D.up then 0 else 1) ∧ sOf v D+(if D.up then 0 else 1)≤σ0 := by
  have hT := norm_pos k l hk hl.le
  obtain ⟨b1,b2⟩ := sigma_bounds hk hl v hv D x h
  have e1 := lt_of_mul_lt_mul_T hT (b1.trans_le h1)
  have e2 := lt_of_mul_lt_mul_T hT (h0.trans_lt b2)
  omega

/-! ## Point reflection `x ↦ E - x` -/

def refl (Ec : ℤ × ℤ) (D : CT) : CT := ⟨!D.up,Ec.1-D.i-1,Ec.2-D.j-1⟩

theorem inCT_refl (Ec : ℤ × ℤ) (D : CT) (x : Lattice) :
    InCT k l D x ↔ InCT k l (refl Ec D) (pos k l Ec-x) := by
  rcases D with ⟨_|_,i,j⟩ <;>
    simp only [InCT,refl,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true,
      a_sub,b_sub,a_pos,b_pos] <;>
    constructor <;> rintro ⟨h1,h2,h3⟩ <;> refine ⟨?_,?_,?_⟩ <;> nlinarith

theorem refl_vert (Ec : ℤ × ℤ) (D : CT) (m : Fin 3) : ∃ m', (refl Ec D).vert m'=Ec-D.vert m := by
  rcases D with ⟨_|_,i,j⟩ <;> fin_cases m
  · exact ⟨2,by ext <;> simp [refl,CT.vert] <;> ring⟩
  · exact ⟨0,by ext <;> simp [refl,CT.vert] <;> ring⟩
  · exact ⟨1,by ext <;> simp [refl,CT.vert] <;> ring⟩
  · exact ⟨1,by ext <;> simp [refl,CT.vert] <;> ring⟩
  · exact ⟨2,by ext <;> simp [refl,CT.vert] <;> ring⟩
  · exact ⟨0,by ext <;> simp [refl,CT.vert] <;> ring⟩

/-! ## Pinning a triangle by its slots -/

theorem ct_pin (hk : 0<k) (hl : 0<l) (D : CT) (x : Lattice) (h : InCT k l D x) (m n : ℤ)
    (ha1 : m*norm k l<a k l x) (ha2 : a k l x<(m+1)*norm k l)
    (hb1 : n*norm k l<b k l x) (hb2 : b k l x<(n+1)*norm k l) : D.i=m ∧ D.j=n := by
  have hT := norm_pos k l hk hl.le
  obtain ⟨a1,a2,b1,b2,-⟩ := inCT_slots hk hl D x h
  exact ⟨slot_eq hT a1 a2 ha1 ha2,slot_eq hT b1 b2 hb1 hb2⟩

end ClaudePos
