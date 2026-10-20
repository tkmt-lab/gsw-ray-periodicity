import Formal.ClaudePosBand

/-!
# Positive side of A3, part 7: every interior band point lies in a listed triangle

Written by a Claude worker (2026-10-19), following section 3 of the verifier's proof.
For a band point `x=(t,y)` the row functional is `σ(x)=a+v b=d' t+e y` with
`d'=k+l-v l`, `e=l+v k`, and `σ(E)=T·s(E)`.

* If `σ0 T ≤ σ(x) ≤ (σ0+1) T` (`{σ0,σ0+1}={0,s(E)}`), the triangle of `x` is in the
  periodic strip (`strip_rows`), and `x` is not a parent vertex unless `x=0` or `x=E`.
* Otherwise (only for the lower band with `s(E)=1` and the upper band with `s(E)=-1`)
  `x` or `E-x` is one of the first points `(x',∓1)`, whose triangle is pinned down
  to at most five explicit triangles near the origin.
-/

namespace ClaudePos
open R002 R002.Icosahedron R002.GCPrimitive R002.GCPrimitiveSurface R002.GCChallengeBridge

variable {k l : ℤ}

theorem sigma_xy (v t y : ℤ) : a k l (t,y)+v*b k l (t,y)=(k+l-v*l)*t+(l+v*k)*y := by
  simp only [a,b]; ring

theorem sigma_pos (v : ℤ) (c : ℤ × ℤ) : a k l (pos k l c)+v*b k l (pos k l c)=(c.1+v*c.2)*norm k l := by
  rw [a_pos,b_pos]; ring

theorem small_mul (m d : ℤ) (hd : 2≤d ∨ d≤ -2) (h1 : -1≤m*d) (h2 : m*d≤1) : m=0 := by
  rcases lt_trichotomy m 0 with h | h | h
  · rcases hd with hd | hd <;> nlinarith
  · exact h
  · rcases hd with hd | hd <;> nlinarith

/-- Parent vertices in the closed band between the rows `0` and `s(E)`. -/
theorem vertex_cases (hk : 0<k) (hl : 0<l) (v σ0 σE : ℤ) (Ec c : ℤ × ℤ)
    (hEy : (pos k l Ec).2=σE) (hσE : σE=1 ∨ σE=-1) (hd : 2≤k+l-v*l ∨ k+l-v*l≤ -2)
    (hrows : (σ0=0 ∧ Ec.1+v*Ec.2=1) ∨ (σ0=-1 ∧ Ec.1+v*Ec.2=-1))
    (h0 : σ0*norm k l≤a k l (pos k l c)+v*b k l (pos k l c))
    (h1 : a k l (pos k l c)+v*b k l (pos k l c)≤(σ0+1)*norm k l)
    (hy : (pos k l c).2=0 ∨ (pos k l c).2=σE) : pos k l c=(0,0) ∨ c=Ec := by
  have hT := norm_pos k l hk hl.le
  rw [sigma_pos] at h0 h1
  have e0 := le_of_mul_le_mul_right h0 hT
  have e1 := le_of_mul_le_mul_right h1 hT
  have hs : c.1+v*c.2=0 ∨ c.1+v*c.2=Ec.1+v*Ec.2 := by omega
  rcases hs with hs | hs
  · left
    have h1' : c.1=-(v*c.2) := by linarith
    have hy2 : (pos k l c).2=c.2*(k+l-v*l) := by simp only [pos]; rw [h1']; ring
    have : c.2=0 := small_mul _ _ hd (by rw [← hy2]; rcases hy with hy | hy <;> rw [hy] <;> omega)
      (by rw [← hy2]; rcases hy with hy | hy <;> rw [hy] <;> omega)
    ext <;> simp [pos,h1',this]
  · right
    have h1' : c.1-Ec.1=-(v*(c.2-Ec.2)) := by linarith
    have hy2 : (pos k l c).2-(pos k l Ec).2=(c.2-Ec.2)*(k+l-v*l) := by
      simp only [pos]; linear_combination l*h1'
    have : c.2-Ec.2=0 := small_mul _ _ hd
      (by rw [← hy2,hEy]; rcases hy with hy | hy <;> rw [hy] <;> omega)
      (by rw [← hy2,hEy]; rcases hy with hy | hy <;> rw [hy] <;> omega)
    rw [this,mul_zero,neg_zero] at h1'
    ext <;> linarith

/-- Main case: a non-vertex with `σ` in the strip range lies in a strip triangle. -/
theorem cover_main (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) (v p σ0 : ℤ) (hv : 1≤v)
    (good : List (Bool × ℤ × ℤ))
    (hstrip : ∀ D : CT, σ0+1-v≤sOf v D+(if D.up then 0 else 1) →
      sOf v D+(if D.up then 0 else 1)≤σ0 → (D.up,sOf v D,D.j%p) ∈ good)
    (x : Lattice) (hx : ∀ c, x≠pos k l c) (h0 : σ0*norm k l≤a k l x+v*b k l x)
    (h1 : a k l x+v*b k l x≤(σ0+1)*norm k l) :
    ∃ D, InCT k l D x ∧ (D.up,sOf v D,D.j%p) ∈ good := by
  obtain ⟨D,hD⟩ := inCT_exists hk hl hprim x hx
  obtain ⟨r1,r2⟩ := strip_rows hk hl v σ0 hv D x hD h0 h1
  exact ⟨D,hD,hstrip D r1 r2⟩

/-- The four triangles below the origin row: `a ∈ (0,2T)`, `b ∈ (-T,0)`. -/
theorem pin_four (hk : 0<k) (hl : 0<l) (D : CT) (x : Lattice) (h : InCT k l D x)
    (ha0 : 0<a k l x) (ha1 : a k l x<2*norm k l) (hb0 : -norm k l<b k l x) (hb1 : b k l x<0) :
    D.j=-1 ∧ (D.i=0 ∨ D.i=1) := by
  have hT := norm_pos k l hk hl.le
  obtain ⟨a1,a2,b1,b2,-⟩ := inCT_slots hk hl D x h
  have := lt_of_mul_lt_mul_T hT (show D.i*norm k l<2*norm k l by linarith)
  have := lt_of_mul_lt_mul_T hT (show 0*norm k l<(D.i+1)*norm k l by linarith)
  have := lt_of_mul_lt_mul_T hT (show D.j*norm k l<0*norm k l by linarith)
  have := lt_of_mul_lt_mul_T hT (show (-1)*norm k l<(D.j+1)*norm k l by linarith)
  omega

/-- The triangle `[0,z,w]`: `a,b,a+b ∈ (0,T)`. -/
theorem pin_up00 (hk : 0<k) (hl : 0<l) (D : CT) (x : Lattice) (h : InCT k l D x)
    (ha0 : 0<a k l x) (hb0 : 0<b k l x) (hc : a k l x+b k l x<norm k l) : D=⟨true,0,0⟩ := by
  have hT := norm_pos k l hk hl.le
  exact inCT_unique hk hl D _ x h (by simp only [InCT,ite_true]; refine ⟨?_,?_,?_⟩ <;> linarith)

/-! ## Band parametrizations -/

theorem upper_param (A n : ℕ) (h0 : 0<n) (h1 : n<2*A+1) :
    (∃ t : ℤ, upperP n=(t,0) ∧ 1≤t ∧ t≤A) ∨ (∃ t : ℤ, upperP n=(t,1) ∧ 0≤t ∧ t≤A-1) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · left; refine ⟨((n/2 : ℕ) : ℤ),by simp [upperP,h],by omega,by omega⟩
  · right; refine ⟨((n/2 : ℕ) : ℤ),by simp [upperP,h],by omega,by omega⟩

theorem lower_param (A n : ℕ) (h0 : 0<n) (h1 : n<2*A-1) :
    (∃ t : ℤ, lowerP n=(t,0) ∧ 1≤t ∧ t≤A-1) ∨ (∃ t : ℤ, lowerP n=(t,-1) ∧ 1≤t ∧ t≤A-1) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · left; refine ⟨((n/2 : ℕ) : ℤ),by simp [lowerP,h],by omega,by omega⟩
  · right; refine ⟨((n/2+1 : ℕ) : ℤ),by simp [lowerP,h],by omega,by omega⟩

end ClaudePos
