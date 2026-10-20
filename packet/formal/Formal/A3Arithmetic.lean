import Formal.LatticeTransport
import Mathlib.Tactic.Positivity

/-! A3 arithmetic, AV. Geometry, chart gluing, and the interpretation of a
candidate as the first legal endpoint remain outside these statements. -/
namespace R002.A3

def norm (k l : ℤ) : ℤ := k^2 + k*l + l^2
def gc (k l u v : ℤ) : ℤ × ℤ := (k*u-l*v, l*u+(k+l)*v)
def invRotate (z : ℤ × ℤ) : ℤ × ℤ := (z.1+z.2, -z.1)

/-- AR identities; valid for arbitrary eps, in particular eps = +1 or -1. -/
theorem unit_endpoint (q l eps : ℤ) :
    let k := q*l+eps
    let Q := q*(k+l)+l
    k*Q = q*norm k l+eps*l ∧ l*Q = norm k l-eps*(k+l) := by
  dsimp [norm]
  constructor <;> ring

theorem second_plus (s r : ℤ) :
    let l := s*r+1; let k := 2*l+r; let Q := s*(3*k+l)+k
    r*Q+(3*k+l) = norm k l ∧ gc k l (3*s+1) (-s) = (Q,1) := by
  dsimp [norm, gc]; constructor
  · ring
  · ext <;> ring

theorem second_minus (s r : ℤ) :
    let l := s*r-1; let k := 2*l+r; let Q := s*(2*k+3*l)+(k+l)
    r*Q-(2*k+3*l) = norm k l ∧ gc k l s (2*s+1) = (1,Q) := by
  dsimp [norm, gc]; constructor
  · ring
  · ext <;> ring

theorem diagonal_plus (s w : ℤ) :
    let l := s*w+1; let k := l+w; let Q := s*(2*k+l)+k
    w*Q+(2*k+l) = norm k l ∧ gc k l (2*s+1) (-s) = (Q,1) := by
  dsimp [norm, gc]; constructor
  · ring
  · ext <;> ring

theorem diagonal_minus (s w : ℤ) :
    let l := s*w-1; let k := l+w; let Q := s*(k+2*l)+(k+l)
    w*Q-(k+2*l) = norm k l ∧ gc k l s (s+1) = (1,Q) := by
  dsimp [norm, gc]; constructor
  · ring
  · ext <;> ring

theorem folded_second_plus (s w : ℤ) :
    let l := s*w+1; let k := 2*l-w; let Q := s*(2*k+3*l)-(k+l)
    w*Q+(2*k+3*l) = norm k l ∧ gc k l s (2*s-1) = (1,Q) := by
  dsimp [norm, gc]; constructor
  · ring
  · ext <;> ring

theorem folded_second_minus (s w : ℤ) :
    let l := s*w-1; let k := 2*l-w; let Q := s*(3*k+l)-k
    w*Q-(3*k+l) = norm k l ∧ gc k l (3*s-1) (-s) = (Q,1) := by
  dsimp [norm, gc]; constructor
  · ring
  · ext <;> ring

/-- AT q>=3: these are coordinate identities, not a proof of surface collision. -/
theorem outer_collisions (q k l : ℤ) :
    let a := (q-4)*k+(q+2)*l-1; let b := (q+2)*k+6*l-1
    (1,a) = rotate60 (0,b) + gc k l (q+2) (-6) ∧
    (a,0) = rotate60 (b,1) + gc k l (q-4) (-(q+2)) := by
  dsimp [rotate60, gc]; constructor <;> apply Prod.ext <;> simp <;> ring

theorem positive_fan_collisions (c s k l : ℤ) :
    let a := (c+1)*s*k+(s-5)*l-1; let b := (c*s+5)*k+(c+1)*s*l-1
    (0,a) = invRotate (1,b) + gc k l (-(c*s+5)) ((c+1)*s) ∧
    (a,1) = invRotate (b,0) + gc k l (s-5) (c*s+5) := by
  dsimp [invRotate, gc]; constructor <;> apply Prod.ext <;> simp <;> ring

theorem negative_fan_collisions (s k l : ℤ) :
    let a := (2*s-5)*k+3*s*l-1; let b := 3*s*k+(s+5)*l-1
    (1,a) = rotate60 (0,b) + gc k l (3*s) (-(s+5)) ∧
    (a,0) = rotate60 (b,1) + gc k l (2*s-5) (-3*s) := by
  dsimp [rotate60, gc]; constructor <;> apply Prod.ext <;> simp <;> ring

/-- A positive proper residue cannot be an integer multiple. -/
theorem no_small_multiple (l r z : ℤ) (hl : 0 < l) (hr : 0 < r) (hrl : r < l) :
    r ≠ l*z := by
  intro he
  rcases (show z ≤ 0 ∨ 1 ≤ z by omega) with hz | hz
  · nlinarith
  · nlinarith

/-- The parent x-coordinate excludes u=1 in the non-unit residue region. -/
theorem outer_u_bound (q l r u v : ℤ) (hl : 0 < l)
    (hr : 2 ≤ r) (hrl : r ≤ l-2) (hu : 1 ≤ u)
    (hx : (q*l+r)*u-l*v = 1) : 2 ≤ u := by
  by_contra hn
  have he : u = 1 := by omega
  rw [he] at hx
  have hmul : r-1 = l*(v-q) := by nlinarith
  exact no_small_multiple l (r-1) (v-q) hl (by omega) (by omega) hmul

/-- The parent y-coordinate excludes v=0 and v=-1. -/
theorem outer_v_bound (q l r u v : ℤ) (hl : 2 ≤ l)
    (hr : 2 ≤ r) (hrl : r ≤ l-2) (hv : v < 1)
    (hy : l*u+(q*l+r+l)*v = 1) : v ≤ -2 := by
  by_contra hn
  have he : v = 0 ∨ v = -1 := by omega
  rcases he with he | he
  · rw [he] at hy
    exact no_small_multiple l 1 u (by omega) (by omega) (by omega) (by nlinarith)
  · rw [he] at hy
    have hmul : r+1 = l*(u-q-1) := by nlinarith
    exact no_small_multiple l (r+1) (u-q-1) (by omega) (by omega) (by omega) hmul

/-- Works with either 2 or s+2 as the lower bound. No division is needed. -/
theorem candidate_order (N k l b h t u v J : ℤ)
    (hN : 0 ≤ N) (hk : 0 ≤ k) (hl : 0 < l)
    (hu : J ≤ u) (hv : v ≤ -J)
    (ha : N*u = k+l+l*h) (hb : N*(-v) = l*t-k)
    (hgap : 0 < J*N-k-l-l*b) :
    b < h ∧ b < t ∧ 2*b < 2*h+1 ∧ 2*b+1 < 2*t+1 := by
  have hNu : N*J ≤ N*u := mul_le_mul_of_nonneg_left hu hN
  have hNv : N*J ≤ N*(-v) := mul_le_mul_of_nonneg_left (by omega) hN
  have hh : b < h := by nlinarith
  have ht : b < t := by nlinarith
  omega

/-- AU §2, with candidate coordinate equations and the AT gap explicitly assumed. -/
theorem outer_endpoint_order (q l r h t u v uB vA b : ℤ)
    (hl : 2 ≤ l) (hr : 2 ≤ r) (hrl : r ≤ l-2)
    (hu : 1 ≤ u) (hv : v < 1)
    (hx : (q*l+r)*u-l*vA = 1) (hy : l*uB+(q*l+r+l)*v = 1)
    (hk : 0 ≤ q*l+r) (hN : 0 ≤ norm (q*l+r) l)
    (ha : norm (q*l+r) l*u = (q*l+r)+l+l*h)
    (hb : norm (q*l+r) l*(-v) = l*t-(q*l+r))
    (hgap : 0 < 2*norm (q*l+r) l-(q*l+r)-l-l*b)
    (hbn : b < norm (q*l+r) l) :
    b < h ∧ b < t ∧ 2*b < 2*h+1 ∧ 2*b+1 < 2*t+1 ∧
      2*b+1 < 2*norm (q*l+r) l := by
  have hu2 := outer_u_bound q l r u vA (by omega) hr hrl hu hx
  have hv2 := outer_v_bound q l r uB v hl hr hrl hv hy
  obtain ⟨hh, ht, hA, hB⟩ := candidate_order (norm (q*l+r) l) (q*l+r) l b h t u v 2
    hN hk (by omega) hu2 hv2 ha hb hgap
  exact ⟨hh, ht, hA, hB, by omega⟩

#print axioms unit_endpoint
#print axioms second_plus
#print axioms second_minus
#print axioms diagonal_plus
#print axioms diagonal_minus
#print axioms folded_second_plus
#print axioms folded_second_minus
#print axioms outer_collisions
#print axioms positive_fan_collisions
#print axioms negative_fan_collisions
#print axioms no_small_multiple
#print axioms outer_u_bound
#print axioms outer_v_bound
#print axioms candidate_order
#print axioms outer_endpoint_order
end R002.A3
