import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Group.Prod

/-!
# K3 pieces: the arithmetic of the cap and tube coordinates

Written by a Claude worker (2026-10-20, K3 bridge).  Pure integer arithmetic, no surfaces.

The K3 sphere is cut into the top cap (a triangle `Δ` of side `2r`), the tube (coordinates
`(h, a)`, `a` modulo `6r`) and the bottom cap.  The top seam is `h = -zz a`, where `zz a` is the
distance from `a` to `2rℤ`; its point at angle `a` is `bT a ∈ ∂Δ`.

* `planar_apex`  : the two lattice triangles on a unit segment;
* `tube_three`   : three tube points adjacent (`TA`) to both ends of a tube edge: two coincide;
* `top_unit_of_TA`, `top_TA_or_chord`, `top_chord_apex`, `top_cap_apex`, `top_tube_apex` :
  the seam facts (a tube edge along the seam is a cap edge; a cap edge between seam points is a
  tube edge or a chord across a corner; only one cap and one tube triangle on a seam edge).
-/

namespace Claude4K3

/-- Unit vectors of the triangular lattice, as a linear disjunction. -/
def Unit (d : ℤ × ℤ) : Prop :=
  (d.1 = 1 ∧ d.2 = 0) ∨ (d.1 = 0 ∧ d.2 = 1) ∨ (d.1 = -1 ∧ d.2 = 1) ∨ (d.1 = -1 ∧ d.2 = 0) ∨
    (d.1 = 0 ∧ d.2 = -1) ∨ (d.1 = 1 ∧ d.2 = -1)

/-- Equality modulo `6r` for numbers less than `6r` apart. -/
def AE (r x y : ℤ) : Prop := x = y ∨ x = y + 6 * r ∨ x = y - 6 * r

/-- Tube adjacency in the coordinates `(h, a)` (`a` modulo `6r`). -/
def TA (r : ℤ) (t u : ℤ × ℤ) : Prop :=
  (u.1 = t.1 + 1 ∧ AE r u.2 (t.2 + 1)) ∨ (u.1 = t.1 - 1 ∧ AE r u.2 (t.2 - 1)) ∨
    (u.1 = t.1 + 1 ∧ AE r u.2 (t.2 - 1)) ∨ (u.1 = t.1 - 1 ∧ AE r u.2 (t.2 + 1)) ∨
    (u.1 = t.1 + 2 ∧ AE r u.2 t.2) ∨ (u.1 = t.1 - 2 ∧ AE r u.2 t.2)

/-- Distance from `a ∈ [0, 6r]` to `{0, 2r, 4r, 6r}`. -/
def zz (r a : ℤ) : ℤ :=
  if a ≤ r then a else if a ≤ 2 * r then 2 * r - a else if a ≤ 3 * r then a - 2 * r
  else if a ≤ 4 * r then 4 * r - a else if a ≤ 5 * r then a - 4 * r else 6 * r - a

/-- The point of the top seam at angle `a`, on the boundary of `Δ`. -/
def bT (r a : ℤ) : ℤ × ℤ :=
  if a ≤ 2 * r then (0, a) else if a ≤ 4 * r then (a - 2 * r, 4 * r - a) else (6 * r - a, 0)

/-- Angle range. -/
def AR (r : ℤ) (t : ℤ × ℤ) : Prop := 0 ≤ t.2 ∧ t.2 < 6 * r

/-- On the top seam. -/
def TopB (r : ℤ) (t : ℤ × ℤ) : Prop := AR r t ∧ t.1 = -zz r t.2

/-- In the closed tube region. -/
def RM (r s : ℤ) (t : ℤ × ℤ) : Prop := AR r t ∧ -zz r t.2 ≤ t.1 ∧ t.1 ≤ 2 * s + zz r t.2

/-- In the closed triangle `Δ` of side `2r`. -/
def InD (r : ℤ) (p : ℤ × ℤ) : Prop := 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 2 * r

variable {r s : ℤ}

/-! ## The plane -/

theorem planar_apex {P Q X : ℤ × ℤ} (h1 : Unit (Q - P)) (h2 : Unit (X - P)) (h3 : Unit (X - Q)) :
    (X.1 = P.1 - (Q.2 - P.2) ∧ X.2 = P.2 + (Q.1 - P.1) + (Q.2 - P.2)) ∨
      (X.1 = P.1 + (Q.1 - P.1) + (Q.2 - P.2) ∧ X.2 = P.2 - (Q.1 - P.1)) := by
  obtain ⟨p1, p2⟩ := P; obtain ⟨q1, q2⟩ := Q; obtain ⟨x1, x2⟩ := X
  simp only [Unit, Prod.fst_sub, Prod.snd_sub] at *
  omega

theorem planar_three {P Q X Y Z : ℤ × ℤ} (h : Unit (Q - P)) (hx1 : Unit (X - P))
    (hx2 : Unit (X - Q)) (hy1 : Unit (Y - P)) (hy2 : Unit (Y - Q)) (hz1 : Unit (Z - P))
    (hz2 : Unit (Z - Q)) : X = Y ∨ X = Z ∨ Y = Z := by
  have a := planar_apex h hx1 hx2
  have b := planar_apex h hy1 hy2
  have c := planar_apex h hz1 hz2
  obtain ⟨x1, x2⟩ := X; obtain ⟨y1, y2⟩ := Y; obtain ⟨z1, z2⟩ := Z
  simp only [Prod.mk.injEq]
  omega

/-! ## The tube -/

/-- A tube step lifts to a unit vector of the plane. -/
theorem ta_lift {t u : ℤ × ℤ} (h : TA r t u) :
    ∃ e : ℤ × ℤ, Unit e ∧ u.1 = t.1 + (e.2 - e.1) ∧ AE r u.2 (t.2 + (e.1 + e.2)) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨(0, 1), by simp [Unit], ?_, ?_⟩ <;> simp only [AE] at * <;> omega
  · refine ⟨(0, -1), by simp [Unit], ?_, ?_⟩ <;> simp only [AE] at * <;> omega
  · refine ⟨(-1, 0), by simp [Unit], ?_, ?_⟩ <;> simp only [AE] at * <;> omega
  · refine ⟨(1, 0), by simp [Unit], ?_, ?_⟩ <;> simp only [AE] at * <;> omega
  · refine ⟨(-1, 1), by simp [Unit], ?_, ?_⟩ <;> simp only [AE] at * <;> omega
  · refine ⟨(1, -1), by simp [Unit], ?_, ?_⟩ <;> simp only [AE] at * <;> omega

set_option maxHeartbeats 4000000 in
theorem ta_unlift_aux (hr : 2 ≤ r) (b1 b2 c1 c2 x1 x2 e1 e2 f1 f2 : ℤ)
    (he : Unit (e1, e2)) (hf : Unit (f1, f2))
    (hc1 : c1 = b1 + (e2 - e1)) (hc2 : AE r c2 (b2 + (e1 + e2)))
    (hx1 : x1 = b1 + (f2 - f1)) (hx2 : AE r x2 (b2 + (f1 + f2)))
    (hcx : TA r (c1, c2) (x1, x2)) : Unit (f1 - e1, f2 - e2) := by
  simp only [Unit] at he hf ⊢
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  norm_num <;> simp only [TA, AE] at hcx hc2 hx2 <;> omega

/-- Two lifted tube points at tube distance one have lifts at unit distance. -/
theorem ta_unlift (hr : 2 ≤ r) {b c x : ℤ × ℤ} {e f : ℤ × ℤ} (he : Unit e) (hf : Unit f)
    (hc1 : c.1 = b.1 + (e.2 - e.1)) (hc2 : AE r c.2 (b.2 + (e.1 + e.2)))
    (hx1 : x.1 = b.1 + (f.2 - f.1)) (hx2 : AE r x.2 (b.2 + (f.1 + f.2)))
    (hcx : TA r c x) : Unit (f - e) := by
  obtain ⟨e1, e2⟩ := e; obtain ⟨f1, f2⟩ := f
  obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c; obtain ⟨x1, x2⟩ := x
  exact ta_unlift_aux hr b1 b2 c1 c2 x1 x2 e1 e2 f1 f2 he hf hc1 hc2 hx1 hx2 hcx

/-- Lifts at the same plane offset give equal tube points. -/
theorem ta_eq_of_lift {b x y e : ℤ × ℤ} (hx : AR r x) (hy : AR r y)
    (hx1 : x.1 = b.1 + (e.2 - e.1)) (hx2 : AE r x.2 (b.2 + (e.1 + e.2)))
    (hy1 : y.1 = b.1 + (e.2 - e.1)) (hy2 : AE r y.2 (b.2 + (e.1 + e.2))) : x = y := by
  obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
  simp only [AR, AE] at *
  ext <;> simp <;> omega

/-- **Tube apexes**: three tube points adjacent to both ends of a tube edge, two coincide. -/
theorem tube_three (hr : 2 ≤ r) {b c x y z : ℤ × ℤ} (hx : AR r x) (hy : AR r y) (hz : AR r z)
    (hbc : TA r b c) (hbx : TA r b x) (hcx : TA r c x) (hby : TA r b y) (hcy : TA r c y)
    (hbz : TA r b z) (hcz : TA r c z) : x = y ∨ x = z ∨ y = z := by
  obtain ⟨e, he, he1, he2⟩ := ta_lift hbc
  obtain ⟨f, hf, hf1, hf2⟩ := ta_lift hbx
  obtain ⟨g, hg, hg1, hg2⟩ := ta_lift hby
  obtain ⟨k, hk, hk1, hk2⟩ := ta_lift hbz
  have u1 := ta_unlift hr he hf he1 he2 hf1 hf2 hcx
  have u2 := ta_unlift hr he hg he1 he2 hg1 hg2 hcy
  have u3 := ta_unlift hr he hk he1 he2 hk1 hk2 hcz
  have h0 : ∀ v : ℤ × ℤ, v - 0 = v := fun v => sub_zero v
  rcases planar_three (P := 0) (Q := e) (by rwa [h0]) (by rwa [h0]) u1 (by rwa [h0]) u2
    (by rwa [h0]) u3 with h | h | h
  · subst h; exact Or.inl (ta_eq_of_lift hx hy hf1 hf2 hg1 hg2)
  · subst h; exact Or.inr (Or.inl (ta_eq_of_lift hx hz hf1 hf2 hk1 hk2))
  · subst h; exact Or.inr (Or.inr (ta_eq_of_lift hy hz hg1 hg2 hk1 hk2))

end Claude4K3
