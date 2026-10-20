import Formal.ClaudeCorRays

/-!
# Second paper (R002 第2弾), §5.1: closed family conditions on integer affine rays

For every catalogue family with a closed iff condition in §5.1 of `paper-lines-v2.md` we state
the condition as a Lean predicate on the (natural-number) family parameters and prove that
along every integer affine ray the condition is eventually periodic.

| family | domain | positive iff (§5.1) | Lean |
|---|---|---|---|
| K3(r,s)    | r,s ≥ 2        | s ≡ ±1 (mod r)                              | `K3Pos`  |
| E10(p,r,s) | p,s ≥ 1, r ≥ 2 | p ≡ d ± 1 (mod 2r+s) for some d ∈ {0,r,r+s} | `E10Pos` |
| B2(p,r)    | p,r ≥ 1        | p = 1 or abs(p - r) = 1                     | `B2Pos`  |
| C1(a,b)    | a,b ≥ 1        | not (b ≥ 2)   (negative iff b ≥ 2)          | `C1Pos`  |
| A1(r)      | r ≥ 1          | never                                       | `A1Pos`  |
| A2(p)      | p ≥ 1          | p = 1                                       | `A2Pos`  |
| A3(k,l)    | k > l > 0      | `ClaudeChallenge.criterion k l`             | `ClaudeCor.criterion_ray` |

This file is pure arithmetic: the predicates are the *statements* of the family conditions,
not graphs.  The link "predicate ↔ a literal gSW path exists in the family's dual graph" is the
(informal, or for A3 formal) family classification and is not used here.

For each family `X` we prove
* `X_ray`     : if the ray eventually stays in the domain, `XPos` is eventually periodic;
* `X_ray_all` : for *every* integer affine ray, `XDom ∧ XPos` is eventually periodic
                (no domain hypothesis);
* refinements: when the relevant modulus grows (K3: `r`, E10: `2r+s`) and for B2, C1, A1, A2
  on every ray, the predicate is eventually *constant* (period 1), `EvConst`.

Concrete rays of §6.3 (both via the arithmetic of the closed condition):
* `k3_example`  : `K3Pos (43+2t) (170+5t) ↔ t = 40 ∨ t = 42` for all `t`;
* `e10_example` : `E10Pos (200+5t) (17+2t) (23+t) ↔ t ∈ {3,10,17,34}` for all `t`.

Ray parameters are `(a * t + b).toNat` with integer `a, b`, as in `ClaudeCor.criterion_ray`.
-/

namespace Claude2

open ClaudeCor

/-! ## Eventually constant predicates -/

/-- `p` is eventually constant: eventually true or eventually false. -/
def EvConst (p : ℕ → Prop) : Prop := Ev p ∨ Ev (fun t => ¬ p t)

theorem EvConst.evPer {p : ℕ → Prop} (h : EvConst p) : EvPer p :=
  h.elim EvPer.of_ev EvPer.of_ev_not

theorem EvConst.const (c : Prop) : EvConst (fun _ => c) := by
  by_cases hc : c
  · exact Or.inl (Ev.of_forall fun _ => hc)
  · exact Or.inr (Ev.of_forall fun _ => hc)

theorem EvConst.congr {p q : ℕ → Prop} (hq : EvConst q) (h : Ev (fun t => p t ↔ q t)) :
    EvConst p := by
  rcases hq with hq | hq
  · exact Or.inl ((hq.and h).mono fun _ ⟨a, b⟩ => b.2 a)
  · exact Or.inr ((hq.and h).mono fun _ ⟨a, b⟩ hp => a (b.1 hp))

theorem EvConst.not {p : ℕ → Prop} (hp : EvConst p) : EvConst (fun t => ¬ p t) := by
  rcases hp with hp | hp
  · exact Or.inr (hp.mono fun _ h h' => h' h)
  · exact Or.inl hp

theorem EvConst.and {p q : ℕ → Prop} (hp : EvConst p) (hq : EvConst q) :
    EvConst (fun t => p t ∧ q t) := by
  rcases hp with hp | hp
  · rcases hq with hq | hq
    · exact Or.inl (hp.and hq)
    · exact Or.inr (hq.mono fun _ h h' => h h'.2)
  · exact Or.inr (hp.mono fun _ h h' => h h'.1)

theorem EvConst.or {p q : ℕ → Prop} (hp : EvConst p) (hq : EvConst q) :
    EvConst (fun t => p t ∨ q t) :=
  (hp.not.and hq.not).not.congr (Ev.of_forall fun _ => by tauto)

theorem evConst_pos {f : ℕ → ℤ} (hf : IsAff f) : EvConst (fun t => 0 < f t) := by
  rcases ev_sign hf with h | h | h
  · exact Or.inl h
  · exact Or.inr (h.mono fun t ht => by show ¬ 0 < f t; rw [ht]; exact lt_irrefl 0)
  · exact Or.inr (h.mono fun _ ht => not_lt.2 ht.le)

theorem evConst_lt {f g : ℕ → ℤ} (hf : IsAff f) (hg : IsAff g) :
    EvConst (fun t => f t < g t) :=
  (evConst_pos (hg.sub hf)).congr (Ev.of_forall fun _ => sub_pos.symm)

theorem evConst_le {f g : ℕ → ℤ} (hf : IsAff f) (hg : IsAff g) :
    EvConst (fun t => f t ≤ g t) :=
  (evConst_lt hf (hg.add (IsAff.const 1))).congr
    (Ev.of_forall fun _ => Int.lt_add_one_iff.symm)

theorem evConst_eq {f g : ℕ → ℤ} (hf : IsAff f) (hg : IsAff g) :
    EvConst (fun t => f t = g t) :=
  ((evConst_le hf hg).and (evConst_le hg hf)).congr (Ev.of_forall fun _ => le_antisymm_iff)

/-- Divisibility by a *nonconstant* affine modulus is eventually constant. -/
theorem evConst_dvd {α : ℤ} (hα : α ≠ 0) (β : ℤ) {B : ℕ → ℤ} (hB : IsAff B) :
    EvConst (fun t : ℕ => α * t + β ∣ B t) := by
  obtain ⟨γ, δ, hB'⟩ := hB
  set D := α * δ - γ * β with hDdef
  have hD : ∀ t : ℕ, α * B t - γ * (α * t + β) = D := fun t => by rw [hB']; ring
  by_cases hD0 : D = 0
  · refine (EvConst.const (α ∣ γ)).congr ((ev_large hα β 0).mono fun t ht => ?_)
    have hAt : α * (t : ℤ) + β ≠ 0 := by
      intro h; rw [h, abs_zero] at ht; exact lt_irrefl 0 ht
    have hrel : α * B t = γ * (α * t + β) := by have := hD t; rw [hD0] at this; linarith
    constructor
    · rintro ⟨s, hs⟩
      refine ⟨s, ?_⟩
      rw [hs] at hrel
      have : (α * t + β) * (α * s) = (α * t + β) * γ := by linear_combination hrel
      exact (mul_left_cancel₀ hAt this).symm
    · rintro ⟨q, hq⟩
      refine ⟨q, ?_⟩
      rw [hq] at hrel
      have : α * B t = α * ((α * t + β) * q) := by rw [hrel]; ring
      exact mul_left_cancel₀ hα this
  · refine Or.inr ((ev_large hα β |D|).mono fun t ht hdvd => ?_)
    have h1 : α * t + β ∣ D := by
      rw [← hD t]
      exact dvd_sub (dvd_mul_of_dvd_right hdvd α) (dvd_mul_left _ γ)
    have h2 := Int.le_of_dvd (abs_pos.2 hD0) ((abs_dvd_abs _ _).2 h1)
    linarith

theorem evConst_dvd_of {A B : ℕ → ℤ} {α β : ℤ} (hα : α ≠ 0) (hA : ∀ t : ℕ, A t = α * t + β)
    (hB : IsAff B) : EvConst (fun t => A t ∣ B t) :=
  (evConst_dvd hα β hB).congr (Ev.of_forall fun t => by rw [hA t])

/-! ## Domains -/

/-- If the domain predicate is eventually constant and, when it eventually holds, `P` is
eventually periodic, then `D ∧ P` is eventually periodic. -/
theorem evPer_dom_and {D P : ℕ → Prop} (hD : EvConst D) (hP : Ev D → EvPer P) :
    EvPer (fun t => D t ∧ P t) := by
  rcases hD with hD | hD
  · exact (hP hD).congr (hD.mono fun _ h => and_iff_right h)
  · exact EvPer.of_ev_not (hD.mono fun _ h h' => h h'.1)

theorem evConst_dom_and {D P : ℕ → Prop} (hD : EvConst D) (hP : Ev D → EvConst P) :
    EvConst (fun t => D t ∧ P t) := by
  rcases hD with hD | hD
  · exact (hP hD).congr (hD.mono fun _ h => and_iff_right h)
  · exact Or.inr (hD.mono fun _ h h' => h h'.1)

/-- The natural-number parameter `(a t + b).toNat`, cast back, is `a t + b` once it is `≥ 0`. -/
theorem cast_toNat {x : ℤ} (h : 0 ≤ x) : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg h

/-- `c ≤ (a t + b).toNat` is eventually constant along a ray (for `c ≥ 1`). -/
theorem evConst_ge_toNat (c : ℕ) (hc : 1 ≤ c) (a b : ℤ) :
    EvConst (fun t : ℕ => c ≤ (a * t + b).toNat) :=
  (evConst_le (IsAff.const (c : ℤ)) (IsAff.lin a b)).congr (Ev.of_forall fun _ => by omega)

/-! ## K3(r,s) -/

/-- Domain of the K3 condition in §5.1. -/
def K3Dom (r s : ℕ) : Prop := 2 ≤ r ∧ 2 ≤ s

/-- K3(r,s): a literal path exists iff `s ≡ ±1 (mod r)` (§5.1, for `r, s ≥ 2`). -/
def K3Pos (r s : ℕ) : Prop := (s : ℤ) ≡ 1 [ZMOD r] ∨ (s : ℤ) ≡ -1 [ZMOD r]

/-- Integer divisibility form of `K3Pos`. -/
def K3Z (R S : ℤ) : Prop := R ∣ S - 1 ∨ R ∣ S + 1

theorem k3Pos_iff (r s : ℕ) : K3Pos r s ↔ K3Z r s := by
  unfold K3Pos K3Z
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd, show (1 : ℤ) - s = -((s : ℤ) - 1) by ring,
    show (-1 : ℤ) - s = -((s : ℤ) + 1) by ring, dvd_neg, dvd_neg]

theorem k3Pos_toNat {R S : ℤ} (hR : 0 ≤ R) (hS : 0 ≤ S) : K3Pos R.toNat S.toNat ↔ K3Z R S := by
  rw [k3Pos_iff, cast_toNat hR, cast_toNat hS]

theorem evPer_k3Z {R S : ℕ → ℤ} (hR : IsAff R) (hS : IsAff S) :
    EvPer (fun t => K3Z (R t) (S t)) :=
  EvPer.or (evPer_dvd hR (hS.sub (IsAff.const 1))) (evPer_dvd hR (hS.add (IsAff.const 1)))

/-- **K3 on rays.** Along an integer affine ray `r = a t + b`, `s = c t + d` that eventually
stays in the domain `r, s ≥ 2`, the K3 condition is eventually periodic. -/
theorem k3_ray (a b c d : ℤ) (h : Ev (fun t : ℕ => 2 ≤ a * t + b ∧ 2 ≤ c * t + d)) :
    EvPer (fun t : ℕ => K3Pos (a * t + b).toNat (c * t + d).toNat) :=
  (evPer_k3Z (IsAff.lin a b) (IsAff.lin c d)).congr
    (h.mono fun _ ht => k3Pos_toNat (by linarith [ht.1]) (by linarith [ht.2]))

/-- **K3 on all rays.** For every integer affine ray, "in the K3 domain and positive" is
eventually periodic. -/
theorem k3_ray_all (a b c d : ℤ) :
    EvPer (fun t : ℕ => K3Dom (a * t + b).toNat (c * t + d).toNat ∧
      K3Pos (a * t + b).toNat (c * t + d).toNat) :=
  evPer_dom_and ((evConst_ge_toNat 2 (by norm_num) a b).and (evConst_ge_toNat 2 (by norm_num) c d))
    fun hD => k3_ray a b c d (hD.mono fun _ h => by
      obtain ⟨h1, h2⟩ := h; exact ⟨by omega, by omega⟩)

/-- **K3, growing modulus.** If `r` is nonconstant along the ray (`a ≠ 0`), the K3 condition is
eventually constant (period 1). -/
theorem k3_ray_const (a b c d : ℤ) (ha : a ≠ 0)
    (h : Ev (fun t : ℕ => 2 ≤ a * t + b ∧ 2 ≤ c * t + d)) :
    EvConst (fun t : ℕ => K3Pos (a * t + b).toNat (c * t + d).toNat) :=
  ((evConst_dvd ha b ((IsAff.lin c d).sub (IsAff.const 1))).or
    (evConst_dvd ha b ((IsAff.lin c d).add (IsAff.const 1)))).congr
    (h.mono fun _ ht => k3Pos_toNat (by linarith [ht.1]) (by linarith [ht.2]))

/-! ## E10(p,r,s) -/

/-- Domain of the E10 condition in §5.1. -/
def E10Dom (p r s : ℕ) : Prop := 1 ≤ p ∧ 2 ≤ r ∧ 1 ≤ s

/-- E10(p,r,s): with `m = 2r + s`, a literal path exists iff `p ≡ d ± 1 (mod m)` for some
`d ∈ {0, r, r + s}` (§5.1, for `p, s ≥ 1`, `r ≥ 2`). -/
def E10Pos (p r s : ℕ) : Prop :=
  ∃ d : ℤ, (d = 0 ∨ d = r ∨ d = r + s) ∧
    ((p : ℤ) ≡ d + 1 [ZMOD 2 * r + s] ∨ (p : ℤ) ≡ d - 1 [ZMOD 2 * r + s])

/-- Integer divisibility form of `E10Pos`: six affine divisibilities by `M = 2R + S`. -/
def E10Z (P R S : ℤ) : Prop :=
  (2 * R + S ∣ 0 + 1 - P ∨ 2 * R + S ∣ 0 - 1 - P) ∨
    (2 * R + S ∣ R + 1 - P ∨ 2 * R + S ∣ R - 1 - P) ∨
    (2 * R + S ∣ R + S + 1 - P ∨ 2 * R + S ∣ R + S - 1 - P)

theorem exists_three {x y z : ℤ} {Q : ℤ → Prop} :
    (∃ d : ℤ, (d = x ∨ d = y ∨ d = z) ∧ Q d) ↔ Q x ∨ Q y ∨ Q z := by
  constructor
  · rintro ⟨d, hd | hd | hd, h⟩ <;> subst hd <;> simp [h]
  · rintro (h | h | h)
    · exact ⟨x, Or.inl rfl, h⟩
    · exact ⟨y, Or.inr (Or.inl rfl), h⟩
    · exact ⟨z, Or.inr (Or.inr rfl), h⟩

theorem e10Pos_iff (p r s : ℕ) : E10Pos p r s ↔ E10Z p r s := by
  unfold E10Pos E10Z
  rw [exists_three]
  simp only [Int.modEq_iff_dvd]

theorem e10Pos_toNat {P R S : ℤ} (hP : 0 ≤ P) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    E10Pos P.toNat R.toNat S.toNat ↔ E10Z P R S := by
  rw [e10Pos_iff, cast_toNat hP, cast_toNat hR, cast_toNat hS]

theorem evPer_e10Z {P R S : ℕ → ℤ} (hP : IsAff P) (hR : IsAff R) (hS : IsAff S) :
    EvPer (fun t => E10Z (P t) (R t) (S t)) := by
  have hM : IsAff (fun t => 2 * R t + S t) := (hR.smul 2).add hS
  have c := IsAff.const
  unfold E10Z
  refine EvPer.or (EvPer.or ?_ ?_) (EvPer.or (EvPer.or ?_ ?_) (EvPer.or ?_ ?_)) <;>
    refine evPer_dvd hM ?_
  · exact ((c 0).add (c 1)).sub hP
  · exact ((c 0).sub (c 1)).sub hP
  · exact (hR.add (c 1)).sub hP
  · exact (hR.sub (c 1)).sub hP
  · exact ((hR.add hS).add (c 1)).sub hP
  · exact ((hR.add hS).sub (c 1)).sub hP

/-- **E10 on rays.** Along an integer affine ray `p = a₁ t + b₁`, `r = a₂ t + b₂`,
`s = a₃ t + b₃` that eventually stays in the domain `p, s ≥ 1`, `r ≥ 2`, the E10 condition is
eventually periodic. -/
theorem e10_ray (a₁ b₁ a₂ b₂ a₃ b₃ : ℤ)
    (h : Ev (fun t : ℕ => 1 ≤ a₁ * t + b₁ ∧ 2 ≤ a₂ * t + b₂ ∧ 1 ≤ a₃ * t + b₃)) :
    EvPer (fun t : ℕ => E10Pos (a₁ * t + b₁).toNat (a₂ * t + b₂).toNat (a₃ * t + b₃).toNat) :=
  (evPer_e10Z (IsAff.lin a₁ b₁) (IsAff.lin a₂ b₂) (IsAff.lin a₃ b₃)).congr
    (h.mono fun _ ht => e10Pos_toNat (by linarith [ht.1]) (by linarith [ht.2.1])
      (by linarith [ht.2.2]))

/-- **E10 on all rays.** -/
theorem e10_ray_all (a₁ b₁ a₂ b₂ a₃ b₃ : ℤ) :
    EvPer (fun t : ℕ =>
      E10Dom (a₁ * t + b₁).toNat (a₂ * t + b₂).toNat (a₃ * t + b₃).toNat ∧
      E10Pos (a₁ * t + b₁).toNat (a₂ * t + b₂).toNat (a₃ * t + b₃).toNat) :=
  evPer_dom_and ((evConst_ge_toNat 1 le_rfl a₁ b₁).and ((evConst_ge_toNat 2 (by norm_num) a₂ b₂).and
      (evConst_ge_toNat 1 le_rfl a₃ b₃)))
    fun hD => e10_ray a₁ b₁ a₂ b₂ a₃ b₃ (hD.mono fun _ h => by
      obtain ⟨h1, h2, h3⟩ := h; exact ⟨by omega, by omega, by omega⟩)

/-- **E10, growing modulus.** If `m = 2r + s` is nonconstant along the ray (`2a₂ + a₃ ≠ 0`),
the E10 condition is eventually constant (period 1). -/
theorem e10_ray_const (a₁ b₁ a₂ b₂ a₃ b₃ : ℤ) (hm : 2 * a₂ + a₃ ≠ 0)
    (h : Ev (fun t : ℕ => 1 ≤ a₁ * t + b₁ ∧ 2 ≤ a₂ * t + b₂ ∧ 1 ≤ a₃ * t + b₃)) :
    EvConst (fun t : ℕ =>
      E10Pos (a₁ * t + b₁).toNat (a₂ * t + b₂).toNat (a₃ * t + b₃).toNat) := by
  have hP := IsAff.lin a₁ b₁
  have hR := IsAff.lin a₂ b₂
  have hS := IsAff.lin a₃ b₃
  have c := IsAff.const
  have key : EvConst (fun t : ℕ => E10Z (a₁ * t + b₁) (a₂ * t + b₂) (a₃ * t + b₃)) := by
    have hMeq : ∀ t : ℕ, 2 * (a₂ * t + b₂) + (a₃ * t + b₃) = (2 * a₂ + a₃) * t + (2 * b₂ + b₃) :=
      fun t => by ring
    have D : ∀ {B : ℕ → ℤ}, IsAff B →
        EvConst (fun t : ℕ => 2 * (a₂ * (t : ℤ) + b₂) + (a₃ * t + b₃) ∣ B t) :=
      fun hB => evConst_dvd_of hm hMeq hB
    unfold E10Z
    exact (D (((c 0).add (c 1)).sub hP)).or (D (((c 0).sub (c 1)).sub hP)) |>.or
      (((D ((hR.add (c 1)).sub hP)).or (D ((hR.sub (c 1)).sub hP))).or
        ((D (((hR.add hS).add (c 1)).sub hP)).or (D (((hR.add hS).sub (c 1)).sub hP))))
  exact key.congr (h.mono fun _ ht => e10Pos_toNat (by linarith [ht.1]) (by linarith [ht.2.1])
    (by linarith [ht.2.2]))

/-! ## B2(p,r), C1(a,b), A1(r), A2(p): eventually constant on every ray -/

/-- Domain of B2 in §5.1. -/
def B2Dom (p r : ℕ) : Prop := 1 ≤ p ∧ 1 ≤ r

/-- B2(p,r): a literal path exists iff `p = 1` or `|p - r| = 1` (§5.1, `p, r ≥ 1`). -/
def B2Pos (p r : ℕ) : Prop := p = 1 ∨ |(p : ℤ) - r| = 1

/-- Domain of C1 in §5.1. -/
def C1Dom (a b : ℕ) : Prop := 1 ≤ a ∧ 1 ≤ b

/-- C1(a,b): negative iff `b ≥ 2` (§5.1, `a, b ≥ 1`). -/
def C1Pos (_a b : ℕ) : Prop := ¬ 2 ≤ b

/-- Domain of A1 in §5.1. -/
def A1Dom (r : ℕ) : Prop := 1 ≤ r

/-- A1(r) = GC(r,0)[C20]: always negative (§5.1, `r ≥ 1`). -/
def A1Pos (_r : ℕ) : Prop := False

/-- Domain of A2 in §5.1. -/
def A2Dom (p : ℕ) : Prop := 1 ≤ p

/-- A2(p) = GC(p,p)[C20]: positive iff `p = 1` (§5.1, `p ≥ 1`). -/
def A2Pos (p : ℕ) : Prop := p = 1

/-- **B2 on rays**: eventually constant once the ray stays in the domain. -/
theorem b2_ray (a b c d : ℤ) (h : Ev (fun t : ℕ => 1 ≤ a * t + b ∧ 1 ≤ c * t + d)) :
    EvConst (fun t : ℕ => B2Pos (a * t + b).toNat (c * t + d).toNat) := by
  have hP := IsAff.lin a b
  have hR := IsAff.lin c d
  refine ((evConst_eq hP (IsAff.const 1)).or ((evConst_eq hP (hR.add (IsAff.const 1))).or
    (evConst_eq hR (hP.add (IsAff.const 1))))).congr (h.mono fun t ht => ?_)
  obtain ⟨h1, h2⟩ := ht
  unfold B2Pos
  rw [cast_toNat (by linarith : (0 : ℤ) ≤ a * t + b), cast_toNat (by linarith : (0 : ℤ) ≤ c * t + d)]
  have : (a * t + b).toNat = 1 ↔ a * (t : ℤ) + b = 1 := by omega
  rw [this, abs_eq (by norm_num)]
  constructor <;> rintro (h | h | h) <;> first
    | exact Or.inl h | exact Or.inr (Or.inl (by linarith)) | exact Or.inr (Or.inr (by linarith))

theorem b2_ray_all (a b c d : ℤ) :
    EvConst (fun t : ℕ => B2Dom (a * t + b).toNat (c * t + d).toNat ∧
      B2Pos (a * t + b).toNat (c * t + d).toNat) :=
  evConst_dom_and ((evConst_ge_toNat 1 le_rfl a b).and (evConst_ge_toNat 1 le_rfl c d))
    fun hD => b2_ray a b c d (hD.mono fun _ h => by
      obtain ⟨h1, h2⟩ := h; exact ⟨by omega, by omega⟩)

/-- **C1 on rays**: eventually constant (no domain hypothesis needed for the predicate). -/
theorem c1_ray (a b c d : ℤ) :
    EvConst (fun t : ℕ => C1Pos (a * t + b).toNat (c * t + d).toNat) :=
  (evConst_ge_toNat 2 (by norm_num) c d).not

theorem c1_ray_all (a b c d : ℤ) :
    EvConst (fun t : ℕ => C1Dom (a * t + b).toNat (c * t + d).toNat ∧
      C1Pos (a * t + b).toNat (c * t + d).toNat) :=
  ((evConst_ge_toNat 1 le_rfl a b).and (evConst_ge_toNat 1 le_rfl c d)).and (c1_ray a b c d)

/-- **A1 on rays**: constantly negative. -/
theorem a1_ray (a b : ℤ) : EvConst (fun t : ℕ => A1Pos (a * t + b).toNat) :=
  EvConst.const False

theorem a1_ray_all (a b : ℤ) :
    EvConst (fun t : ℕ => A1Dom (a * t + b).toNat ∧ A1Pos (a * t + b).toNat) :=
  (evConst_ge_toNat 1 le_rfl a b).and (a1_ray a b)

/-- **A2 on rays**: eventually constant. -/
theorem a2_ray (a b : ℤ) : EvConst (fun t : ℕ => A2Pos (a * t + b).toNat) :=
  ((evConst_ge_toNat 1 le_rfl a b).and (evConst_ge_toNat 2 (by norm_num) a b).not).congr
    (Ev.of_forall fun _ => by unfold A2Pos; omega)

theorem a2_ray_all (a b : ℤ) :
    EvConst (fun t : ℕ => A2Dom (a * t + b).toNat ∧ A2Pos (a * t + b).toNat) :=
  (evConst_ge_toNat 1 le_rfl a b).and (a2_ray a b)

/-- B2, C1, A1, A2 are in particular eventually periodic on every ray. -/
theorem b2_c1_a1_a2_evPer (a b c d : ℤ) :
    EvPer (fun t : ℕ => B2Dom (a * t + b).toNat (c * t + d).toNat ∧
      B2Pos (a * t + b).toNat (c * t + d).toNat) ∧
    EvPer (fun t : ℕ => C1Dom (a * t + b).toNat (c * t + d).toNat ∧
      C1Pos (a * t + b).toNat (c * t + d).toNat) ∧
    EvPer (fun t : ℕ => A1Dom (a * t + b).toNat ∧ A1Pos (a * t + b).toNat) ∧
    EvPer (fun t : ℕ => A2Dom (a * t + b).toNat ∧ A2Pos (a * t + b).toNat) :=
  ⟨(b2_ray_all a b c d).evPer, (c1_ray_all a b c d).evPer, (a1_ray_all a b).evPer,
    (a2_ray_all a b).evPer⟩

/-- A3, for the table: `ClaudeCor.criterion_ray` (first paper, Corollary 4). -/
theorem a3_ray (a b c d : ℤ) (h : Ev (fun t : ℕ => 0 < c * t + d ∧ c * t + d < a * t + b)) :
    EvPer (fun t : ℕ => ClaudeChallenge.criterion (a * t + b).toNat (c * t + d).toNat) :=
  criterion_ray a b c d h

end Claude2

#print axioms Claude2.k3_ray
#print axioms Claude2.k3_ray_all
#print axioms Claude2.k3_ray_const
#print axioms Claude2.e10_ray
#print axioms Claude2.e10_ray_all
#print axioms Claude2.e10_ray_const
#print axioms Claude2.b2_ray_all
#print axioms Claude2.c1_ray_all
#print axioms Claude2.a1_ray_all
#print axioms Claude2.a2_ray_all
#print axioms Claude2.b2_c1_a1_a2_evPer
#print axioms Claude2.a3_ray
