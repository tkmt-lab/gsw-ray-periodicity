import Formal.ClaudeBeltVertex

/-!
# Belt case of A3, part 2: the developed belt and its caps

Written by a Claude worker (2026-10-19), following the verifier's belt argument
(`.worktrees/verify/studies/R004/a3-belt-proof.md`) in mirrored coordinates.

Plane coordinates are those of the challenge charts: `z=(k,l)`, `w=rot z=(-l,k+l)`.
Write `α=a k l`, `β=b k l` (coefficients of `z` and `w`, times `T=norm k l`).
The ten belt faces of the challenge icosahedron are developed as

* `low i` : face `[U_i,L_i,U_(i+1)]`, plane triangle `iw, iw+z, (i+1)w`;
* `up i`  : face `[U_(i+1),L_i,L_(i+1)]`, plane triangle `(i+1)w, iw+z, (i+1)w+z`;

(`U_i` is label `1+(i mod 5)`, `L_i` is label `6+(i mod 5)`), and the caps as

* `top i` : face `[0,U_i,U_(i+1)]`, attached to `low i` along `U_iU_(i+1)`;
* `bot i` : face `[11,L_(i+1),L_i]`, attached to `up i` along `L_iL_(i+1)`.

A lattice point is *in* a region when its chart point is a strict interior point.
Main results: regions are unique, every point strictly inside the band lies in a band
region, and a unit step out of a band region lands in the same region or in one of
its three neighbors, which gives an edge of `ClaudeChallenge.gcGraph`.
-/

namespace ClaudeBelt
open R002 R002.Icosahedron R002.GCPrimitive R002.GCPrimitiveSurface R002.GCChallengeBridge

variable {k l : ℤ}

inductive Kind | low | up | top | bot
  deriving DecidableEq

structure Reg where
  kind : Kind
  idx : ℤ
  deriving DecidableEq

def r5 (i : ℤ) : Fin 5 := ⟨(i % 5).toNat, by omega⟩

theorem r5_add_one (i : ℤ) : r5 (i+1)=r5 i+1 := by
  ext; simp only [r5,Fin.val_add]; omega

def kindFace : Kind → Fin 5 → Fin 20
  | .low => ![1,5,9,13,17]
  | .up => ![2,6,10,14,18]
  | .top => ![0,4,8,12,16]
  | .bot => ![3,7,11,15,19]

def Reg.face (R : Reg) : Fin 20 := kindFace R.kind (r5 R.idx)

/-- Plane-to-chart maps (orientation preserving lattice isometries). -/
def chart (k l : ℤ) : Reg → Lattice → Lattice
  | ⟨.low,i⟩, p => (p.1+i*l,p.2-i*(k+l))
  | ⟨.up,i⟩, p => ClaudeChallenge.rot (p.1+(i+1)*l,p.2-(i+1)*(k+l))
  | ⟨.top,i⟩, p => ClaudeChallenge.rot (p.1+i*l,p.2-i*(k+l))+(k,l)
  | ⟨.bot,i⟩, p => ClaudeChallenge.rot (-(i*l)+2*k-p.1,i*(k+l)+2*l-p.2)

def InR (k l : ℤ) (R : Reg) (p : Lattice) : Prop := Interior k l (chart k l R p)

def IsBand (R : Reg) : Prop := R.kind=.low ∨ R.kind=.up

/-! ## Slices of the charts -/

theorem in_low (i : ℤ) (p : Lattice) : InR k l ⟨.low,i⟩ p ↔
    0<a k l p ∧ i*norm k l<b k l p ∧ a k l p+b k l p<(i+1)*norm k l := by
  simp only [InR,chart,Interior,a,b,c,norm]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> refine ⟨?_,?_,?_⟩ <;> nlinarith

theorem in_up (i : ℤ) (p : Lattice) : InR k l ⟨.up,i⟩ p ↔
    b k l p<(i+1)*norm k l ∧ (i+1)*norm k l<a k l p+b k l p ∧ a k l p<norm k l := by
  simp only [InR,chart,Interior,a,b,c,norm,ClaudeChallenge.rot]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> refine ⟨?_,?_,?_⟩ <;> nlinarith

theorem in_top (i : ℤ) (p : Lattice) : InR k l ⟨.top,i⟩ p ↔
    b k l p<(i+1)*norm k l ∧ i*norm k l<a k l p+b k l p ∧ a k l p<0 := by
  simp only [InR,chart,Interior,a,b,c,norm,ClaudeChallenge.rot,Prod.fst_add,Prod.snd_add]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> refine ⟨?_,?_,?_⟩ <;> nlinarith

theorem in_bot (i : ℤ) (p : Lattice) : InR k l ⟨.bot,i⟩ p ↔
    i*norm k l<b k l p ∧ a k l p+b k l p<(i+2)*norm k l ∧ norm k l<a k l p := by
  simp only [InR,chart,Interior,a,b,c,norm,ClaudeChallenge.rot]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> refine ⟨?_,?_,?_⟩ <;> nlinarith

/-! ## Uniqueness of regions -/

def slots (R : Reg) : ℤ × ℤ × ℤ :=
  match R.kind with
  | .low => (0,R.idx,R.idx)
  | .up => (0,R.idx,R.idx+1)
  | .top => (-1,R.idx,R.idx)
  | .bot => (1,R.idx,R.idx+1)

def InSlots (k l : ℤ) (s : ℤ × ℤ × ℤ) (p : Lattice) : Prop :=
  s.1*norm k l<a k l p ∧ a k l p<(s.1+1)*norm k l ∧
  s.2.1*norm k l<b k l p ∧ b k l p<(s.2.1+1)*norm k l ∧
  s.2.2*norm k l<a k l p+b k l p ∧ a k l p+b k l p<(s.2.2+1)*norm k l

theorem in_slots (hk : 0<k) (hl : 0<l) (R : Reg) (p : Lattice) (h : InR k l R p) :
    InSlots k l (slots R) p := by
  have hT := norm_pos k l hk hl.le
  rcases R with ⟨_|_|_|_,i⟩
  · obtain ⟨h1,h2,h3⟩ := (in_low i p).mp h
    simp only [InSlots,slots]; refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith
  · obtain ⟨h1,h2,h3⟩ := (in_up i p).mp h
    simp only [InSlots,slots]; refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith
  · obtain ⟨h1,h2,h3⟩ := (in_top i p).mp h
    simp only [InSlots,slots]; refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith
  · obtain ⟨h1,h2,h3⟩ := (in_bot i p).mp h
    simp only [InSlots,slots]; refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith

theorem slot_unique {T x i j : ℤ} (hT : 0<T) (h1 : i*T<x) (h2 : x<(i+1)*T)
    (h3 : j*T<x) (h4 : x<(j+1)*T) : i=j := by
  have : i<j+1 := lt_of_mul_lt_mul_right (h1.trans h4) hT.le
  have : j < i+1 := lt_of_mul_lt_mul_right (h3.trans h2) hT.le
  omega

theorem inSlots_unique (hk : 0<k) (hl : 0<l) (s s' : ℤ × ℤ × ℤ) (p : Lattice)
    (h : InSlots k l s p) (h' : InSlots k l s' p) : s=s' := by
  have hT := norm_pos k l hk hl.le
  obtain ⟨a1,a2,b1,b2,c1,c2⟩ := h
  obtain ⟨a1',a2',b1',b2',c1',c2'⟩ := h'
  have e1 := slot_unique hT a1 a2 a1' a2'
  have e2 := slot_unique hT b1 b2 b1' b2'
  have e3 := slot_unique hT c1 c2 c1' c2'
  exact Prod.ext e1 (Prod.ext e2 e3)

theorem slots_injective : Function.Injective slots := by
  rintro ⟨_|_|_|_,i⟩ ⟨_|_|_|_,j⟩ h <;> simp only [slots,Prod.mk.injEq] at h <;>
    first | (obtain ⟨_,_,_⟩ := h; omega) | (congr 1; omega)

theorem region_unique (hk : 0<k) (hl : 0<l) (R R' : Reg) (p : Lattice)
    (h : InR k l R p) (h' : InR k l R' p) : R=R' :=
  slots_injective (inSlots_unique hk hl _ _ p (in_slots hk hl R p h) (in_slots hk hl R' p h'))

/-- Region interiors avoid the lines `α=0` and `α=T` through the parent vertices. -/
theorem in_alpha_ne (hk : 0<k) (hl : 0<l) (R : Reg) (p : Lattice) (h : InR k l R p) :
    a k l p≠0 ∧ a k l p≠norm k l := by
  have hT := norm_pos k l hk hl.le
  obtain ⟨a1,a2,-⟩ := in_slots hk hl R p h
  constructor
  · intro h0; rw [h0] at a1 a2
    have : (slots R).1<0 := by
      by_contra hc; push Not at hc; nlinarith
    have : -1<(slots R).1 := by
      by_contra hc; push Not at hc; nlinarith
    omega
  · intro h0; rw [h0] at a1 a2
    have : (slots R).1<1 := by
      by_contra hc; push Not at hc; nlinarith
    have : 0<(slots R).1 := by
      by_contra hc; push Not at hc; nlinarith
    omega

/-! ## Every point strictly inside the band is in a band region -/

theorem primitive_zero_line (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) (x : Lattice)
    (hb : b k l x=0) (h0 : 0<a k l x) (h1 : a k l x<norm k l) : False := by
  obtain ⟨j,rfl⟩ := primitive_line k l hk hprim x hb
  have ha : a k l (k*j,l*j)=norm k l*j := by dsimp [a,norm]; ring
  rw [ha] at h0 h1
  have hT := norm_pos k l hk hl.le
  have : 0<j := by nlinarith
  have : j<1 := by nlinarith
  omega

theorem band_exists (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) (p : Lattice)
    (h0 : 0<a k l p) (h1 : a k l p<norm k l) : ∃ R, IsBand R ∧ InR k l R p := by
  have hT := norm_pos k l hk hl.le
  set i := b k l p / norm k l
  have hi1 : i*norm k l ≤ b k l p := Int.ediv_mul_le _ hT.ne'
  have hi2 : b k l p<(i+1)*norm k l := Int.lt_ediv_add_one_mul_self _ hT
  have hne : i*norm k l≠b k l p := by
    intro he
    apply primitive_zero_line hk hl hprim (chart k l ⟨.low,i⟩ p)
    · simp only [chart,b,norm] at he ⊢; nlinarith
    · simp only [chart,a]; simp only [a] at h0; nlinarith
    · simp only [chart,a]; simp only [a] at h1; nlinarith
  rcases lt_trichotomy (a k l p+b k l p) ((i+1)*norm k l) with hs | hs | hs
  · exact ⟨⟨.low,i⟩,Or.inl rfl,(in_low i p).mpr ⟨h0,lt_of_le_of_ne hi1 hne,hs⟩⟩
  · exfalso
    let y := chart k l ⟨.up,i⟩ p
    apply primitive_zero_line hk hl hprim y
    · simp only [y,chart,b,ClaudeChallenge.rot,norm] at hs ⊢; simp only [a,b,norm] at hs; nlinarith
    · simp only [y,chart,a,ClaudeChallenge.rot]; simp only [b,norm] at hi2 ⊢; nlinarith
    · simp only [y,chart,a,ClaudeChallenge.rot]
      simp only [a,b,norm] at hi1 hne h0 hs ⊢
      have := lt_of_le_of_ne hi1 hne
      nlinarith
  · exact ⟨⟨.up,i⟩,Or.inr rfl,(in_up i p).mpr ⟨hi2,hs,h1⟩⟩

/-! ## Unit steps through charts -/

theorem chart_unit (R : Reg) (p q : Lattice) (h : GCPrimitive.Unit p q) :
    GCPrimitive.Unit (chart k l R p) (chart k l R q) := by
  obtain ⟨d,rfl⟩ := h
  rcases R with ⟨_|_|_|_,i⟩ <;> fin_cases d <;>
    first
    | (refine ⟨0,?_⟩; ext <;> (simp [chart,direction,ClaudeChallenge.rot]; try ring1); done)
    | (refine ⟨1,?_⟩; ext <;> (simp [chart,direction,ClaudeChallenge.rot]; try ring1); done)
    | (refine ⟨2,?_⟩; ext <;> (simp [chart,direction,ClaudeChallenge.rot]; try ring1); done)
    | (refine ⟨3,?_⟩; ext <;> (simp [chart,direction,ClaudeChallenge.rot]; try ring1); done)
    | (refine ⟨4,?_⟩; ext <;> (simp [chart,direction,ClaudeChallenge.rot]; try ring1); done)
    | (refine ⟨5,?_⟩; ext <;> (simp [chart,direction,ClaudeChallenge.rot]; try ring1); done)

/-! ## Neighbors of band regions -/

def nbr : Reg → Corner → Reg
  | ⟨.low,i⟩, e => if e=0 then ⟨.up,i-1⟩ else if e=1 then ⟨.up,i⟩ else ⟨.top,i⟩
  | ⟨.up,i⟩, e => if e=0 then ⟨.low,i⟩ else if e=1 then ⟨.bot,i⟩ else ⟨.low,i+1⟩
  | R, _ => R

theorem opp_frame_iff (e : Corner) (x : Lattice) :
    Interior k l (opposite k l (frame k l e x)) ↔
      (e=0 ∧ a k l x<norm k l ∧ b k l x<0 ∧ 0<a k l x+b k l x) ∨
      (e=1 ∧ b k l x<norm k l ∧ c k l x<0 ∧ 0<b k l x+c k l x) ∨
      (e=2 ∧ c k l x<norm k l ∧ a k l x<0 ∧ 0<c k l x+a k l x) := by
  rw [opposite_interior]
  have ht := turn_slices k l x
  have htt := turn_slices k l (turn k l x)
  fin_cases e <;> simp [frame,ht.1,ht.2.1,ht.2.2,htt.1,htt.2.1]

theorem nbr_in (R : Reg) (hR : IsBand R) (e : Corner) (p : Lattice)
    (h : Interior k l (opposite k l (frame k l e (chart k l R p)))) : InR k l (nbr R e) p := by
  rw [opp_frame_iff] at h
  rcases R with ⟨_|_|_|_,i⟩
  · rcases h with ⟨rfl,h1,h2,h3⟩ | ⟨rfl,h1,h2,h3⟩ | ⟨rfl,h1,h2,h3⟩
    · show InR k l ⟨.up,i-1⟩ p
      rw [in_up]; simp only [chart,a,b,c,norm] at h1 h2 h3 ⊢
      refine ⟨?_,?_,?_⟩ <;> nlinarith
    · show InR k l ⟨.up,i⟩ p
      rw [in_up]; simp only [chart,a,b,c,norm] at h1 h2 h3 ⊢
      refine ⟨?_,?_,?_⟩ <;> nlinarith
    · show InR k l ⟨.top,i⟩ p
      rw [in_top]; simp only [chart,a,b,c,norm] at h1 h2 h3 ⊢
      refine ⟨?_,?_,?_⟩ <;> nlinarith
  · rcases h with ⟨rfl,h1,h2,h3⟩ | ⟨rfl,h1,h2,h3⟩ | ⟨rfl,h1,h2,h3⟩
    · show InR k l ⟨.low,i⟩ p
      rw [in_low]; simp only [chart,a,b,c,norm,ClaudeChallenge.rot] at h1 h2 h3 ⊢
      refine ⟨?_,?_,?_⟩ <;> nlinarith
    · show InR k l ⟨.bot,i⟩ p
      rw [in_bot]; simp only [chart,a,b,c,norm,ClaudeChallenge.rot] at h1 h2 h3 ⊢
      refine ⟨?_,?_,?_⟩ <;> nlinarith
    · show InR k l ⟨.low,i+1⟩ p
      rw [in_low]; simp only [chart,a,b,c,norm,ClaudeChallenge.rot] at h1 h2 h3 ⊢
      refine ⟨?_,?_,?_⟩ <;> nlinarith
  · exact absurd hR (by simp [IsBand])
  · exact absurd hR (by simp [IsBand])

/-- The parent corners of a band chart lie on `α=0` or `α=T`. -/
theorem band_corner_alpha (R : Reg) (hR : IsBand R) (p : Lattice)
    (h : chart k l R p=(0,0) ∨ chart k l R p=A k l ∨ chart k l R p=B k l) :
    a k l p=0 ∨ a k l p=norm k l := by
  have key : ∀ x : Lattice, (x=(0,0) ∨ x=A k l ∨ x=B k l) →
      (a k l x=0 ∨ a k l x=norm k l) ∧ (c k l x=0 ∨ c k l x=norm k l) := by
    rintro x (rfl|rfl|rfl) <;> refine ⟨?_,?_⟩ <;> simp only [a,b,c,A,B,norm] <;>
      first | (left; ring1) | (right; ring1)
  obtain ⟨ha,hc⟩ := key _ h
  rcases R with ⟨_|_|_|_,i⟩
  · simp only [chart,a,norm] at ha ⊢
    rcases ha with ha | ha
    · left; linarith
    · right; linarith
  · simp only [chart,c,a,b,norm,ClaudeChallenge.rot] at hc ⊢
    rcases hc with hc | hc
    · right; linarith
    · left; linarith
  · exact absurd hR (by simp [IsBand])
  · exact absurd hR (by simp [IsBand])

/-- A unit step out of a band region stays in it or enters one of its three neighbors. -/
theorem band_step (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) (R R' : Reg) (hR : IsBand R)
    (p q : Lattice) (hp : InR k l R p) (hu : GCPrimitive.Unit p q) (hq : InR k l R' q) :
    R'=R ∨ ∃ e, R'=nbr R e := by
  rcases unit_step_covered k l hk hl _ _ hp (chart_unit R p q hu) with hc | ⟨e,he⟩
  · rcases closed_partition k l hk hl.le hprim _ hc with h | h | h | h
    · exact absurd (band_corner_alpha R hR q (Or.inl h)) (by
        have := in_alpha_ne hk hl R' q hq; tauto)
    · exact absurd (band_corner_alpha R hR q (Or.inr (Or.inl h))) (by
        have := in_alpha_ne hk hl R' q hq; tauto)
    · exact absurd (band_corner_alpha R hR q (Or.inr (Or.inr h))) (by
        have := in_alpha_ne hk hl R' q hq; tauto)
    · exact Or.inl (region_unique hk hl R' R q hq h)
  · exact Or.inr ⟨e,region_unique hk hl R' _ q hq (nbr_in R hR e q he)⟩

end ClaudeBelt
