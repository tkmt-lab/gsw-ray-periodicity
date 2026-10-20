import Formal.ClaudePosFrame
import Mathlib.Tactic.Abel

/-!
# Positive side of A3, part 2: charts of coarse triangles, steps and gluings

Written by a Claude worker (2026-10-19).

* `chart k l D r` sends the `m`-th vertex of `D` to `corner (r+m)`.
* A unit step out of a coarse triangle stays in it or enters one of its three
  edge-neighbors `nbr D e` (reusing `unit_step_covered`).
* For a labeling `L` of coarse vertices by icosahedron labels such that every triangle used
  is a face (`FaceOK`), the charts of edge-neighbors differ by a `ClaudeChallenge.Glue`.
  Consequently unit steps become `ClaudeChallenge.StepTo`.
-/

namespace ClaudePos
open R002 R002.Icosahedron R002.GCPrimitive R002.GCPrimitiveSurface R002.GCChallengeBridge
open ClaudeChallenge (rot rotN)

variable {k l : ℤ}

/-! ## Charts -/

def chartM (D : CT) (r : Fin 3) : ℕ := ((if D.up then 0 else 5)+2*r.val)%6

theorem chartM_lt (D : CT) (r : Fin 3) : chartM D r<6 := Nat.mod_lt _ (by norm_num)

def chart (k l : ℤ) (D : CT) (r : Fin 3) (x : Lattice) : Lattice :=
  rotN (chartM D r) (x-pos k l (D.vert 0))+ClaudeChallenge.corner k l r

theorem chart_vert (D : CT) (r m : Fin 3) :
    chart k l D r (pos k l (D.vert m))=ClaudeChallenge.corner k l (r+m) := by
  rcases D with ⟨_|_,i,j⟩ <;> fin_cases r <;> fin_cases m <;>
    ext <;> simp [chart,chartM,CT.vert,pos,rotN,rot,ClaudeChallenge.corner] <;> ring

theorem chart_interior (D : CT) (r : Fin 3) (x : Lattice) :
    Interior k l (chart k l D r x) ↔ InCT k l D x := by
  rcases D with ⟨_|_,i,j⟩ <;> fin_cases r <;>
    simp [Interior,InCT,chart,chartM,CT.vert,pos,rotN,rot,ClaudeChallenge.corner,a,b,c,norm] <;>
    constructor <;> rintro ⟨h1,h2,h3⟩ <;> refine ⟨?_,?_,?_⟩ <;> nlinarith

theorem chart_injective (D : CT) (r : Fin 3) : Function.Injective (chart k l D r) := by
  intro x y h
  simp only [chart] at h
  have := rotN_injective _ (add_right_cancel h)
  exact sub_left_inj.mp this

theorem chart_unit (D : CT) (r : Fin 3) (x y : Lattice) (h : GCPrimitive.Unit x y) :
    GCPrimitive.Unit (chart k l D r x) (chart k l D r y) := by
  apply unit_aff
  obtain ⟨i,rfl⟩ := h
  exact ⟨i,by abel⟩

/-! ## Neighbors -/

def nbr (D : CT) (e : Fin 3) : CT :=
  if D.up then
    (if e=0 then ⟨false,D.i,D.j-1⟩ else if e=1 then ⟨false,D.i,D.j⟩ else ⟨false,D.i-1,D.j⟩)
  else
    (if e=0 then ⟨true,D.i+1,D.j⟩ else if e=1 then ⟨true,D.i,D.j+1⟩ else ⟨true,D.i,D.j⟩)

def nbrG (D : CT) (e : Fin 3) : Fin 3 := if D.up then ![1,2,0] e else ![2,0,1] e

theorem nbr_vert (D : CT) (e : Fin 3) :
    (nbr D e).vert (nbrG D e)=D.vert (e+1) ∧ (nbr D e).vert (nbrG D e+1)=D.vert e := by
  rcases D with ⟨_|_,i,j⟩ <;> fin_cases e <;>
    simp [nbr,nbrG,CT.vert]

theorem nbr_in (D : CT) (e : Fin 3) (y : Lattice)
    (h : Interior k l (opposite k l (frame k l e (chart k l D 0 y)))) : InCT k l (nbr D e) y := by
  rw [ClaudeBelt.opp_frame_iff] at h
  rcases D with ⟨_|_,i,j⟩ <;>
    rcases h with ⟨rfl,h1,h2,h3⟩ | ⟨rfl,h1,h2,h3⟩ | ⟨rfl,h1,h2,h3⟩ <;>
    simp [nbr,InCT,chart,chartM,CT.vert,pos,rotN,rot,ClaudeChallenge.corner,a,b,c,norm] at h1 h2 h3 ⊢ <;>
    refine ⟨?_,?_,?_⟩ <;> nlinarith

/-- A unit step out of a coarse triangle stays in it or crosses one edge. -/
theorem ct_step (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) (D D' : CT) (x y : Lattice)
    (hx : InCT k l D x) (hu : GCPrimitive.Unit x y) (hy : InCT k l D' y) :
    D'=D ∨ ∃ e, D'=nbr D e := by
  have hxi : Interior k l (chart k l D 0 x) := (chart_interior D 0 x).mpr hx
  rcases unit_step_covered k l hk hl _ _ hxi (chart_unit D 0 x y hu) with hc | ⟨e,he⟩
  · have hv : ∀ m : Fin 3, chart k l D 0 y=ClaudeChallenge.corner k l m → False := by
      intro m hm
      rw [← zero_add m,← chart_vert (k:=k) (l:=l) D 0 m] at hm
      rw [chart_injective D 0 hm] at hy
      exact not_inCT_pos hk hl D' _ hy
    rcases closed_partition k l hk hl.le hprim _ hc with h | h | h | h
    · exact (hv 0 h).elim
    · exact (hv 1 h).elim
    · exact (hv 2 h).elim
    · exact Or.inl (inCT_unique hk hl D' D y hy ((chart_interior D 0 y).mp h))
  · exact Or.inr ⟨e,inCT_unique hk hl D' _ y hy (nbr_in D e y he)⟩

/-! ## Chart transfer -/

theorem chart_transfer (D D' : CT) (r r' : Fin 3) :
    ∃ (j : ℕ) (t : Lattice), ∀ y, rotN j (chart k l D' r' y)+t=chart k l D r y := by
  have hM := chartM_lt D r
  have hM' := chartM_lt D' r'
  refine ⟨(chartM D r+6-chartM D' r')%6,
    rotN (chartM D r) (pos k l (D'.vert 0)-pos k l (D.vert 0))+ClaudeChallenge.corner k l r-
    rotN ((chartM D r+6-chartM D' r')%6) (ClaudeChallenge.corner k l r'),fun y => ?_⟩
  simp only [chart]
  rw [rotN_add,rotN_rotN,rotN_mod _ (y-_),
    show ((chartM D r+6-chartM D' r')%6+chartM D' r')%6=chartM D r by omega]
  have : y-pos k l (D.vert 0)=(y-pos k l (D'.vert 0))+(pos k l (D'.vert 0)-pos k l (D.vert 0)) := by
    abel
  rw [this,rotN_add]
  abel

/-! ## Labelings -/

/-- The face and rotation carrying the labels `x,y,z` counterclockwise (if any). -/
def findFR (x y z : Fin 12) : Fin 20 × Fin 3 :=
  (((List.finRange 20).flatMap fun f => (List.finRange 3).map fun r => (f,r)).find?
    fun fr => ClaudeChallenge.face fr.1 fr.2==x && ClaudeChallenge.face fr.1 (fr.2+1)==y &&
      ClaudeChallenge.face fr.1 (fr.2+2)==z).getD (0,0)

def fr (L : ℤ × ℤ → Fin 12) (D : CT) : Fin 20 × Fin 3 :=
  findFR (L (D.vert 0)) (L (D.vert 1)) (L (D.vert 2))

def FaceOK (L : ℤ × ℤ → Fin 12) (D : CT) : Prop :=
  ∀ m : Fin 3, ClaudeChallenge.face (fr L D).1 ((fr L D).2+m)=L (D.vert m)

theorem fin3_aux : ∀ x y : Fin 3, x+1=y → x=y+1 → False := by decide
theorem fin3_ne : ∀ x y : Fin 3, x+y≠x+(y+1) := by decide

theorem glue_nbr (L : ℤ × ℤ → Fin 12) (D : CT) (e : Fin 3) (hD : FaceOK L D)
    (hD' : FaceOK L (nbr D e)) : ∃ j t,
      ClaudeChallenge.Glue k l (fr L (nbr D e)).1 (fr L D).1 j t ∧
      ∀ y, rotN j (chart k l (nbr D e) (fr L (nbr D e)).2 y)+t=chart k l D (fr L D).2 y := by
  obtain ⟨j,t,ht⟩ := chart_transfer (k:=k) (l:=l) D (nbr D e) (fr L D).2 (fr L (nbr D e)).2
  refine ⟨j,t,?_,ht⟩
  set f := (fr L D).1; set r := (fr L D).2
  set f' := (fr L (nbr D e)).1; set r' := (fr L (nbr D e)).2
  set g := nbrG D e
  obtain ⟨hv1,hv0⟩ := nbr_vert D e
  have ha : ClaudeChallenge.face f' (r'+(g+1))=ClaudeChallenge.face f (r+e) := by
    rw [hD' (g+1),hD e,hv0]
  have hb : ClaudeChallenge.face f' (r'+g)=ClaudeChallenge.face f (r+(e+1)) := by
    rw [hD' g,hD (e+1),hv1]
  refine ⟨?_,ClaudeChallenge.face f (r+e),ClaudeChallenge.face f (r+(e+1)),
    fun h => fin3_ne r e (challenge_face_injective f h),
    ClaudeChallenge.corner k l (r'+(g+1)),ClaudeChallenge.corner k l (r'+g),
    ClaudeChallenge.corner k l (r+e),ClaudeChallenge.corner k l (r+(e+1)),
    ⟨_,ha,rfl⟩,⟨_,hb,rfl⟩,⟨_,rfl,rfl⟩,⟨_,rfl,rfl⟩,?_,?_⟩
  · intro hff
    rw [hff] at ha hb
    have h1 := challenge_face_injective f ha
    have h2 := challenge_face_injective f hb
    exact fin3_aux (r'+g) (r+e) (by rw [← h1,add_assoc]) (by rw [h2,add_assoc])
  · have e1 := chart_vert (k:=k) (l:=l) (nbr D e) r' (g+1)
    have e2 := chart_vert (k:=k) (l:=l) D r e
    rw [hv0] at e1
    rw [← e1,← e2]; exact ht _
  · have e1 := chart_vert (k:=k) (l:=l) (nbr D e) r' g
    have e2 := chart_vert (k:=k) (l:=l) D r (e+1)
    rw [hv1] at e1
    rw [← e1,← e2]; exact ht _

/-! ## Sites and steps -/

def site (L : ℤ × ℤ → Fin 12) (D : CT) (x : Lattice) (h : InCT k l D x) :
    ClaudeChallenge.Site k l :=
  ⟨((fr L D).1,chart k l D (fr L D).2 x),
    (inTri_iff_closed _).mpr (interior_closed k l _ ((chart_interior D _ x).mpr h))⟩

theorem site_interior (L : ℤ × ℤ → Fin 12) (D : CT) (x : Lattice) (h : InCT k l D x) :
    Interior k l (site L D x h).val.2 := (chart_interior D _ x).mpr h

theorem step_sites (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) (L : ℤ × ℤ → Fin 12)
    (D D' : CT) (x y : Lattice) (hD : FaceOK L D) (hD' : FaceOK L D')
    (hx : InCT k l D x) (hy : InCT k l D' y) (hu : GCPrimitive.Unit x y) :
    ClaudeChallenge.StepTo k l (site L D x hx) (site L D' y hy) := by
  obtain ⟨u,hu',he⟩ := (unit_list_iff _ _).mpr (chart_unit D (fr L D).2 x y hu)
  refine ⟨u,hu',?_⟩
  rcases ct_step hk hl hprim D D' x y hx hu hy with rfl | ⟨e,rfl⟩
  · exact Or.inl ⟨rfl,he⟩
  · obtain ⟨j,t,hg,ht⟩ := glue_nbr (k:=k) (l:=l) L D e hD hD'
    exact Or.inr ⟨j,t,hg,(ht y).trans he⟩

end ClaudePos
