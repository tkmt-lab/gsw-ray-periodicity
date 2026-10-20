import Formal.ClaudeChallengeSpec
import Formal.GCPrimitiveDegree

/-! First comparison with the independently written challenge; no use of its main. -/
namespace R002.GCChallengeBridge
open Icosahedron GCPrimitive GCPrimitiveSurface
variable {k l : ℤ}

def faceMap : Face → Fin 20 := ![0,4,8,12,16,1,5,9,13,17,2,6,10,14,18,3,7,11,15,19]
def cornerMap (f : Face) (e : Corner) : Fin 3 := if f=4 then e+2 else e
def posMap (k l : ℤ) (f : Face) (p : Lattice) : Lattice := if f=4 then GCPrimitive.turn k l (GCPrimitive.turn k l p) else p
def posInverse (k l : ℤ) (f : Face) (p : Lattice) : Lattice := if f=4 then GCPrimitive.turn k l p else p

theorem faceMap_bijective : Function.Bijective faceMap := by decide +kernel

theorem labels_agree : ∀ f e, ClaudeChallenge.face (faceMap f) (cornerMap f e)=faceVertex f e := by
  decide +kernel

theorem cornerMap_add_one : ∀ f e, cornerMap f (e+1)=cornerMap f e+1 := by decide +kernel

theorem posInverse_posMap (f : Face) (p : Lattice) : posInverse k l f (posMap k l f p)=p := by
  by_cases hf : f=4 <;> simp [posMap,posInverse,hf,turn_three]

theorem posMap_posInverse (f : Face) (p : Lattice) : posMap k l f (posInverse k l f p)=p := by
  by_cases hf : f=4 <;> simp [posMap,posInverse,hf,turn_three]

theorem posMap_injective (f : Face) : Function.Injective (posMap k l f) :=
  (show Function.LeftInverse (posInverse k l f) (posMap k l f) from posInverse_posMap f).injective

theorem inTri_iff_closed (p : Lattice) : ClaudeChallenge.InTri k l p ↔ Closed k l p := by
  dsimp [ClaudeChallenge.InTri,Closed,a,b,c,norm]
  constructor <;> rintro ⟨ha,hb,hc⟩ <;> refine ⟨ha,hb,?_⟩ <;> nlinarith

theorem posMap_closed (f : Face) (p : Lattice) : Closed k l (posMap k l f p) ↔ Closed k l p := by
  by_cases hf : f=4 <;> simp [posMap,hf,closed_turn]

theorem posInverse_closed (f : Face) (p : Lattice) : Closed k l (posInverse k l f p) ↔ Closed k l p := by
  by_cases hf : f=4 <;> simp [posInverse,hf,closed_turn]

theorem corners_agree (f : Face) (e : Corner) :
    posMap k l f (corner k l e)=ClaudeChallenge.corner k l (cornerMap f e) := by
  by_cases hf : f=4
  · fin_cases e <;> ext <;> simp [posMap,cornerMap,hf,corner,ClaudeChallenge.corner,GCPrimitive.turn,A,B] <;> ring
  · simp [posMap,cornerMap,hf,corner,ClaudeChallenge.corner,A,B]

def rawSite (hk : 0<k) (hl : 0<l) (u : Raw k l) : ClaudeChallenge.Site k l :=
  ⟨(faceMap u.1,posMap k l u.1 (position u)),
    (inTri_iff_closed _).mpr ((posMap_closed u.1 _).mpr (position_closed hk hl.le u))⟩

theorem rawSite_injective (hk : 0<k) (hl : 0<l) : Function.Injective (rawSite hk hl) := by
  intro u v h
  have hf : faceMap u.1=faceMap v.1 := congrArg (fun z : ClaudeChallenge.Site k l => z.val.1) h
  have hg := faceMap_bijective.1 hf
  have hp : posMap k l u.1 (position u)=posMap k l v.1 (position v) :=
    congrArg (fun z : ClaudeChallenge.Site k l => z.val.2) h
  rw [← hg] at hp
  exact position_injective_in_face hk hl u v hg (posMap_injective u.1 hp)

theorem rawSite_surjective (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) :
    Function.Surjective (rawSite hk hl) := by
  intro s
  obtain ⟨f,hf⟩ := faceMap_bijective.2 s.val.1
  let p := posInverse k l f s.val.2
  have hp : Closed k l p := (posInverse_closed f _).mpr ((inTri_iff_closed _).mp s.property)
  obtain ⟨u,hu,hpos⟩ := closed_has_raw hk hl.le hprim f p hp
  refine ⟨u,Subtype.ext (Prod.ext ?_ ?_)⟩
  · change faceMap u.1=s.val.1
    rw [hu,hf]
  · change posMap k l u.1 (position u)=s.val.2
    rw [hu,hpos]
    exact posMap_posInverse f s.val.2

noncomputable def siteEquiv (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) :
    Raw k l ≃ ClaudeChallenge.Site k l := Equiv.ofBijective _
      ⟨rawSite_injective hk hl,rawSite_surjective hk hl hprim⟩

/-- Every seam coordinate change is one of the challenge's rotations plus a translation. -/
theorem affine_unfold (e m : Corner) : ∃ j : ℕ, ∃ t : Lattice, ∀ p : Lattice,
    ClaudeChallenge.rotN j p+t=unframe k l m (opposite k l (frame k l e p)) := by
  fin_cases e <;> fin_cases m
  · refine ⟨3,unframe k l 0 (opposite k l (frame k l 0 (0,0))),?_⟩
    intro p; ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,frame,unframe,opposite,GCPrimitive.turn] <;> ring
  · refine ⟨5,unframe k l 1 (opposite k l (frame k l 0 (0,0))),?_⟩
    intro p; ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,frame,unframe,opposite,GCPrimitive.turn] <;> ring
  · refine ⟨1,unframe k l 2 (opposite k l (frame k l 0 (0,0))),?_⟩
    intro p; ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,frame,unframe,opposite,GCPrimitive.turn] <;> ring
  · refine ⟨1,unframe k l 0 (opposite k l (frame k l 1 (0,0))),?_⟩
    intro p; ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,frame,unframe,opposite,GCPrimitive.turn] <;> ring
  · refine ⟨3,unframe k l 1 (opposite k l (frame k l 1 (0,0))),?_⟩
    intro p; ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,frame,unframe,opposite,GCPrimitive.turn] <;> ring
  · refine ⟨5,unframe k l 2 (opposite k l (frame k l 1 (0,0))),?_⟩
    intro p; ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,frame,unframe,opposite,GCPrimitive.turn] <;> ring
  · refine ⟨5,unframe k l 0 (opposite k l (frame k l 2 (0,0))),?_⟩
    intro p; ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,frame,unframe,opposite,GCPrimitive.turn] <;> ring
  · refine ⟨1,unframe k l 1 (opposite k l (frame k l 2 (0,0))),?_⟩
    intro p; ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,frame,unframe,opposite,GCPrimitive.turn] <;> ring
  · refine ⟨3,unframe k l 2 (opposite k l (frame k l 2 (0,0))),?_⟩
    intro p; ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot,frame,unframe,opposite,GCPrimitive.turn] <;> ring

end R002.GCChallengeBridge
