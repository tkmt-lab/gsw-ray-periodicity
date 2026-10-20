import Formal.GCSectorArithmetic

/-! A developed triangular tiling at scale (k,l), independent of parent labels. -/
namespace R002.GCSector
open GCPrimitive Icosahedron

structure Tile where
  i : ℤ
  j : ℤ
  side : Bool
  deriving DecidableEq

def tileBase (k l : ℤ) (t : Tile) : Lattice :=
  A3.gc k l (t.i-t.j-(if t.side then 0 else 1)) (t.j+1)
def tileLocal (k l : ℤ) (t : Tile) (p : Lattice) : Lattice :=
  let v := p-tileBase k l t
  if t.side then (-v.1-v.2,v.1) else (-v.2,v.1+v.2)
def tileEmbed (k l : ℤ) (t : Tile) (p : Lattice) : Lattice :=
  tileBase k l t + if t.side then (p.2,-p.1-p.2) else (p.1+p.2,-p.1)

theorem tile_inverse (k l : ℤ) (t : Tile) (p : Lattice) :
    tileEmbed k l t (tileLocal k l t p)=p ∧ tileLocal k l t (tileEmbed k l t p)=p := by
  rcases t with ⟨i,j,side⟩
  cases side <;> constructor <;> ext <;> dsimp [tileEmbed,tileLocal,tileBase,A3.gc] <;> ring

theorem tile_local_injective (k l : ℤ) (t : Tile) : Function.Injective (tileLocal k l t) :=
  (show Function.LeftInverse (tileEmbed k l t) (tileLocal k l t) from fun p => (tile_inverse k l t p).1).injective

theorem tile_slices_A (k l i j : ℤ) (p : Lattice) :
    a k l (tileLocal k l ⟨i,j,false⟩ p)=(j+1)*norm k l-b k l p ∧
    b k l (tileLocal k l ⟨i,j,false⟩ p)=a k l p+b k l p-i*norm k l ∧
    c k l (tileLocal k l ⟨i,j,false⟩ p)=(i-j)*norm k l-a k l p := by
  dsimp [a,b,c,GCPrimitive.norm,tileLocal,tileBase,A3.gc]
  constructor
  · ring
  constructor <;> ring

theorem tile_slices_B (k l i j : ℤ) (p : Lattice) :
    a k l (tileLocal k l ⟨i,j,true⟩ p)=(i+1)*norm k l-(a k l p+b k l p) ∧
    b k l (tileLocal k l ⟨i,j,true⟩ p)=a k l p-(i-j)*norm k l ∧
    c k l (tileLocal k l ⟨i,j,true⟩ p)=b k l p-j*norm k l := by
  dsimp [a,b,c,GCPrimitive.norm,tileLocal,tileBase,A3.gc]
  constructor
  · ring
  constructor <;> ring

theorem tile_box (k l : ℤ) (t : Tile) (p : Lattice)
    (hp : Interior k l (tileLocal k l t p)) :
    t.i*norm k l<a k l p+b k l p ∧ a k l p+b k l p<(t.i+1)*norm k l ∧
    t.j*norm k l<b k l p ∧ b k l p<(t.j+1)*norm k l := by
  rcases t with ⟨i,j,side⟩
  cases side
  · have h := tile_slices_A k l i j p
    dsimp [Interior] at hp
    rw [h.1,h.2.1,h.2.2] at hp
    dsimp
    constructor
    · linarith
    constructor
    · nlinarith
    constructor <;> nlinarith
  · have h := tile_slices_B k l i j p
    dsimp [Interior] at hp
    rw [h.1,h.2.1,h.2.2] at hp
    dsimp
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith

theorem interval_index_unique (T x i j : ℤ) (hT : 0<T)
    (hi : i*T<x ∧ x<(i+1)*T) (hj : j*T<x ∧ x<(j+1)*T) : i=j := by
  rcases lt_trichotomy i j with h|h|h
  · have hh := mul_le_mul_of_nonneg_right (show i + 1 ≤ j by omega) hT.le
    nlinarith [hi.2,hj.1]
  · exact h
  · have hh := mul_le_mul_of_nonneg_right (show j + 1 ≤ i by omega) hT.le
    nlinarith [hi.1,hj.2]

theorem tile_unique (k l : ℤ) (hT : 0<norm k l) (t u : Tile) (p : Lattice)
    (ht : Interior k l (tileLocal k l t p)) (hu : Interior k l (tileLocal k l u p)) : t=u := by
  have hb := tile_box k l t p ht
  have hc := tile_box k l u p hu
  have hi := interval_index_unique _ _ _ _ hT ⟨hb.1,hb.2.1⟩ ⟨hc.1,hc.2.1⟩
  have hj := interval_index_unique _ _ _ _ hT hb.2.2 hc.2.2
  rcases t with ⟨i,j,s⟩
  rcases u with ⟨i',j',s'⟩
  dsimp at hi hj
  subst i'; subst j'
  cases s <;> cases s'
  · rfl
  · have h1 := (tile_slices_A k l i j p).2.2
    have h2 := (tile_slices_B k l i j p).2.1
    have hh := ht.2.2; have hg := hu.2.1
    rw [h1] at hh; rw [h2] at hg; omega
  · have h1 := (tile_slices_B k l i j p).2.1
    have h2 := (tile_slices_A k l i j p).2.2
    have hh := ht.2.1; have hg := hu.2.2
    rw [h1] at hh; rw [h2] at hg; omega
  · rfl

def tileNeighbor (t : Tile) (e : Corner) : Tile :=
  if t.side then ![⟨t.i,t.j,false⟩,⟨t.i,t.j-1,false⟩,⟨t.i+1,t.j,false⟩] e
  else ![⟨t.i-1,t.j,true⟩,⟨t.i,t.j,true⟩,⟨t.i,t.j+1,true⟩] e

def tileMateCorner (t : Tile) (e : Corner) : Corner :=
  if t.side then ![1,2,0] e else ![2,0,1] e

theorem neighbor_coordinates (k l : ℤ) (t : Tile) (e : Corner) (p : Lattice) :
    tileLocal k l (tileNeighbor t e) p=
      unframe k l (tileMateCorner t e) (opposite k l (frame k l e (tileLocal k l t p))) := by
  rcases t with ⟨i,j,side⟩
  cases side <;> fin_cases e <;> ext <;>
    simp [tileNeighbor,tileMateCorner,tileLocal,tileBase,A3.gc,frame,unframe,opposite,GCPrimitive.turn] <;> ring

theorem tile_unit_forward (k l : ℤ) (t : Tile) (p q : Lattice) (h : Unit p q) :
    Unit (tileLocal k l t p) (tileLocal k l t q) := by
  obtain ⟨d,rfl⟩ := h
  rcases t with ⟨i,j,side⟩
  cases side
  · refine ⟨d+1,?_⟩
    fin_cases d <;> ext <;> simp [tileLocal,direction] <;> ring
  · refine ⟨d+2,?_⟩
    fin_cases d <;> ext <;> simp [tileLocal,direction] <;> ring

/-- From any interior tile, a unit step is in this tile or an immediate adjacent tile. -/
theorem tile_step_covered (k l : ℤ) (hk : 0<k) (hl : 0<l) (t : Tile) (p q : Lattice)
    (hp : Interior k l (tileLocal k l t p)) (hu : Unit p q) :
    Closed k l (tileLocal k l t q) ∨
      ∃ e : Corner, Interior k l (tileLocal k l (tileNeighbor t e) q) := by
  rcases unit_step_covered k l hk hl _ _ hp (tile_unit_forward k l t p q hu) with h|⟨e,he⟩
  · exact Or.inl h
  · refine Or.inr ⟨e,?_⟩
    rw [neighbor_coordinates,interior_unframe]
    exact he

end R002.GCSector
