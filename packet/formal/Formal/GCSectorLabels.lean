import Formal.GCSectorActive
import Mathlib.Data.ZMod.Basic

/-! Finite parent labels and seam checks for the developed belt-cap-return patch. -/
namespace R002.GCSector
open Icosahedron

def labelA : ZMod 5 → Face := ![5,6,7,8,9]
def labelB : ZMod 5 → Face := ![10,11,12,13,14]
def labelC : ZMod 5 → Face := ![15,16,17,18,19]
def bandDart (i : ZMod 5) (side : Bool) : Dart :=
  if side then (labelB i,0) else (labelA i,0)
def capDart (q : ZMod 5) (side : Bool) : Dart :=
  if side then (labelC (q+1),2) else (labelC q,2)
def returnDart (q j : ZMod 5) (side : Bool) : Dart :=
  if side then (labelA (q-j),0) else (labelB (q-j-1),1)

def Compatible (d : Dart) (e : Corner) (d' : Dart) (m : Corner) : Prop :=
  mate (d.1,e+d.2)=(d'.1,m+d'.2)
instance (d : Dart) (e : Corner) (d' : Dart) (m : Corner) :
    Decidable (Compatible d e d' m) := inferInstanceAs (Decidable (_=_))

theorem band_left : ∀ i, Compatible (bandDart i false) 0 (bandDart (i-1) true) 2 := by decide +kernel
theorem band_diag : ∀ i, Compatible (bandDart i false) 1 (bandDart i true) 0 := by decide +kernel
theorem band_diag_rev : ∀ i, Compatible (bandDart i true) 0 (bandDart i false) 1 := by decide +kernel
theorem band_right : ∀ i, Compatible (bandDart i true) 2 (bandDart (i+1) false) 0 := by decide +kernel
theorem band_top : Compatible (bandDart 0 false) 2 (0,0) 1 := by decide +kernel
theorem top_band : Compatible (0,0) 1 (bandDart 0 false) 2 := by decide +kernel
theorem band_cap : ∀ q, Compatible (bandDart q true) 1 (capDart q false) 2 := by decide +kernel
theorem cap_band : ∀ q, Compatible (capDart q false) 2 (bandDart q true) 1 := by decide +kernel
theorem cap_diag : ∀ q, Compatible (capDart q false) 1 (capDart q true) 0 := by decide +kernel
theorem cap_diag_rev : ∀ q, Compatible (capDart q true) 0 (capDart q false) 1 := by decide +kernel
theorem cap_return : ∀ q, Compatible (capDart q true) 2 (returnDart q (-2) false) 0 := by decide +kernel
theorem return_cap : ∀ q, Compatible (returnDart q (-2) false) 0 (capDart q true) 2 := by decide +kernel
theorem return_diag : ∀ q j, Compatible (returnDart q j false) 1 (returnDart q j true) 0 := by decide +kernel
theorem return_up : ∀ q j, Compatible (returnDart q j false) 2 (returnDart q (j+1) true) 1 := by decide +kernel
theorem return_diag_rev : ∀ q j, Compatible (returnDart q j true) 0 (returnDart q j false) 1 := by decide +kernel
theorem return_down : ∀ q j, Compatible (returnDart q j true) 1 (returnDart q (j-1) false) 2 := by decide +kernel

def tileDart (P : Parameters) (t : Tile) : Dart :=
  if t.j= -1 then bandDart t.i t.side
  else if t.i=P.q then capDart P.q t.side
  else if t.i=P.q+1 then returnDart P.q t.j t.side
  else (0,0)

theorem dart_band (P : Parameters) (i : ℤ) (s : Bool) :
    tileDart P ⟨i,-1,s⟩=bandDart i s := by simp [tileDart]
theorem dart_cap (P : Parameters) (s : Bool) :
    tileDart P ⟨P.q,-2,s⟩=capDart P.q s := by simp [tileDart]
theorem dart_return (P : Parameters) (j : ℤ) (hj : j≤ -2) (s : Bool) :
    tileDart P ⟨P.q+1,j,s⟩=returnDart P.q j s := by
  have hj' : j≠ -1 := by omega
  simp [tileDart,hj']
theorem dart_top (P : Parameters) : tileDart P ⟨0,0,true⟩=(0,0) := by
  have hq := P.hq
  simp [tileDart,show (0:ℤ)≠P.q by omega,show (0:ℤ)≠P.q+1 by omega]

/-- Every adjacent pair actually used by the strip has the required parent mate. -/
theorem active_compatible (P : Parameters) (t : Tile) (e : Corner)
    (ht : Active P t) (hu : Active P (tileNeighbor t e)) :
    Compatible (tileDart P t) e (tileDart P (tileNeighbor t e)) (tileMateCorner t e) := by
  have hq := P.hq
  rcases t with ⟨i,j,s⟩
  rcases ht with ⟨hj,hi⟩|⟨hi,hj⟩|⟨hi,hj⟩|⟨hi,hj,hs⟩
  · dsimp at hj hi
    subst j
    cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
    · rw [dart_band,dart_band]
      simpa only [Int.cast_sub,Int.cast_one] using band_left (i : ZMod 5)
    · rw [dart_band,dart_band]; exact band_diag _
    · have hi0 : i=0 := by simp [Active] at hu <;> omega
      subst i
      rw [dart_band,dart_top]; exact band_top
    · rw [dart_band,dart_band]; exact band_diag_rev _
    · have hiq : i=P.q := by simp [Active] at hu <;> omega
      subst i
      rw [dart_band,dart_cap]; exact band_cap _
    · rw [dart_band,dart_band]
      simpa only [Int.cast_add,Int.cast_one] using band_right (i : ZMod 5)
  · dsimp at hi hj
    subst i; subst j
    cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
    · simp [Active] at hu <;> omega
    · rw [dart_cap,dart_cap]; exact cap_diag _
    · rw [dart_cap,dart_band]; exact cap_band _
    · rw [dart_cap,dart_cap]; exact cap_diag_rev _
    · simp [Active] at hu <;> omega
    · rw [dart_cap,dart_return P (-2) (by omega)]
      simpa using cap_return (P.q : ZMod 5)
  · dsimp at hi hj
    subst i
    cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
    · have hj2 : j= -2 := by simp [Active] at hu <;> omega
      subst j
      rw [dart_return P (-2) (by omega)]
      rw [dart_cap]
      simpa using return_cap (P.q : ZMod 5)
    · rw [dart_return P j hj,dart_return P j hj]; exact return_diag _ _
    · have hju : j+1≤ -2 := by simp [Active] at hu <;> omega
      rw [dart_return P j hj,dart_return P (j+1) hju]
      simpa only [Int.cast_add,Int.cast_one] using return_up (P.q : ZMod 5) (j : ZMod 5)
    · rw [dart_return P j hj,dart_return P j hj]; exact return_diag_rev _ _
    · rw [dart_return P j hj,dart_return P (j-1) (by omega)]
      simpa only [Int.cast_sub,Int.cast_one] using return_down (P.q : ZMod 5) (j : ZMod 5)
    · simp [Active] at hu <;> omega
  · dsimp at hi hj hs
    subst i; subst j; subst s
    fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
    · simp [Active] at hu <;> omega
    · rw [dart_top,dart_band]; exact top_band
    · simp [Active] at hu <;> omega

end R002.GCSector
