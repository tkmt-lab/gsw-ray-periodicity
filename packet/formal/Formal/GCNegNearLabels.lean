import Formal.GCNegMinusActive
import Formal.GCNegCompSeams

namespace R002.GCNeg
open Icosahedron GCPrimitive GCPrimitiveSurface GCSector

def phasePsi (n : ZMod 2) (d : Dart) := rotateDart ((![(0,0),(12,0)] : ZMod 2 → Rotation) n) d
def phaseChi (n : ZMod 2) (d : Dart) := rotateDart ((![(0,0),(7,0)] : ZMod 2 → Rotation) n) d
theorem psi_zero : ∀ d, phasePsi 0 d=d := by decide +kernel
theorem chi_zero : ∀ d, phaseChi 0 d=d := by decide +kernel
theorem psi_compatible (n : ZMod 2) (d : Dart) (e : Corner) (d' : Dart) (m : Corner)
    (h : Compatible d e d' m) : Compatible (phasePsi n d) e (phasePsi n d') m := compatible_rotate _ _ _ _ _ h
theorem chi_compatible (n : ZMod 2) (d : Dart) (e : Corner) (d' : Dart) (m : Corner)
    (h : Compatible d e d' m) : Compatible (phaseChi n d) e (phaseChi n d') m := compatible_rotate _ _ _ _ _ h

theorem psi_wrap : ∀ n, Compatible (phasePsi n (bandDart 2 true)) 1 (phasePsi (n+1) (bandDart 0 false)) 2 := by decide +kernel
theorem psi_wrap_rev : ∀ n, Compatible (phasePsi n (bandDart 0 false)) 2 (phasePsi (n-1) (bandDart 2 true)) 1 := by decide +kernel
theorem psi_terminal : ∀ n, Compatible (phasePsi (n-1) (bandDart 2 true)) 2 (phasePsi n (1,0)) 0 := by decide +kernel
theorem psi_terminal_rev : ∀ n, Compatible (phasePsi n (1,0)) 0 (phasePsi (n-1) (bandDart 2 true)) 2 := by decide +kernel

def gDart (tail side : Bool) : Dart := if tail then (if side then (15,1) else (10,0)) else (if side then (6,2) else (1,0))
def hDart (tail side : Bool) : Dart := if tail then (if side then (7,0) else (11,1)) else (if side then (16,2) else (15,2))
theorem psi_caps : ∀ n,
    Compatible (phasePsi n (gDart false false)) 1 (phasePsi n (gDart false true)) 0 ∧
    Compatible (phasePsi n (gDart false true)) 0 (phasePsi n (gDart false false)) 1 ∧
    Compatible (phasePsi n (gDart false true)) 1 (phasePsi n (gDart true false)) 2 ∧
    Compatible (phasePsi n (gDart true false)) 2 (phasePsi n (gDart false true)) 1 ∧
    Compatible (phasePsi n (gDart true false)) 1 (phasePsi n (gDart true true)) 0 ∧
    Compatible (phasePsi n (gDart true true)) 0 (phasePsi n (gDart true false)) 1 := by decide +kernel

def minusBase (m : ℤ) (s : Bool) : Dart :=
  if m= -1 then bandDart 1 s else if m= -3 then (if s then (17,2) else (16,2)) else (if s then (8,0) else (12,1))
theorem chi_seams : ∀ n,
    Compatible (phaseChi n (minusBase (-1) true)) 1 (phaseChi n (minusBase (-3) false)) 2 ∧
    Compatible (phaseChi n (minusBase (-3) false)) 2 (phaseChi n (minusBase (-1) true)) 1 ∧
    Compatible (phaseChi n (minusBase (-3) true)) 2 (phaseChi n (minusBase (-2) false)) 0 ∧
    Compatible (phaseChi n (minusBase (-2) false)) 0 (phaseChi n (minusBase (-3) true)) 2 ∧
    Compatible (phaseChi n (minusBase (-2) true)) 2 (phaseChi (n+1) (minusBase (-1) false)) 0 ∧
    Compatible (phaseChi n (minusBase (-1) false)) 0 (phaseChi (n-1) (minusBase (-2) true)) 2 := by decide +kernel
theorem chi_initial : Compatible (bandDart 0 true) 2 (minusBase (-1) false) 0 ∧
    Compatible (minusBase (-1) false) 0 (bandDart 0 true) 2 := by decide +kernel
theorem chi_terminal : ∀ n, Compatible (phaseChi (n-1) (minusBase (-2) true)) 1 (phaseChi n (hDart false false)) 2 ∧
    Compatible (phaseChi n (hDart false false)) 2 (phaseChi (n-1) (minusBase (-2) true)) 1 := by decide +kernel
theorem chi_caps : ∀ n,
    Compatible (phaseChi n (hDart false false)) 1 (phaseChi n (hDart false true)) 0 ∧
    Compatible (phaseChi n (hDart false true)) 0 (phaseChi n (hDart false false)) 1 ∧
    Compatible (phaseChi n (hDart false true)) 2 (phaseChi n (hDart true false)) 0 ∧
    Compatible (phaseChi n (hDart true false)) 0 (phaseChi n (hDart false true)) 2 ∧
    Compatible (phaseChi n (hDart true false)) 1 (phaseChi n (hDart true true)) 0 ∧
    Compatible (phaseChi n (hDart true true)) 0 (phaseChi n (hDart true false)) 1 := by decide +kernel
theorem minus_diag : ∀ m ∈ ({-1,-3,-2} : Finset ℤ), Compatible (minusBase m false) 1 (minusBase m true) 0 ∧
    Compatible (minusBase m true) 0 (minusBase m false) 1 := by
  intro m hm; simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl|rfl|rfl <;> decide +kernel

def plusDart (P : TailParameters) (t : Tile) : Dart :=
  if t.j=0 then (0,0) else if t.i= -1 then bandDart (-1) t.side
  else if t.i=2*P.a+3 then phasePsi (P.a+1) (gDart (decide (t.j≠ -P.a-1)) t.side)
  else phasePsi (-t.j-1) (bandDart ((t.i+2*t.j+2 : ℤ) : ZMod 5) t.side)
def minusDart (P : TailParameters) (t : Tile) : Dart :=
  if t.j=0 then (0,0) else if t.i= -1 then bandDart (-1) t.side
  else if t.i=0 then bandDart 0 t.side
  else if t.j= -P.a-2 then phaseChi P.a (hDart (decide (t.i≠2*P.a)) t.side)
  else phaseChi (-t.j-(if t.i+2*t.j= -1 then 1 else 2)) (minusBase (t.i+2*t.j) t.side)

theorem psi_index_up (j : ℤ) : -(↑(j+1):ZMod 2)-1=(-↑j-1)-1 := by push_cast; ring
theorem psi_index_down (j : ℤ) : -(↑(j-1):ZMod 2)-1=(-↑j-1)+1 := by push_cast; ring

end R002.GCNeg
