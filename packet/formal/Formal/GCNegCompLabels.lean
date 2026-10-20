import Formal.GCNegAtlas

namespace R002.GCNeg
open Icosahedron GCPrimitive GCPrimitiveSurface GCSector

def phase3 (n : ZMod 3) (d : Dart) : Dart :=
  rotateDart ((![ (0,0),(11,0),(8,0)] : ZMod 3 → Rotation) n) d

theorem compatible_rotate (r : Rotation) (d : Dart) (e : Corner) (d' : Dart) (m : Corner)
    (h : Compatible d e d' m) : Compatible (rotateDart r d) e (rotateDart r d') m := by
  change mate (d.1,e+d.2)=(d'.1,m+d'.2) at h
  have hh := congrArg (rotateDart r) h
  rw [rotate_mate] at hh
  simpa only [Compatible,rotate_mate,rotateDart,add_assoc,add_left_comm,add_comm] using hh
theorem phase3_compatible (n : ZMod 3) (d : Dart) (e : Corner) (d' : Dart) (m : Corner)
    (h : Compatible d e d' m) : Compatible (phase3 n d) e (phase3 n d') m :=
  compatible_rotate _ d e d' m h
theorem phase3_zero : ∀ d, phase3 0 d=d := by decide +kernel

theorem comp_wrap : ∀ n, Compatible (phase3 n (11,0)) 1 (phase3 (n+1) (5,0)) 2 := by decide +kernel
theorem comp_wrap_rev : ∀ n, Compatible (phase3 n (5,0)) 2 (phase3 (n-1) (11,0)) 1 := by decide +kernel
theorem comp_terminal : ∀ n, Compatible (phase3 (n-1) (11,0)) 2 (phase3 n (1,0)) 0 := by decide +kernel
theorem comp_terminal_rev : ∀ n, Compatible (phase3 n (1,0)) 0 (phase3 (n-1) (11,0)) 2 := by decide +kernel
theorem comp_cap12 : ∀ n, Compatible (phase3 n (1,0)) 1 (phase3 n (6,2)) 0 := by decide +kernel
theorem comp_cap21 : ∀ n, Compatible (phase3 n (6,2)) 0 (phase3 n (1,0)) 1 := by decide +kernel
theorem comp_cap23 : ∀ n, Compatible (phase3 n (6,2)) 1 (phase3 n (10,0)) 2 := by decide +kernel
theorem comp_cap32 : ∀ n, Compatible (phase3 n (10,0)) 2 (phase3 n (6,2)) 1 := by decide +kernel
theorem comp_cap34 : ∀ n, Compatible (phase3 n (10,0)) 1 (phase3 n (15,1)) 0 := by decide +kernel
theorem comp_cap43 : ∀ n, Compatible (phase3 n (15,1)) 0 (phase3 n (10,0)) 1 := by decide +kernel

def compDart (P : Parameters) (t : Tile) : Dart :=
  if t.j=0 then (0,0)
  else if t.i= -1 then bandDart (-1) t.side
  else if t.i=P.q+1 then phase3 P.q
    (if t.j= -P.q then (if t.side then (6,2) else (1,0))
      else (if t.side then (15,1) else (10,0)))
  else phase3 (-t.j-1) (bandDart (if t.i+t.j= -1 then 0 else 1) t.side)

theorem comp_dart_top (P : Parameters) : compDart P ⟨0,0,true⟩=(0,0) := by simp [compDart]
theorem comp_dart_lower (P : Parameters) (s : Bool) :
    compDart P ⟨-1,-1,s⟩=bandDart (-1) s := by simp [compDart]
theorem comp_dart_reg0 (P : Parameters) (j : ℤ) (hj0 : -P.q≤j) (hj1 : j≤ -1) (s : Bool) :
    compDart P ⟨-j-1,j,s⟩=phase3 (-j-1) (bandDart 0 s) := by
  have hq := P.hq
  simp [compDart,show j≠0 by omega,show -j-1≠ -1 by omega,show -j-1≠P.q+1 by omega,show -j-1+j= -1 by omega]
theorem comp_dart_reg1 (P : Parameters) (j : ℤ) (hj0 : -P.q≤j) (hj1 : j≤ -1) (s : Bool) :
    compDart P ⟨-j,j,s⟩=phase3 (-j-1) (bandDart 1 s) := by
  have hq := P.hq
  simp [compDart,show j≠0 by omega,show -j≠ -1 by omega,show -j≠P.q+1 by omega]
theorem comp_dart_cap0 (P : Parameters) (s : Bool) :
    compDart P ⟨P.q+1,-P.q,s⟩=phase3 P.q (if s then (6,2) else (1,0)) := by
  have hq := P.hq
  simp [compDart,show -P.q≠0 by omega,show P.q+1≠ -1 by omega]
theorem comp_dart_cap1 (P : Parameters) (s : Bool) :
    compDart P ⟨P.q+1,-P.q-1,s⟩=phase3 P.q (if s then (15,1) else (10,0)) := by
  have hq := P.hq
  simp [compDart,show -P.q-1≠0 by omega,show P.q+1≠ -1 by omega]

theorem index_up (j : ℤ) : (-(↑(j+1) : ZMod 3)-1)=(-(↑j : ZMod 3)-1)-1 := by push_cast; ring
theorem index_down (j : ℤ) : (-(↑(j-1) : ZMod 3)-1)=(-(↑j : ZMod 3)-1)+1 := by push_cast; ring

end R002.GCNeg
