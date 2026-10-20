import Formal.GCSectorObstruction

/-! The two explicit finite traces start at genuine oriented graph triangles. -/
namespace R002.GCSector
open GCPrimitive GCPrimitiveSurface Icosahedron

def startDart (side : Bool) : Dart := if side then (0,1) else (14,0)
def startTile (side : Bool) : Tile := if side then ⟨0,0,true⟩ else ⟨-1,-1,true⟩

theorem start_third : ∀ side, thirdDart (startDart side) side=(5,0) := by decide +kernel
theorem start_parent {k l : ℤ} (side : Bool) : parent (k:=k) (l:=l) (startDart side)=parent (0,1) := by
  apply toCanonical_injective
  cases side <;> rfl

theorem start_local (P : Parameters) (side : Bool) :
    tileLocal P.k P.l (startTile side) (zigzag side 1)=unframe P.k P.l (startDart side).2 (0,1) := by
  cases side <;> ext <;> simp [startTile,startDart,zigzag,tileLocal,tileBase,A3.gc,unframe,GCPrimitive.turn] <;> ring
theorem start_face (P : Parameters) (side : Bool) :
    tileDart P (startTile side)=((startDart side).1,0) := by
  cases side
  · rw [show startTile false=⟨-1,-1,true⟩ from rfl,dart_band]; rfl
  · rw [show startTile true=⟨0,0,true⟩ from rfl,dart_top]; rfl
theorem start_interior (P : Parameters) (side : Bool) :
    Interior P.k P.l (tileLocal P.k P.l (startTile side) (zigzag side 1)) := by
  rw [start_local,interior_unframe]
  exact (origin_winner P.k P.l (params_positive P).2 (params_positive P).1).1

theorem second_local (P : Parameters) (side : Bool) : tileLocal P.k P.l ⟨0,-1,false⟩ (zigzag side 2)=(0,1) := by
  ext <;> simp [zigzag,tileLocal,tileBase,A3.gc]
theorem second_interior (P : Parameters) (side : Bool) :
    Interior P.k P.l (tileLocal P.k P.l ⟨0,-1,false⟩ (zigzag side 2)) := by
  rw [second_local]
  exact (origin_winner P.k P.l (params_positive P).2 (params_positive P).1).1

noncomputable def trace (P : Parameters) (hprim : Primitive P.k P.l) (side : Bool) (n : ℕ) : Vertex P.k P.l :=
  if hn : n=0 then parent (0,1)
  else if hb : n≤bound P side then stripVertex P hprim (zigzag side n)
    (zigzag_in_strip P side n hb) (zigzag_nonzero side n (Nat.pos_of_ne_zero hn))
  else parent (0,1)

theorem trace_zero (P : Parameters) (hprim : Primitive P.k P.l) (side : Bool) :
    trace P hprim side 0=parent (0,1) := by simp [trace]
theorem trace_strip (P : Parameters) (hprim : Primitive P.k P.l) (side : Bool) (n : ℕ)
    (hn : 0<n) (hb : n≤bound P side) :
    trace P hprim side n=stripVertex P hprim (zigzag side n) (zigzag_in_strip P side n hb) (zigzag_nonzero side n hn) := by
  simp [trace,show n≠0 by omega,hb]

theorem trace_one (P : Parameters) (hprim : Primitive P.k P.l) (side : Bool) :
    trace P hprim side 1=fan (params_positive P).2 (params_positive P).1 (startDart side) := by
  have hb : 1≤bound P side := by have := zigzag_indices_order P side; omega
  rw [trace_strip P hprim side 1 (by omega) hb,
    stripVertex_eq_chart P hprim _ _ _ (startTile side) (start_interior P side)]
  unfold chartVertex fan
  apply congrArg vertex
  apply Prod.ext
  · simp only [start_face]
  · apply congrArg Sum.inr
    apply Subtype.ext
    change unframe P.k P.l (tileDart P (startTile side)).2 _=unframe P.k P.l (startDart side).2 (0,1)
    rw [start_face]
    exact start_local P side

theorem trace_two (P : Parameters) (hprim : Primitive P.k P.l) (side : Bool) :
    trace P hprim side 2=fan (params_positive P).2 (params_positive P).1 (5,0) := by
  have hb : 2≤bound P side := by have := zigzag_indices_order P side; omega
  rw [trace_strip P hprim side 2 (by omega) hb,
    stripVertex_eq_chart P hprim _ _ _ ⟨0,-1,false⟩ (second_interior P side)]
  unfold chartVertex fan
  apply congrArg vertex
  apply Prod.ext
  · rw [dart_band]; rfl
  · apply congrArg Sum.inr
    apply Subtype.ext
    change unframe P.k P.l (tileDart P ⟨0,-1,false⟩).2 _=unframe P.k P.l 0 (0,1)
    rw [dart_band]
    exact second_local P side

theorem trace_degree (P : Parameters) (hprim : Primitive P.k P.l) (side : Bool) (n : ℕ)
    (hn : 0<n) (hb : n≤bound P side) : ClaudeChallenge.deg (graph P.k P.l) (trace P hprim side n)=6 := by
  rw [trace_strip P hprim side n hn hb]
  exact strip_degree P hprim _ _ _
theorem trace_root_degree (P : Parameters) (hprim : Primitive P.k P.l) (side : Bool) :
    ClaudeChallenge.deg (graph P.k P.l) (trace P hprim side 0)=5 := by
  rw [trace_zero]
  exact start_parent_degree (params_positive P).2 (params_positive P).1 _

end R002.GCSector
