import Formal.GCNegAtlas

namespace R002.GCNeg
open Icosahedron GCPrimitive GCPrimitiveSurface GCSector

theorem zigzag_region (S : Atlas) (side : Bool) (n : ℕ) (hn : n≤(2*S.A).toNat) :
    Region S.A (zigzag side n) := by
  have ha := S.hA
  obtain ⟨t,rfl|rfl⟩ := index_parity n
  · rw [zigzag_even]; dsimp [Region]; omega
  · rw [zigzag_odd]; cases side <;> dsimp [Region] <;> omega

theorem start_local (S : Atlas) (side : Bool) :
    tileLocal S.k S.l (startTile side) (zigzag side 1)=unframe S.k S.l (startDart side).2 (0,1) := by
  cases side <;> ext <;> simp [startTile,startDart,zigzag,tileLocal,tileBase,A3.gc,unframe,GCPrimitive.turn] <;> ring
theorem start_face (S : Atlas) (side : Bool) :
    S.dart (startTile side)=((startDart side).1,0) := by
  cases side
  · exact S.dartLower
  · exact S.dartTop
theorem start_interior (S : Atlas) (side : Bool) :
    Interior S.k S.l (tileLocal S.k S.l (startTile side) (zigzag side 1)) := by
  rw [start_local,interior_unframe]
  exact (origin_winner S.k S.l S.hkl S.hl).1

theorem second_local (S : Atlas) (side : Bool) : tileLocal S.k S.l ⟨0,-1,false⟩ (zigzag side 2)=(0,1) := by
  ext <;> simp [zigzag,tileLocal,tileBase,A3.gc]
theorem second_interior (S : Atlas) (side : Bool) :
    Interior S.k S.l (tileLocal S.k S.l ⟨0,-1,false⟩ (zigzag side 2)) := by
  rw [second_local]
  exact (origin_winner S.k S.l S.hkl S.hl).1

noncomputable def trace (S : Atlas) (side : Bool) (n : ℕ) : Vertex S.k S.l :=
  if hn : n=0 then parent (0,1)
  else if hb : n≤(2*S.A).toNat then stripVertex S (zigzag side n)
    (zigzag_region S side n hb) (zigzag_nonzero side n (Nat.pos_of_ne_zero hn))
  else parent (0,1)

theorem trace_zero (S : Atlas) (side : Bool) :
    trace S side 0=parent (0,1) := by simp [trace]
theorem trace_strip (S : Atlas) (side : Bool) (n : ℕ)
    (hn : 0<n) (hb : n≤(2*S.A).toNat) :
    trace S side n=stripVertex S (zigzag side n) (zigzag_region S side n hb) (zigzag_nonzero side n hn) := by
  simp [trace,show n≠0 by omega,hb]

theorem trace_one (S : Atlas) (side : Bool) :
    trace S side 1=fan S.hkl S.hl (startDart side) := by
  have hb : 1≤(2*S.A).toNat := by have := S.hA; omega
  rw [trace_strip S side 1 (by omega) hb,
    stripVertex_eq_chart S _ _ _ (startTile side) (start_interior S side)]
  unfold chartVertex fan
  apply congrArg vertex
  apply Prod.ext
  · simp only [start_face]
  · apply congrArg Sum.inr
    apply Subtype.ext
    change unframe S.k S.l (S.dart (startTile side)).2 _=unframe S.k S.l (startDart side).2 (0,1)
    rw [start_face]
    exact start_local S side

theorem trace_two (S : Atlas) (side : Bool) :
    trace S side 2=fan S.hkl S.hl (5,0) := by
  have hb : 2≤(2*S.A).toNat := by have := S.hA; omega
  rw [trace_strip S side 2 (by omega) hb,
    stripVertex_eq_chart S _ _ _ ⟨0,-1,false⟩ (second_interior S side)]
  unfold chartVertex fan
  apply congrArg vertex
  apply Prod.ext
  · rw [S.dartSecond]
  · apply congrArg Sum.inr
    apply Subtype.ext
    change unframe S.k S.l (S.dart ⟨0,-1,false⟩).2 _=unframe S.k S.l 0 (0,1)
    rw [S.dartSecond]
    exact second_local S side

theorem trace_degree (S : Atlas) (side : Bool) (n : ℕ)
    (hn : 0<n) (hb : n≤(2*S.A).toNat) : ClaudeChallenge.deg (graph S.k S.l) (trace S side n)=6 := by
  rw [trace_strip S side n hn hb]
  exact strip_degree S _ _ _
theorem trace_root_degree (S : Atlas) (side : Bool) :
    ClaudeChallenge.deg (graph S.k S.l) (trace S side 0)=5 := by
  rw [trace_zero]
  exact start_parent_degree S.hkl S.hl _

theorem trace_adjacent (S : Atlas) (side : Bool)
    (n : ℕ) (hn : n+1≤(2*S.A).toNat) :
    (graph S.k S.l).Adj (trace S side n) (trace S side (n+1)) := by
  by_cases hz : n=0
  · subst n
    rw [trace_zero,trace_one,← start_parent side]
    exact fan_adj_parent S.hkl S.hl _
  · rw [trace_strip S side n (by omega) (by omega),
      trace_strip S side (n+1) (by omega) hn]
    exact strip_adjacent S _ _ _ _ _ _ (zigzag_unit side n)

theorem trace_skip (S : Atlas) (side : Bool)
    (n : ℕ) (hn : n+2≤(2*S.A).toNat) :
    (graph S.k S.l).Adj (trace S side n) (trace S side (n+2)) := by
  by_cases hz : n=0
  · subst n
    rw [trace_zero,trace_two]
    have he : parent (k:=S.k) (l:=S.l) (5,0)=parent (0,1) := by apply toCanonical_injective; rfl
    rw [← he]
    exact fan_adj_parent S.hkl S.hl _
  · rw [trace_strip S side n (by omega) (by omega),
      trace_strip S side (n+2) (by omega) hn]
    exact strip_adjacent S _ _ _ _ _ _ (zigzag_skip_unit side n)

theorem trace_no_backtrack (S : Atlas) (side : Bool)
    (n : ℕ) (hn : n+3≤(2*S.A).toNat) : trace S side (n+3)≠trace S side n := by
  intro he
  by_cases hz : n=0
  · subst n
    have hd := trace_degree S side 3 (by omega) hn
    rw [he,trace_root_degree] at hd
    omega
  · rw [trace_strip S side (n+3) (by omega) hn,
      trace_strip S side n (by omega) (by omega)] at he
    have hh := strip_neighbor_injective S (zigzag side (n+1)) (zigzag side (n+3)) (zigzag side n)
      (zigzag_region S side (n+1) (by omega)) (zigzag_region S side (n+3) hn)
      (zigzag_region S side n (by omega)) (zigzag_nonzero side (n+1) (by omega))
      (zigzag_nonzero side (n+3) (by omega)) (zigzag_nonzero side n (by omega))
      (zigzag_skip_unit side (n+1)) (unit_symm _ _ (zigzag_unit side n)) he
    exact zigzag_three_ne side n hh

theorem trace_forced (S : Atlas) (side : Bool) :
    ForcedPrefix (graph S.k S.l) (trace S side) ((2*S.A).toNat) :=
  ⟨trace_adjacent S side,trace_skip S side,trace_no_backtrack S side⟩

theorem no_path_of_repeat (S : Atlas) (side : Bool) (e N : ℕ)
    (he : e<N) (hN : N≤(2*S.A).toNat) (hrep : trace S side e=trace S side N) :
    ¬PathFromTriangle (startTriangle S.hkl S.hl (startDart side) side) := by
  have hforced : ForcedPrefix (graph S.k S.l) (trace S side) N :=
    ⟨fun i hi => trace_adjacent S side i (by omega),
      fun i hi => trace_skip S side i (by omega),fun i hi => trace_no_backtrack S side i (by omega)⟩
  have hobs := repetition_obstructs (graph S.k S.l) (two_common_neighbors S.hkl S.hl S.hprim)
    (trace S side) N e hforced (fun i hi hiN => trace_degree S side i hi (by omega)) he hrep
  rintro ⟨n,p,hp,h0,h1,h2⟩
  apply hobs
  refine ⟨n,p,hp,?_,?_,?_⟩
  · simpa only [startTriangle,start_parent,trace_zero] using h0
  · simpa only [startTriangle,trace_one] using h1
  · simpa only [startTriangle,start_third,trace_two] using h2

theorem no_challenge_of_repeats (S : Atlas)
    (H : ∀ side, ∃ e N, e<N ∧ N≤(2*S.A).toNat ∧ trace S side e=trace S side N) :
    ¬∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph S.k S.l) n p := by
  rw [challenge_paths_iff_two_starts S.hkl S.hl S.hprim]
  rintro ⟨side,hp⟩
  have hh := map_path_from (rotationGraphIso (startDart side)) _ hp
  rw [representative,rotate_startTriangle,rotate_root] at hh
  obtain ⟨e,N,he,hN,hrep⟩ := H side
  exact no_path_of_repeat S side e N he hN hrep hh

end R002.GCNeg
