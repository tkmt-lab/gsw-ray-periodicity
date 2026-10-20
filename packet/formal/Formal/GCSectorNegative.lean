import Formal.GCSectorTrace

/-! General first negative sector: both actual starts repeat before reaching any other degree-five vertex. -/
namespace R002.GCSector
open GCPrimitive GCPrimitiveSurface Icosahedron

theorem trace_adjacent (P : Parameters) (hprim : Primitive P.k P.l) (side : Bool)
    (n : ℕ) (hn : n+1≤bound P side) :
    (graph P.k P.l).Adj (trace P hprim side n) (trace P hprim side (n+1)) := by
  by_cases hz : n=0
  · subst n
    rw [trace_zero,trace_one,← start_parent side]
    exact fan_adj_parent (params_positive P).2 (params_positive P).1 _
  · rw [trace_strip P hprim side n (by omega) (by omega),
      trace_strip P hprim side (n+1) (by omega) hn]
    exact strip_adjacent P hprim _ _ _ _ _ _ (zigzag_unit side n)

theorem trace_skip (P : Parameters) (hprim : Primitive P.k P.l) (side : Bool)
    (n : ℕ) (hn : n+2≤bound P side) :
    (graph P.k P.l).Adj (trace P hprim side n) (trace P hprim side (n+2)) := by
  by_cases hz : n=0
  · subst n
    rw [trace_zero,trace_two]
    have he : parent (k:=P.k) (l:=P.l) (5,0)=parent (0,1) := by apply toCanonical_injective; rfl
    rw [← he]
    exact fan_adj_parent (params_positive P).2 (params_positive P).1 _
  · rw [trace_strip P hprim side n (by omega) (by omega),
      trace_strip P hprim side (n+2) (by omega) hn]
    exact strip_adjacent P hprim _ _ _ _ _ _ (zigzag_skip_unit side n)

theorem trace_no_backtrack (P : Parameters) (hprim : Primitive P.k P.l) (side : Bool)
    (n : ℕ) (hn : n+3≤bound P side) : trace P hprim side (n+3)≠trace P hprim side n := by
  intro he
  by_cases hz : n=0
  · subst n
    have hd := trace_degree P hprim side 3 (by omega) hn
    rw [he,trace_root_degree] at hd
    omega
  · rw [trace_strip P hprim side (n+3) (by omega) hn,
      trace_strip P hprim side n (by omega) (by omega)] at he
    have hh := strip_neighbor_injective P hprim (zigzag side (n+1)) (zigzag side (n+3)) (zigzag side n)
      (zigzag_in_strip P side (n+1) (by omega)) (zigzag_in_strip P side (n+3) hn)
      (zigzag_in_strip P side n (by omega)) (zigzag_nonzero side (n+1) (by omega))
      (zigzag_nonzero side (n+3) (by omega)) (zigzag_nonzero side n (by omega))
      (zigzag_skip_unit side (n+1)) (unit_symm _ _ (zigzag_unit side n)) he
    exact zigzag_three_ne side n hh

theorem trace_forced (P : Parameters) (hprim : Primitive P.k P.l) (side : Bool) :
    ForcedPrefix (graph P.k P.l) (trace P hprim side) (bound P side) :=
  ⟨trace_adjacent P hprim side,trace_skip P hprim side,trace_no_backtrack P hprim side⟩

theorem trace_repetition (P : Parameters) (hprim : Primitive P.k P.l) (side : Bool) :
    trace P hprim side (bound P side)=trace P hprim side (earlier P side) := by
  have h := zigzag_indices_order P side
  rw [trace_strip P hprim side (bound P side) (by omega) le_rfl,
    trace_strip P hprim side (earlier P side) h.2.1 h.2.2.le]
  have hH : InStrip P (H P (zigzag side (earlier P side))) := by
    rw [zigzag_return]; exact zigzag_in_strip P side _ le_rfl
  have hHn : H P (zigzag side (earlier P side))≠(0,0) := by
    rw [zigzag_return]; exact zigzag_nonzero side _ (by omega)
  have hh := strip_return P hprim (zigzag side (earlier P side))
    (zigzag_in_strip P side _ h.2.2.le) (zigzag_nonzero side _ h.2.1) hH hHn (zigzag_earlier_belt P side)
  simpa only [zigzag_return] using hh

theorem no_path_from_start (P : Parameters) (hprim : Primitive P.k P.l) (side : Bool) :
    ¬PathFromTriangle (startTriangle (params_positive P).2 (params_positive P).1 (startDart side) side) := by
  have hobs := repetition_obstructs (graph P.k P.l)
    (two_common_neighbors (params_positive P).2 (params_positive P).1 hprim)
    (trace P hprim side) (bound P side) (earlier P side) (trace_forced P hprim side)
    (trace_degree P hprim side) (zigzag_indices_order P side).2.2 (trace_repetition P hprim side).symm
  rintro ⟨n,p,hp,h0,h1,h2⟩
  apply hobs
  refine ⟨n,p,hp,?_,?_,?_⟩
  · simpa only [startTriangle,start_parent,trace_zero] using h0
  · simpa only [startTriangle,trace_one] using h1
  · simpa only [startTriangle,start_third,trace_two] using h2

theorem no_representative (P : Parameters) (hprim : Primitive P.k P.l) (side : Bool) :
    ¬PathFromTriangle (representative (params_positive P).2 (params_positive P).1 side) := by
  intro hp
  have hh := map_path_from (rotationGraphIso (startDart side)) _ hp
  rw [representative,rotate_startTriangle,rotate_root] at hh
  exact no_path_from_start P hprim side hh

theorem no_research_path (P : Parameters) (hprim : Primitive P.k P.l) :
    ¬∃ n p, ClaudeChallenge.LiteralPath (graph P.k P.l) n p := by
  rw [all_paths_iff_two_starts (params_positive P).2 (params_positive P).1 hprim]
  rintro ⟨side,hp⟩
  exact no_representative P hprim side hp

/-- An unconditional negative theorem about the independently defined Challenge graph. -/
theorem no_challenge_path (P : Parameters) (hprim : Primitive P.k P.l) :
    ¬∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph P.k P.l) n p := by
  rw [challenge_paths_iff_two_starts (params_positive P).2 (params_positive P).1 hprim]
  rintro ⟨side,hp⟩
  exact no_representative P hprim side hp

end R002.GCSector
