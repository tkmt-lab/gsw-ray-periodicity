import Formal.GCPrimitiveCoverage
import Formal.GCPrimitiveSurfaceSpec
import Formal.GCPrimitiveFanDirect

namespace R002.GCPrimitive
open Icosahedron (Corner)

theorem unframe_frame (k l : ℤ) (e : Corner) (p : Lattice) :
    unframe k l e (frame k l e p)=p := by
  fin_cases e <;> simp [frame,unframe,turn_three]

theorem frame_unframe (k l : ℤ) (e : Corner) (p : Lattice) :
    frame k l e (unframe k l e p)=p := by
  fin_cases e <;> simp [frame,unframe,turn_three]

theorem frame_injective (k l : ℤ) (e : Corner) : Function.Injective (frame k l e) :=
  (show Function.LeftInverse (unframe k l e) (frame k l e) from unframe_frame k l e).injective

theorem closed_frame (k l : ℤ) (e : Corner) (p : Lattice) :
    Closed k l (frame k l e p) ↔ Closed k l p := by
  fin_cases e <;> simp [frame,closed_turn]

theorem interior_frame (k l : ℤ) (e : Corner) (p : Lattice) :
    Interior k l (frame k l e p) ↔ Interior k l p := by
  fin_cases e <;> simp [frame,interior_turn]

theorem interior_unframe (k l : ℤ) (e : Corner) (p : Lattice) :
    Interior k l (unframe k l e p) ↔ Interior k l p := by
  fin_cases e <;> simp [unframe,interior_turn]

theorem frame_unit (k l : ℤ) (e : Corner) (p q : Lattice) :
    Unit (frame k l e p) (frame k l e q) ↔ Unit p q := by
  have forward : ∀ e p q, Unit p q → Unit (frame k l e p) (frame k l e q) := by
    intro e p q h
    fin_cases e <;> simp only [frame,Fin.isValue]
    · exact h
    · exact unit_turn k l _ _ (unit_turn k l p q h)
    · exact unit_turn k l p q h
  constructor
  · intro h
    fin_cases e
    · simpa [frame] using h
    · have hh := unit_turn k l _ _ h
      simpa [frame,turn_three] using hh
    · have hh := unit_turn k l _ _ (unit_turn k l _ _ h)
      simpa [frame,turn_three] using hh
  · exact forward e p q

theorem b_frames (k l : ℤ) (p : Lattice) :
    b k l (frame k l 0 p)=b k l p ∧
    b k l (frame k l 1 p)=c k l p ∧
    b k l (frame k l 2 p)=a k l p := by
  simp [frame,(turn_slices k l p).2.1,(turn_slices k l p).1,
    (turn_slices k l (turn k l p)).2.1]

theorem outside_has_negative (k l : ℤ) (q : Lattice) (hq : ¬Closed k l q) :
    ∃ e : Corner, b k l (frame k l e q)<0 := by
  by_cases hb : b k l q<0
  · exact ⟨0,by simpa [frame] using hb⟩
  by_cases hc : c k l q<0
  · exact ⟨1,by rw [(b_frames k l q).2.1]; exact hc⟩
  refine ⟨2,?_⟩
  rw [(b_frames k l q).2.2]
  dsimp [Closed] at hq
  omega

/-- This rules out the proposed second crossing, in integer coordinates. -/
theorem unit_step_covered (k l : ℤ) (hk : 0<k) (hl : 0<l)
    (p q : Lattice) (hp : Interior k l p) (hu : Unit p q) :
    Closed k l q ∨ ∃ e : Corner, Interior k l (opposite k l (frame k l e q)) := by
  by_cases hq : Closed k l q
  · exact Or.inl hq
  right
  obtain ⟨e,he⟩ := outside_has_negative k l q hq
  exact ⟨e,negative_b_lands k l hk hl _ _ ((interior_frame k l e p).mpr hp)
    ((frame_unit k l e p q).mpr hu) he⟩

theorem neighbor_unique_negative (k l : ℤ) (q : Lattice) (e d : Corner)
    (he : Interior k l (opposite k l (frame k l e q))) :
    b k l (frame k l d q)<0 ↔ d=e := by
  have ht := turn_slices k l q
  have htt := turn_slices k l (turn k l q)
  rw [opposite_interior] at he
  fin_cases e <;> fin_cases d <;>
    simp [frame,ht.1,ht.2.1,ht.2.2,htt.1,htt.2.1] at he ⊢ <;>
    dsimp [c] at * <;> omega

theorem adjacent_chart_unique (k l : ℤ) (q : Lattice) (e d : Corner)
    (he : Interior k l (opposite k l (frame k l e q)))
    (hd : Interior k l (opposite k l (frame k l d q))) : d=e :=
  (neighbor_unique_negative k l q e d he).mp ((opposite_interior k l _).mp hd).2.1

theorem neighbor_not_closed (k l : ℤ) (q : Lattice) (e : Corner)
    (he : Interior k l (opposite k l (frame k l e q))) : ¬Closed k l q := by
  intro hc
  have hb := ((closed_frame k l e q).mpr hc).2.1
  have hn := ((opposite_interior k l _).mp he).2.1
  omega

theorem corner_closed (k l : ℤ) (hk : 0<k) (hl : 0≤l) (e : Corner) :
    Closed k l (corner k l e) := by
  have hT := norm_pos k l hk hl
  fin_cases e <;> dsimp [corner,Closed,A,B,a,b,c,norm] at * <;>
    refine ⟨?_,?_,?_⟩ <;> nlinarith

theorem corner_not_interior (k l : ℤ) (e : Corner) : ¬Interior k l (corner k l e) := by
  fin_cases e <;> simp [corner,Interior,A,B,a,b,c,norm] <;> ring_nf <;> omega

theorem corner_injective (k l : ℤ) (hk : 0<k) (hl : 0<l) :
    Function.Injective (corner k l) := by
  intro e d h
  have hx := congrArg Prod.fst h
  fin_cases e <;> fin_cases d <;> simp [corner,A,B] at hx ⊢ <;> omega

/-- A corner has just one unit neighbor in each incident closed face. -/
theorem closed_origin_fan (k l : ℤ) (hkl : l<k) (hl : 0<l) (p : Lattice) :
    Closed k l p ∧ Unit (0,0) p ↔ p=(0,1) := by
  constructor
  · rintro ⟨hp,i,rfl⟩
    fin_cases i <;> norm_num [Closed,a,b,c,norm,direction] at hp ⊢ <;> omega
  · rintro rfl
    exact ⟨interior_closed k l _ (origin_winner k l hkl hl).1,(origin_winner k l hkl hl).2⟩

end R002.GCPrimitive
