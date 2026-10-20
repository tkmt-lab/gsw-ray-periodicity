import Formal.GCSectorReturn

/-! Two explicit zigzags and the finite indices at which the return repeats a vertex. -/
namespace R002.GCSector
open GCPrimitive

def zigzag (side : Bool) (n : ℕ) : Lattice :=
  if n%2=0 then (↑(n/2:ℕ),0) else if side then (↑(n/2:ℕ),1) else ((↑(n/2:ℕ):ℤ)+1,-1)

theorem zigzag_even (side : Bool) (t : ℕ) : zigzag side (2*t)=((t:ℤ),0) := by
  simp [zigzag]
theorem zigzag_odd (side : Bool) (t : ℕ) :
    zigzag side (2*t+1)=if side then ((t:ℤ),1) else ((t:ℤ)+1,-1) := by
  unfold zigzag
  rw [show (2*t+1)%2=1 by omega,show (2*t+1)/2=t by omega]
  simp

theorem index_parity (n : ℕ) : ∃ t, n=2*t ∨ n=2*t+1 := by
  refine ⟨n/2,?_⟩
  omega

theorem zigzag_unit (side : Bool) (n : ℕ) : Unit (zigzag side n) (zigzag side (n+1)) := by
  obtain ⟨t,rfl|rfl⟩ := index_parity n
  · rw [zigzag_even,zigzag_odd]
    cases side
    · exact ⟨5,by ext <;> simp [direction]⟩
    · exact ⟨1,by ext <;> simp [direction]⟩
  · have he : 2*t+1+1=2*(t+1) := by omega
    rw [he,zigzag_even,zigzag_odd]
    cases side
    · exact ⟨1,by ext <;> simp [direction]⟩
    · exact ⟨5,by ext <;> simp [direction]⟩

theorem zigzag_skip_unit (side : Bool) (n : ℕ) : Unit (zigzag side n) (zigzag side (n+2)) := by
  obtain ⟨t,rfl|rfl⟩ := index_parity n
  · have he : 2*t+2=2*(t+1) := by omega
    rw [he,zigzag_even,zigzag_even]
    exact ⟨0,by ext <;> simp [direction]⟩
  · have he : 2*t+1+2=2*(t+1)+1 := by omega
    rw [he,zigzag_odd,zigzag_odd]
    cases side <;> exact ⟨0,by ext <;> simp [direction]⟩

theorem zigzag_three_ne (side : Bool) (n : ℕ) : zigzag side (n+3)≠zigzag side n := by
  obtain ⟨t,rfl|rfl⟩ := index_parity n
  · have he : 2*t+3=2*(t+1)+1 := by omega
    rw [he,zigzag_even,zigzag_odd]
    cases side <;> simp
  · have he : 2*t+1+3=2*(t+2) := by omega
    rw [he,zigzag_even,zigzag_odd]
    cases side <;> simp

theorem zigzag_nonzero (side : Bool) (n : ℕ) (hn : 0<n) : zigzag side n≠(0,0) := by
  obtain ⟨t,rfl|rfl⟩ := index_parity n
  · rw [zigzag_even]; intro he; have hh := congrArg Prod.fst he; dsimp at hh; omega
  · rw [zigzag_odd]; cases side <;> simp

def bound (P : Parameters) (side : Bool) : ℕ :=
  if side then (2*P.K-1).toNat else (2*P.K-2).toNat
def earlier (P : Parameters) (side : Bool) : ℕ :=
  if side then (2*P.J-2).toNat else (2*P.J-1).toNat

theorem bound_cast (P : Parameters) (side : Bool) :
    (bound P side : ℤ)=if side then 2*P.K-1 else 2*P.K-2 := by
  have := indices_order P
  cases side <;> simp [bound] <;> omega
theorem earlier_cast (P : Parameters) (side : Bool) :
    (earlier P side : ℤ)=if side then 2*P.J-2 else 2*P.J-1 := by
  have := indices_order P
  cases side <;> simp [earlier] <;> omega
theorem zigzag_indices_order (P : Parameters) (side : Bool) :
    4≤bound P side ∧ 0<earlier P side ∧ earlier P side<bound P side := by
  have hb := bound_cast P side
  have he := earlier_cast P side
  have h := indices_order P
  cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hb he <;> omega

theorem zigzag_in_strip (P : Parameters) (side : Bool) (n : ℕ) (hn : n≤bound P side) :
    InStrip P (zigzag side n) := by
  have hb := bound_cast P side
  obtain ⟨t,rfl|rfl⟩ := index_parity n
  · rw [zigzag_even]
    cases side <;> dsimp [InStrip] <;> simp only [ite_true,Bool.false_eq_true,ite_false] at hb <;> omega
  · rw [zigzag_odd]
    cases side <;> dsimp [InStrip] <;> simp only [ite_true,Bool.false_eq_true,ite_false] at hb <;> omega

theorem zigzag_bound (P : Parameters) (side : Bool) :
    zigzag side (bound P side)=if side then (P.K-1,1) else (P.K-1,0) := by
  have hb := bound_cast P side
  have hk := indices_order P
  cases side
  · have he : bound P false=2*(P.K-1).toNat := by simp only [Bool.false_eq_true,ite_false] at hb; omega
    rw [he,zigzag_even]; simp; omega
  · have he : bound P true=2*(P.K-1).toNat+1 := by simp only [ite_true] at hb; omega
    rw [he,zigzag_odd]; simp; omega

theorem zigzag_earlier (P : Parameters) (side : Bool) :
    zigzag side (earlier P side)=if side then (P.J-1,0) else (P.J,-1) := by
  have he := earlier_cast P side
  have hj := indices_order P
  cases side
  · have hh : earlier P false=2*(P.J-1).toNat+1 := by simp only [Bool.false_eq_true,ite_false] at he; omega
    rw [hh,zigzag_odd]; simp; omega
  · have hh : earlier P true=2*(P.J-1).toNat := by simp only [ite_true] at he; omega
    rw [hh,zigzag_even]; simp; omega

theorem zigzag_return (P : Parameters) (side : Bool) :
    H P (zigzag side (earlier P side))=zigzag side (bound P side) := by
  rw [zigzag_earlier,zigzag_bound]
  cases side
  · exact lower_collision P
  · exact upper_collision P

theorem zigzag_earlier_belt (P : Parameters) (side : Bool) : Belt P (zigzag side (earlier P side)) := by
  rw [zigzag_earlier]
  cases side
  · exact (earlier_points_in_belt P).2
  · exact (earlier_points_in_belt P).1

end R002.GCSector
