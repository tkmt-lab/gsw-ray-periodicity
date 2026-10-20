import Formal.GCPrimitiveSpec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! Primitive parent sides and the closed-triangle partition. -/
namespace R002.GCPrimitive

theorem norm_pos (k l : ℤ) (hk : 0<k) (hl : 0≤l) : 0<norm k l := by
  dsimp [norm]
  have := mul_nonneg hk.le hl
  nlinarith [sq_nonneg l]

theorem turn_three (k l : ℤ) (p : Lattice) :
    turn k l (turn k l (turn k l p))=p := by
  ext <;> dsimp [turn] <;> ring

theorem turn_slices (k l : ℤ) (p : Lattice) :
    a k l (turn k l p)=c k l p ∧
    b k l (turn k l p)=a k l p ∧
    c k l (turn k l p)=b k l p := by
  dsimp [a,b,c,norm,turn]
  constructor
  · ring
  constructor <;> ring

theorem closed_turn (k l : ℤ) (p : Lattice) :
    Closed k l (turn k l p) ↔ Closed k l p := by
  simp only [Closed,(turn_slices k l p).1,(turn_slices k l p).2.1,
    (turn_slices k l p).2.2]
  tauto

theorem interior_turn (k l : ℤ) (p : Lattice) :
    Interior k l (turn k l p) ↔ Interior k l p := by
  simp only [Interior,(turn_slices k l p).1,(turn_slices k l p).2.1,
    (turn_slices k l p).2.2]
  tauto

/-- All integral points on the primitive OA line are integer multiples of A. -/
theorem primitive_line (k l : ℤ) (hk : 0<k) (hprim : Primitive k l)
    (p : Lattice) (hline : b k l p=0) :
    ∃ j : ℤ, p=(k*j,l*j) := by
  have hd : k ∣ l*p.1 := ⟨p.2,by dsimp [b] at hline; linarith⟩
  obtain ⟨j,hj⟩ := Int.dvd_of_dvd_mul_right_of_gcd_one hd hprim
  refine ⟨j,Prod.ext hj ?_⟩
  dsimp [b] at hline
  apply mul_left_cancel₀ (ne_of_gt hk)
  nlinarith [congrArg (fun z : ℤ => l*z) hj]

/-- The closed primitive OA edge contains exactly its endpoints. -/
theorem primitive_OA (k l : ℤ) (hk : 0<k) (hl : 0≤l)
    (hprim : Primitive k l) (p : Lattice)
    (hp : Closed k l p) (hb : b k l p=0) : p=(0,0) ∨ p=A k l := by
  obtain ⟨j,rfl⟩ := primitive_line k l hk hprim p hb
  have hT := norm_pos k l hk hl
  have ha : a k l (k*j,l*j)=norm k l*j := by dsimp [a,norm]; ring
  have hc : c k l (k*j,l*j)=norm k l*(1-j) := by dsimp [a,b,c,norm]; ring
  obtain ⟨h0,_,h1⟩ := hp
  rw [ha] at h0
  rw [hc] at h1
  have hj0 : 0≤j := by nlinarith
  have hj1 : j≤1 := by nlinarith
  have hj : j=0 ∨ j=1 := by omega
  rcases hj with rfl | rfl <;> simp [A]

/-- No unlisted lattice points occur on any of the three primitive sides. -/
theorem closed_partition (k l : ℤ) (hk : 0<k) (hl : 0≤l)
    (hprim : Primitive k l) (p : Lattice) (hp : Closed k l p) :
    p=(0,0) ∨ p=A k l ∨ p=B k l ∨ Interior k l p := by
  by_cases hb : b k l p=0
  · rcases primitive_OA k l hk hl hprim p hp hb with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  by_cases ha : a k l p=0
  · have ht := (closed_turn k l p).mpr hp
    have hz : b k l (turn k l p)=0 := (turn_slices k l p).2.1.trans ha
    rcases primitive_OA k l hk hl hprim _ ht hz with h | h
    all_goals have hx := congrArg Prod.fst h
    all_goals have hy := congrArg Prod.snd h
    all_goals dsimp [turn,A] at hx hy
    · exact Or.inr (Or.inr (Or.inl (by ext <;> dsimp [B] <;> omega)))
    · exact Or.inl (by ext <;> dsimp <;> omega)
  by_cases hc : c k l p=0
  · have ht := (closed_turn k l (turn k l p)).mpr ((closed_turn k l p).mpr hp)
    have hz : b k l (turn k l (turn k l p))=0 := by
      rw [(turn_slices k l (turn k l p)).2.1,(turn_slices k l p).1,hc]
    rcases primitive_OA k l hk hl hprim _ ht hz with h | h
    all_goals have hx := congrArg Prod.fst h
    all_goals have hy := congrArg Prod.snd h
    all_goals dsimp [turn,A] at hx hy
    · exact Or.inr (Or.inl (by ext <;> dsimp [A] <;> omega))
    · exact Or.inr (Or.inr (Or.inl (by ext <;> dsimp [B] <;> omega)))
  · right; right; right
    exact ⟨lt_of_le_of_ne hp.1 (Ne.symm ha),lt_of_le_of_ne hp.2.1 (Ne.symm hb),
      lt_of_le_of_ne hp.2.2 (Ne.symm hc)⟩

end R002.GCPrimitive
