import Formal.GCPrimitiveFanCommon

/-! Baseline: prove the six corner-fan rows directly by arithmetic. -/
namespace R002.GCPrimitive

theorem origin_fan_direct (k l : ℤ) (hkl : l<k) (hl : 0<l) (p : Lattice) :
    Interior k l p ∧ Unit (0,0) p ↔ p=(0,1) := by
  constructor
  · rintro ⟨hp,i,rfl⟩
    fin_cases i <;> norm_num [Interior,a,b,c,norm,direction] at hp ⊢ <;> omega
  · rintro rfl
    exact origin_winner k l hkl hl

end R002.GCPrimitive
