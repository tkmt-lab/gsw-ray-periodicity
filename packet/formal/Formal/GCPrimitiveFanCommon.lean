import Formal.GCPrimitiveCuts

/-! Shared statement and positive direction for the six-row corner-fan experiment. -/
namespace R002.GCPrimitive

theorem origin_winner (k l : ℤ) (hkl : l<k) (hl : 0<l) :
    Interior k l (0,1) ∧ Unit (0,0) (0,1) := by
  constructor
  · dsimp [Interior,a,b,c,norm]
    have hk : 2≤k := by omega
    have hmul := mul_nonneg (show 0≤k by omega) (show 0≤l by omega)
    constructor
    · omega
    constructor
    · omega
    · nlinarith [sq_nonneg l]
  · exact ⟨1,rfl⟩

end R002.GCPrimitive
