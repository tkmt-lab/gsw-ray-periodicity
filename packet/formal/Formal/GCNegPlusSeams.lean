import Formal.GCNegNearDarts

namespace R002.GCNeg
open Icosahedron GCSector

theorem plus_seams (P : TailParameters) (t : Tile) (e : Corner)
    (ht : PlusActive P t) (hu : PlusActive P (tileNeighbor t e)) :
    Compatible (plusDart P t) e (plusDart P (tileNeighbor t e)) (tileMateCorner t e) := by
  have ha := P.ha
  rcases t with ⟨i,j,s⟩
  rcases ht with ⟨hi,hj,hs⟩|⟨hi,hj⟩|⟨hj0,hj1,hm0,hm1⟩|⟨hi,hj0,hj1⟩
  · dsimp at hi hj hs; subst i; subst j; subst s
    fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
    · simp [PlusActive] at hu <;> omega
    · rw [plus_top,plus_reg P 0 (-1) (by omega) (by omega) (by omega) (by omega)]
      simpa [psi_zero] using top_band
    · simp [PlusActive] at hu <;> omega
  · dsimp at hi hj; subst i; subst j
    cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
    · simp [PlusActive] at hu <;> omega
    · rw [plus_lower,plus_lower]; exact band_diag _
    · simp [PlusActive] at hu <;> omega
    · rw [plus_lower,plus_lower]; exact band_diag_rev _
    · simp [PlusActive] at hu <;> omega
    · rw [plus_lower,plus_reg P 0 (-1) (by omega) (by omega) (by omega) (by omega)]
      simpa [psi_zero] using band_right (-1)
  · dsimp at hj0 hj1 hm0 hm1
    cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
    · rw [plus_reg P i j hj0 hj1 hm0 hm1]
      by_cases hm : i+2*j= -2
      · have he : i=0 ∧ j= -1 := by simp [PlusActive] at hu <;> omega
        rcases he with ⟨rfl,rfl⟩
        norm_num only
        rw [plus_lower]
        simpa [psi_zero] using band_left 0
      · rw [plus_reg P (i-1) j hj0 hj1 (by omega) (by omega)]
        have hc : ((i-1+2*j+2:ℤ):ZMod 5)=((i+2*j+2:ℤ):ZMod 5)-1 := by push_cast; ring
        rw [hc]; exact psi_compatible _ _ _ _ _ (band_left _)
    · rw [plus_reg P i j hj0 hj1 hm0 hm1,plus_reg P i j hj0 hj1 hm0 hm1]
      exact psi_compatible _ _ _ _ _ (band_diag _)
    · have hm : i+2*j= -2 := by simp [PlusActive] at hu <;> omega
      rw [plus_reg P i j hj0 hj1 hm0 hm1]
      by_cases hj : j= -1
      · have hi : i=0 := by omega
        subst i; subst j
        norm_num only
        rw [plus_top]
        simpa [psi_zero] using band_top
      · rw [plus_reg P i (j+1) (by omega) (by omega) (by omega) (by omega),psi_index_up]
        have h0 : i+2*j+2=0 := by omega
        have h2 : i+2*(j+1)+2=2 := by omega
        rw [h0,h2]
        simpa using psi_wrap_rev ((-j-1:ℤ):ZMod 2)
    · rw [plus_reg P i j hj0 hj1 hm0 hm1,plus_reg P i j hj0 hj1 hm0 hm1]
      exact psi_compatible _ _ _ _ _ (band_diag_rev _)
    · have hm : i+2*j=0 := by simp [PlusActive] at hu <;> omega
      have hjq : -P.a-1<j := by simp [PlusActive] at hu <;> omega
      rw [plus_reg P i j hj0 hj1 hm0 hm1,plus_reg P i (j-1) (by omega) (by omega) (by omega) (by omega),psi_index_down]
      have h2 : i+2*j+2=2 := by omega
      have h0 : i+2*(j-1)+2=0 := by omega
      rw [h2,h0]
      simpa using psi_wrap ((-j-1:ℤ):ZMod 2)
    · rw [plus_reg P i j hj0 hj1 hm0 hm1]
      by_cases hm : i+2*j=0
      · have he : i=2*P.a+2 ∧ j= -P.a-1 := by simp [PlusActive] at hu <;> omega
        rcases he with ⟨rfl,rfl⟩
        rw [show 2*P.a+2+1=2*P.a+3 by ring,plus_cap0]
        have hi : -(↑(-P.a-1):ZMod 2)-1=(P.a:ZMod 2) := by push_cast; ring
        have hc : 2*P.a+2+2*(-P.a-1)+2=2 := by ring
        rw [hi,hc]
        simpa [gDart,Int.cast_add] using psi_terminal ((P.a:ZMod 2)+1)
      · rw [plus_reg P (i+1) j hj0 hj1 (by omega) (by omega)]
        have hc : ((i+1+2*j+2:ℤ):ZMod 5)=((i+2*j+2:ℤ):ZMod 5)+1 := by push_cast; ring
        rw [hc]; exact psi_compatible _ _ _ _ _ (band_right _)
  · dsimp at hi hj0 hj1; subst i
    have hj : j= -P.a-1 ∨ j= -P.a-2 := by omega
    rcases hj with rfl|rfl
    · cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
      · rw [show 2*P.a+3-1=2*P.a+2 by ring,plus_cap0,plus_reg P (2*P.a+2) (-P.a-1) (by omega) (by omega) (by omega) (by omega)]
        have hi : -(↑(-P.a-1):ZMod 2)-1=(P.a:ZMod 2) := by push_cast; ring
        have hc : 2*P.a+2+2*(-P.a-1)+2=2 := by ring
        rw [hi,hc]
        simpa [gDart,Int.cast_add] using psi_terminal_rev ((P.a:ZMod 2)+1)
      · rw [plus_cap0,plus_cap0]; exact (psi_caps _).1
      · simp [PlusActive] at hu <;> omega
      · rw [plus_cap0,plus_cap0]; exact (psi_caps _).2.1
      · rw [show -P.a-1-1= -P.a-2 by ring,plus_cap0,plus_cap1]; exact (psi_caps _).2.2.1
      · simp [PlusActive] at hu <;> omega
    · cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
      · simp [PlusActive] at hu <;> omega
      · rw [plus_cap1,plus_cap1]; exact (psi_caps _).2.2.2.2.1
      · rw [show -P.a-2+1= -P.a-1 by ring,plus_cap1,plus_cap0]; exact (psi_caps _).2.2.2.1
      · rw [plus_cap1,plus_cap1]; exact (psi_caps _).2.2.2.2.2
      · simp [PlusActive] at hu <;> omega
      · simp [PlusActive] at hu <;> omega

end R002.GCNeg
