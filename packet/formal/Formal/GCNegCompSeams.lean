import Formal.GCNegCompLabels

namespace R002.GCNeg
open Icosahedron GCPrimitive GCPrimitiveSurface GCSector

theorem comp_reg0 (P : Parameters) (i j : ℤ) (h0 : -P.q≤j) (h1 : j≤ -1)
    (h : i+j= -1) (s : Bool) : compDart P ⟨i,j,s⟩=phase3 (-j-1) (bandDart 0 s) := by
  have hi : i= -j-1 := by omega
  subst i; exact comp_dart_reg0 P j h0 h1 s
theorem comp_reg1 (P : Parameters) (i j : ℤ) (h0 : -P.q≤j) (h1 : j≤ -1)
    (h : i+j=0) (s : Bool) : compDart P ⟨i,j,s⟩=phase3 (-j-1) (bandDart 1 s) := by
  have hi : i= -j := by omega
  subst i; exact comp_dart_reg1 P j h0 h1 s

theorem comp_seams (P : Parameters) (t : Tile) (e : Corner)
    (ht : CompActive P t) (hu : CompActive P (tileNeighbor t e)) :
    Compatible (compDart P t) e (compDart P (tileNeighbor t e)) (tileMateCorner t e) := by
  have hq := P.hq
  rcases t with ⟨i,j,s⟩
  rcases ht with ⟨hi,hj,hs⟩|⟨hi,hj⟩|⟨hj0,hj1,hij⟩|⟨hi,hj0,hj1⟩
  · dsimp at hi hj hs
    subst i; subst j; subst s
    fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
    · simp [CompActive] at hu <;> omega
    · rw [comp_dart_top,comp_reg0 P 0 (-1) (by omega) (by omega) (by omega)]
      norm_num only [Int.cast_neg,Int.cast_one,phase3_zero]
      exact top_band
    · simp [CompActive] at hu <;> omega
  · dsimp at hi hj
    subst i; subst j
    cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
    · simp [CompActive] at hu <;> omega
    · rw [comp_dart_lower,comp_dart_lower]; exact band_diag _
    · simp [CompActive] at hu <;> omega
    · rw [comp_dart_lower,comp_dart_lower]; exact band_diag_rev _
    · simp [CompActive] at hu <;> omega
    · rw [comp_dart_lower,comp_reg0 P 0 (-1) (by omega) (by omega) (by omega)]
      norm_num only [Int.cast_neg,Int.cast_one,phase3_zero]
      simpa using band_right (-1)
  · dsimp at hj0 hj1 hij
    rcases hij with hij|hij
    · cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
      · have hji : j= -1 ∧ i=0 := by simp [CompActive] at hu <;> omega
        rcases hji with ⟨rfl,rfl⟩
        rw [comp_reg0 P 0 (-1) (by omega) (by omega) (by omega)]
        norm_num only [Int.cast_neg,Int.cast_one,phase3_zero]
        rw [comp_dart_lower]
        simpa using band_left 0
      · rw [comp_reg0 P i j hj0 hj1 hij,comp_reg0 P i j hj0 hj1 hij]
        exact phase3_compatible _ _ _ _ _ (band_diag 0)
      · rw [comp_reg0 P i j hj0 hj1 hij]
        by_cases hj : j= -1
        · have hi : i=0 := by omega
          subst i; subst j
          norm_num only [Int.cast_neg,Int.cast_one,phase3_zero]
          rw [comp_dart_top]; exact band_top
        · rw [comp_reg1 P i (j+1) (by omega) (by omega) (by omega),index_up]
          exact comp_wrap_rev _
      · rw [comp_reg0 P i j hj0 hj1 hij,comp_reg0 P i j hj0 hj1 hij]
        exact phase3_compatible _ _ _ _ _ (band_diag_rev 0)
      · simp [CompActive] at hu <;> omega
      · rw [comp_reg0 P i j hj0 hj1 hij,comp_reg1 P (i+1) j hj0 hj1 (by omega)]
        simpa using phase3_compatible ((-j-1:ℤ):ZMod 3) _ _ _ _ (band_right 0)
    · cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
      · rw [comp_reg1 P i j hj0 hj1 hij,comp_reg0 P (i-1) j hj0 hj1 (by omega)]
        simpa using phase3_compatible ((-j-1:ℤ):ZMod 3) _ _ _ _ (band_left 1)
      · rw [comp_reg1 P i j hj0 hj1 hij,comp_reg1 P i j hj0 hj1 hij]
        exact phase3_compatible _ _ _ _ _ (band_diag 1)
      · simp [CompActive] at hu <;> omega
      · rw [comp_reg1 P i j hj0 hj1 hij,comp_reg1 P i j hj0 hj1 hij]
        exact phase3_compatible _ _ _ _ _ (band_diag_rev 1)
      · have hjq : -P.q<j := by simp [CompActive] at hu <;> omega
        rw [comp_reg1 P i j hj0 hj1 hij,comp_reg0 P i (j-1) (by omega) (by omega) (by omega),index_down]
        exact comp_wrap _
      · have hji : j= -P.q ∧ i=P.q := by simp [CompActive] at hu <;> omega
        rcases hji with ⟨rfl,rfl⟩
        rw [comp_reg1 P P.q (-P.q) (by omega) (by omega) (by omega),comp_dart_cap0]
        simpa [Int.cast_neg,bandDart,labelB] using comp_terminal (P.q : ZMod 3)
  · dsimp at hi hj0 hj1
    subst i
    have hj : j= -P.q ∨ j= -P.q-1 := by omega
    rcases hj with rfl|rfl
    · cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
      · rw [comp_dart_cap0,comp_reg1 P P.q (-P.q) (by omega) (by omega) (by omega)]
        simpa [Int.cast_neg,bandDart,labelB] using comp_terminal_rev (P.q : ZMod 3)
      · rw [comp_dart_cap0,comp_dart_cap0]; exact comp_cap12 _
      · simp [CompActive] at hu <;> omega
      · rw [comp_dart_cap0,comp_dart_cap0]; exact comp_cap21 _
      · rw [comp_dart_cap0,comp_dart_cap1]; exact comp_cap23 _
      · simp [CompActive] at hu <;> omega
    · cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
      · simp [CompActive] at hu <;> omega
      · rw [comp_dart_cap1,comp_dart_cap1]; exact comp_cap34 _
      · rw [comp_dart_cap1,comp_dart_cap0]; exact comp_cap32 _
      · rw [comp_dart_cap1,comp_dart_cap1]; exact comp_cap43 _
      · simp [CompActive] at hu <;> omega
      · simp [CompActive] at hu <;> omega

end R002.GCNeg
