import Formal.GCNegPlusSeams

namespace R002.GCNeg
open Icosahedron GCSector

theorem chi_above (j : ℤ) : -(↑(j+1):ZMod 2)-1= -↑j-2 := by push_cast; ring
theorem chi_below (j : ℤ) : -(↑(j-1):ZMod 2)-2= -↑j-1 := by push_cast; ring
theorem chi_step (j : ℤ) : (-↑j-1:ZMod 2)=(-↑j-2)+1 := by ring
theorem chi_prev (j : ℤ) : (-↑j-2:ZMod 2)=(-↑j-1)-1 := by ring

theorem minus_seams (P : TailParameters) (ha2 : 2≤P.a) (t : Tile) (e : Corner)
    (ht : MinusActive P t) (hu : MinusActive P (tileNeighbor t e)) :
    Compatible (minusDart P t) e (minusDart P (tileNeighbor t e)) (tileMateCorner t e) := by
  rcases t with ⟨i,j,s⟩
  rcases ht with ⟨hi,hj,hs⟩|⟨hi,hj⟩|⟨hi,hj⟩|⟨hj0,hj1,hm⟩|⟨hj0,hj1,hm⟩|⟨hj,hi⟩
  · dsimp at hi hj hs; subst i; subst j; subst s
    fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
    · simp [MinusActive] at hu <;> omega
    · rw [minus_top,minus_initial]; exact top_band
    · simp [MinusActive] at hu <;> omega
  · dsimp at hi hj; subst i; subst j
    cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
    · simp [MinusActive] at hu <;> omega
    · rw [minus_lower,minus_lower]; exact band_diag _
    · simp [MinusActive] at hu <;> omega
    · rw [minus_lower,minus_lower]; exact band_diag_rev _
    · simp [MinusActive] at hu <;> omega
    · rw [minus_lower,minus_initial]; simpa using band_right (-1)
  · dsimp at hi hj; subst i; subst j
    cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
    · rw [minus_initial,minus_lower]; exact band_left 0
    · rw [minus_initial,minus_initial]; exact band_diag 0
    · rw [minus_initial,minus_top]; exact band_top
    · rw [minus_initial,minus_initial]; exact band_diag_rev 0
    · simp [MinusActive] at hu <;> omega
    · rw [minus_initial,minus_upper P 1 (-1) (by omega) (by omega) (by omega)]
      simpa [chi_zero] using chi_initial.1
  · dsimp at hj0 hj1 hm
    cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
    · rw [minus_upper P i j hj0 hj1 hm]
      by_cases hj : j= -1
      · have hi : i=1 := by omega
        subst i; subst j
        norm_num only
        rw [minus_initial]
        simpa [chi_zero] using chi_initial.2
      · rw [minus_bottom P (i-1) j (-2) (by omega) (by omega) (by omega) (Or.inr rfl),chi_prev]
        exact (chi_seams _).2.2.2.2.2
    · rw [minus_upper P i j hj0 hj1 hm,minus_upper P i j hj0 hj1 hm]
      exact chi_compatible _ _ _ _ _ (minus_diag (-1) (by simp)).1
    · simp [MinusActive] at hu <;> omega
    · rw [minus_upper P i j hj0 hj1 hm,minus_upper P i j hj0 hj1 hm]
      exact chi_compatible _ _ _ _ _ (minus_diag (-1) (by simp)).2
    · rw [minus_upper P i j hj0 hj1 hm,minus_bottom P i (j-1) (-3) (by omega) (by omega) (by omega) (Or.inl rfl),chi_below]
      exact (chi_seams _).1
    · simp [MinusActive] at hu <;> omega
  · dsimp at hj0 hj1 hm
    rcases hm with hm|hm
    · cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
      · simp [MinusActive] at hu <;> omega
      · rw [minus_bottom P i j (-3) hj0 hj1 hm (Or.inl rfl),minus_bottom P i j (-3) hj0 hj1 hm (Or.inl rfl)]
        exact chi_compatible _ _ _ _ _ (minus_diag (-3) (by simp)).1
      · rw [minus_bottom P i j (-3) hj0 hj1 hm (Or.inl rfl),minus_upper P i (j+1) (by omega) (by omega) (by omega),chi_above]
        exact (chi_seams _).2.1
      · rw [minus_bottom P i j (-3) hj0 hj1 hm (Or.inl rfl),minus_bottom P i j (-3) hj0 hj1 hm (Or.inl rfl)]
        exact chi_compatible _ _ _ _ _ (minus_diag (-3) (by simp)).2
      · simp [MinusActive] at hu <;> omega
      · rw [minus_bottom P i j (-3) hj0 hj1 hm (Or.inl rfl),minus_bottom P (i+1) j (-2) hj0 hj1 (by omega) (Or.inr rfl)]
        exact (chi_seams _).2.2.1
    · cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
      · rw [minus_bottom P i j (-2) hj0 hj1 hm (Or.inr rfl),minus_bottom P (i-1) j (-3) hj0 hj1 (by omega) (Or.inl rfl)]
        exact (chi_seams _).2.2.2.1
      · rw [minus_bottom P i j (-2) hj0 hj1 hm (Or.inr rfl),minus_bottom P i j (-2) hj0 hj1 hm (Or.inr rfl)]
        exact chi_compatible _ _ _ _ _ (minus_diag (-2) (by simp)).1
      · simp [MinusActive] at hu <;> omega
      · rw [minus_bottom P i j (-2) hj0 hj1 hm (Or.inr rfl),minus_bottom P i j (-2) hj0 hj1 hm (Or.inr rfl)]
        exact chi_compatible _ _ _ _ _ (minus_diag (-2) (by simp)).2
      · have he : i=2*P.a ∧ j= -P.a-1 := by simp [MinusActive] at hu <;> omega
        rcases he with ⟨rfl,rfl⟩
        rw [show -P.a-1-1= -P.a-2 by ring,minus_bottom P (2*P.a) (-P.a-1) (-2) (by omega) (by omega) (by omega) (Or.inr rfl),minus_cap0 P ha2]
        have hn : -(↑(-P.a-1):ZMod 2)-2=(P.a:ZMod 2)-1 := by push_cast; ring
        rw [hn]; exact (chi_terminal _).1
      · have hjq : -P.a≤j := by simp [MinusActive] at hu <;> omega
        rw [minus_bottom P i j (-2) hj0 hj1 hm (Or.inr rfl),minus_upper P (i+1) j hjq (by omega) (by omega),chi_step]
        exact (chi_seams _).2.2.2.2.1
  · dsimp at hj hi; subst j
    rcases hi with rfl|rfl
    · cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
      · simp [MinusActive] at hu <;> omega
      · rw [minus_cap0 P ha2,minus_cap0 P ha2]; exact (chi_caps _).1
      · rw [show -P.a-2+1= -P.a-1 by ring,minus_cap0 P ha2,minus_bottom P (2*P.a) (-P.a-1) (-2) (by omega) (by omega) (by omega) (Or.inr rfl)]
        have hn : -(↑(-P.a-1):ZMod 2)-2=(P.a:ZMod 2)-1 := by push_cast; ring
        rw [hn]; exact (chi_terminal _).2
      · rw [minus_cap0 P ha2,minus_cap0 P ha2]; exact (chi_caps _).2.1
      · simp [MinusActive] at hu <;> omega
      · rw [minus_cap0 P ha2,minus_cap1 P ha2]; exact (chi_caps _).2.2.1
    · cases s <;> fin_cases e <;> simp [tileNeighbor,tileMateCorner] at hu ⊢
      · rw [minus_cap1 P ha2,minus_cap0 P ha2]; exact (chi_caps _).2.2.2.1
      · rw [minus_cap1 P ha2,minus_cap1 P ha2]; exact (chi_caps _).2.2.2.2.1
      · simp [MinusActive] at hu <;> omega
      · rw [minus_cap1 P ha2,minus_cap1 P ha2]; exact (chi_caps _).2.2.2.2.2
      · simp [MinusActive] at hu <;> omega
      · simp [MinusActive] at hu <;> omega

end R002.GCNeg
