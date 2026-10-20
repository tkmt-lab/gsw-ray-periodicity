import Formal.GCNegAtlas

namespace R002.GCNeg
open GCPrimitive GCSector Icosahedron

/-- A Euclidean remainder bounded away from ±1 rules out every coarse vertex in the rectangle. -/
theorem rectangle_zero (r t B T X : ℤ) (hr : 4≤r) (ht : 2≤t) (htr : t≤r-2)
    (hB : 0≤B) (hT : B<T) (hgap : r*X+B<2*T)
    (p : Lattice) (hp : Region X p) (c d : ℤ)
    (h1 : r*p.1+B*p.2=T*c) (h2 : p.2=t*c+r*d) : p=(0,0) := by
  have hTp : 0<T := by omega
  have hx0 := mul_nonneg (show 0≤r by omega) hp.1
  have hx1 := mul_le_mul_of_nonneg_left hp.2.1 (show 0≤r by omega)
  have hy0 := mul_le_mul_of_nonneg_left hp.2.2.1 hB
  have hy1 := mul_le_mul_of_nonneg_left hp.2.2.2 hB
  have hc0 : 0≤c := by
    by_contra hc
    have hh := mul_le_mul_of_nonneg_left (show c≤ -1 by omega) hTp.le
    nlinarith
  have hc1 : c≤1 := by
    by_contra hc
    have hh := mul_le_mul_of_nonneg_left (show 2≤c by omega) hTp.le
    nlinarith
  by_cases hc : c=0
  · have hd : d=0 := by
      rcases lt_trichotomy d 0 with hd|hd|hd
      · have hh := mul_le_mul_of_nonneg_left (show d≤ -1 by omega) (show 0≤r by omega)
        rw [hc] at h2; nlinarith [hp.2.2.1]
      · exact hd
      · have hh := mul_le_mul_of_nonneg_left (show 1≤d by omega) (show 0≤r by omega)
        rw [hc] at h2; nlinarith [hp.2.2.2]
    have hy : p.2=0 := by rw [hc,hd] at h2; simpa using h2
    have hx : p.1=0 := by rw [hc,hy] at h1; nlinarith
    exact Prod.ext hx hy
  · have hc : c=1 := by omega
    rw [hc] at h2
    exact False.elim (no_positive_strip r (-d) (by omega)
      (by nlinarith [hp.2.2.2]) (by nlinarith [hp.2.2.1]))

theorem closed_interior_of_no_coarse (k l X : ℤ) (hk : 0<k) (hl : 0<l) (hprim : Primitive k l)
    (H : ∀ u v, Region X (A3.gc k l u v) → A3.gc k l u v=(0,0))
    (p : Lattice) (hp : Region X p) (hn : p≠(0,0)) (t : Tile)
    (ht : Closed k l (tileLocal k l t p)) : Interior k l (tileLocal k l t p) := by
  have hnc : ∀ e, tileLocal k l t p≠corner k l e := by
    intro e he
    have hx : p=tileEmbed k l t (corner k l e) :=
      (tile_inverse k l t p).1.symm.trans (congrArg (tileEmbed k l t) he)
    obtain ⟨u,v,hv⟩ := tile_corners_coarse k l t e
    have heq := hx.trans hv
    exact hn (heq.trans (H u v (heq ▸ hp)))
  rcases closed_partition k l hk hl.le hprim _ ht with h|h|h|h
  · exact False.elim (hnc 0 h)
  · exact False.elim (hnc 1 h)
  · exact False.elim (hnc 2 h)
  · exact h

end R002.GCNeg
