import Formal.GCSectorCaps

/-! No parent vertex occurs in the full bounded strip of the complementary sector. -/
namespace R002.GCSector
open GCPrimitive Icosahedron

def CompStrip (P : Parameters) (p : Lattice) : Prop :=
  0≤p.1 ∧ p.1≤compA P ∧ -1≤p.2 ∧ p.2≤1

theorem comp_strip_gaps (P : Parameters) :
    0<norm P.k (compL P)-(3*P.k-P.l) ∧
    0<2*norm P.k (compL P)-P.l*compA P-(3*P.k-P.l) ∧
    0<(P.q+2)*norm P.k (compL P)-P.k*compA P-(P.k+compL P) := by
  rcases P with ⟨q,h,s,hq,hs,hsh⟩
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ q=3+u := ⟨q-3,by omega,by omega⟩
  obtain ⟨v,hv,rfl⟩ : ∃ v : ℤ, 0≤v ∧ s=2+v := ⟨s-2,by omega,by omega⟩
  obtain ⟨w,hw,rfl⟩ : ∃ w : ℤ, 0≤w ∧ h=4+v+w := ⟨h-4-v,by omega,by omega⟩
  refine ⟨?_,?_,?_⟩
  all_goals dsimp [GCPrimitive.norm,compL,compA,Parameters.k]; ring_nf; positivity

theorem comp_coarse_identity (P : Parameters) (u v : ℤ) :
    P.l*(A3.gc P.k (compL P) u v).1+(3*P.k-P.l)*(A3.gc P.k (compL P) u v).2=
      norm P.k (compL P)*(u+2*v) ∧
    (A3.gc P.k (compL P) u v).2=P.k*(u+2*v)-P.l*(u+v) := by
  constructor <;> dsimp [A3.gc,compL,GCPrimitive.norm] <;> ring

theorem comp_no_coarse (P : Parameters) (u v : ℤ) (hp : CompStrip P (A3.gc P.k (compL P) u v)) :
    A3.gc P.k (compL P) u v=(0,0) := by
  have hl := l_ge_four P
  have hk := k_ge P
  have hs := P.hs
  have hsl := P.hsl
  have ht := norm_pos P.k (compL P) (by omega) (comp_positive P).1.le
  have hg := comp_strip_gaps P
  have hc := comp_coarse_identity P u v
  have hcoef : 0≤3*P.k-P.l := by omega
  have hx0 := mul_nonneg (show 0≤P.l by omega) hp.1
  have hx1 := mul_le_mul_of_nonneg_left hp.2.1 (show 0≤P.l by omega)
  have hy0 := mul_le_mul_of_nonneg_left hp.2.2.1 hcoef
  have hy1 := mul_le_mul_of_nonneg_left hp.2.2.2 hcoef
  have hn0 : 0≤u+2*v := by
    by_contra hn
    have hh := mul_le_mul_of_nonneg_left (show u+2*v≤ -1 by omega) ht.le
    nlinarith [hc.1,hg.1]
  have hn1 : u+2*v≤1 := by
    by_contra hn
    have hh := mul_le_mul_of_nonneg_left (show 2≤u+2*v by omega) ht.le
    nlinarith [hc.1,hg.2.1]
  by_cases hz : u+2*v=0
  · have hd : u+v=0 := by
      rw [hz] at hc
      rcases lt_trichotomy (u+v) 0 with hd|hd|hd
      · have hh := mul_le_mul_of_nonneg_left (show u+v≤ -1 by omega) (show 0≤P.l by omega)
        nlinarith [hc.2,hp.2.2.2]
      · exact hd
      · have hh := mul_le_mul_of_nonneg_left (show 1≤u+v by omega) (show 0≤P.l by omega)
        nlinarith [hc.2,hp.2.2.1]
    have hu : u=0 := by omega
    have hv : v=0 := by omega
    simp [A3.gc,hu,hv]
  · have hn : u+2*v=1 := by omega
    have he : (A3.gc P.k (compL P) u v).2=P.s-P.l*(u+v-P.q) := by
      rw [hc.2,hn]; dsimp [Parameters.k]; ring
    exact False.elim (no_positive_strip P.l (u+v-P.q) (by omega)
      (by have := hp.2.2.2; linarith) (by have := hp.2.2.1; linarith))

theorem comp_not_corner (P : Parameters) (p : Lattice) (hp : CompStrip P p) (hn : p≠(0,0))
    (t : Tile) (e : Corner) : tileLocal P.k (compL P) t p≠corner P.k (compL P) e := by
  intro he
  have hx : p=tileEmbed P.k (compL P) t (corner P.k (compL P) e) :=
    (tile_inverse P.k (compL P) t p).1.symm.trans (congrArg (tileEmbed P.k (compL P) t) he)
  obtain ⟨u,v,hv⟩ := tile_corners_coarse P.k (compL P) t e
  have hpp := hx.trans hv
  exact hn (hpp.trans (comp_no_coarse P u v (hpp ▸ hp)))

theorem comp_closed_interior (P : Parameters) (hprim : Primitive P.k (compL P))
    (p : Lattice) (hp : CompStrip P p) (hn : p≠(0,0)) (t : Tile)
    (ht : Closed P.k (compL P) (tileLocal P.k (compL P) t p)) :
    Interior P.k (compL P) (tileLocal P.k (compL P) t p) := by
  have hk : 0<P.k := (comp_positive P).1.trans (comp_positive P).2
  rcases closed_partition P.k (compL P) hk (comp_positive P).1.le hprim _ ht with h|h|h|h
  · exact False.elim (comp_not_corner P p hp hn t 0 h)
  · exact False.elim (comp_not_corner P p hp hn t 1 h)
  · exact False.elim (comp_not_corner P p hp hn t 2 h)
  · exact h

theorem comp_tiles_cover (P : Parameters) (hprim : Primitive P.k (compL P))
    (p : Lattice) (hp : CompStrip P p) (hn : p≠(0,0)) :
    ∃! t : Tile, Interior P.k (compL P) (tileLocal P.k (compL P) t p) := by
  have hT := norm_pos P.k (compL P) ((comp_positive P).1.trans (comp_positive P).2) (comp_positive P).1.le
  obtain ⟨t,ht⟩ := tiles_cover_closed P.k (compL P) hT p
  have hi := comp_closed_interior P hprim p hp hn t ht
  exact ⟨t,hi,fun u hu => tile_unique P.k (compL P) hT u t p hu hi⟩

end R002.GCSector
