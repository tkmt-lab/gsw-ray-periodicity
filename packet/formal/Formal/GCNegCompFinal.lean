import Formal.GCNegCompSeams
import Formal.GCNegTrace

namespace R002.GCNeg
open Icosahedron GCPrimitive GCPrimitiveSurface GCSector

abbrev compAtlas (P : Parameters) (hp : Primitive P.k (compL P)) : Atlas where
  k := P.k
  l := compL P
  A := compA P
  hkl := (comp_positive P).2
  hl := (comp_positive P).1
  hprim := hp
  hA := by have := comp_indices_order P; omega
  active := CompActive P
  dart := compDart P
  closedInterior := comp_closed_interior P hp
  activeOf := comp_strip_active P hp
  compatible := comp_seams P
  dartTop := comp_dart_top P
  dartLower := by rw [comp_dart_lower]; rfl
  dartSecond := by
    simpa [Int.cast_neg,phase3_zero,bandDart,labelA] using
      comp_reg0 P 0 (-1) (by have := P.hq; omega) (by omega) (by omega) false

theorem comp_return_local (P : Parameters) (p : Lattice) :
    tileLocal P.k (compL P) ⟨P.q+1,-P.q-1,false⟩ (compG P p)=
      tileLocal P.k (compL P) ⟨P.q-3,2-P.q,true⟩ p := by
  ext <;> dsimp [tileLocal,tileBase,compG,compA,compJ,A3.gc] <;> ring

theorem comp_return_dart (P : Parameters) :
    compDart P ⟨P.q+1,-P.q-1,false⟩=compDart P ⟨P.q-3,2-P.q,true⟩ := by
  have hq := P.hq
  rw [comp_dart_cap1,comp_reg0 P (P.q-3) (2-P.q) (by omega) (by omega) (by omega)]
  have he : (-(↑(2-P.q) : ZMod 3)-1)=(P.q : ZMod 3) := by
    push_cast
    have h3 : (3 : ZMod 3)=0 := by decide +kernel
    linear_combination -h3
  rw [he]
  rfl

theorem comp_return_vertex (P : Parameters) (hp : Primitive P.k (compL P))
    (xi : ℤ) (hx0 : 0≤xi) (hx1 : xi≤1)
    (hsrc : Region (compA P) (compJ P-1,xi)) (hsrcn : (compJ P-1,xi)≠(0,0))
    (hdst : Region (compA P) (compG P (compJ P-1,xi))) (hdstn : compG P (compJ P-1,xi)≠(0,0)) :
    stripVertex (compAtlas P hp) (compG P (compJ P-1,xi)) hdst hdstn=
      stripVertex (compAtlas P hp) (compJ P-1,xi) hsrc hsrcn := by
  have ht := comp_source_interior P xi hx0 hx1
  have hu : Interior P.k (compL P)
      (tileLocal P.k (compL P) ⟨P.q+1,-P.q-1,false⟩ (compG P (compJ P-1,xi))) := by
    rwa [comp_return_local]
  rw [stripVertex_eq_chart (compAtlas P hp) _ _ _ _ hu,
    stripVertex_eq_chart (compAtlas P hp) _ _ _ _ ht]
  unfold chartVertex
  apply congrArg vertex
  apply Prod.ext
  · change (compDart P _).1=(compDart P _).1
    rw [comp_return_dart]
  · apply congrArg Sum.inr
    apply Subtype.ext
    change unframe P.k (compL P) (compDart P _).2 _=unframe P.k (compL P) (compDart P _).2 _
    rw [comp_return_dart,comp_return_local]

theorem comp_no_challenge_path (P : Parameters) (hp : Primitive P.k (compL P)) :
    ¬∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph P.k (compL P)) n p := by
  apply no_challenge_of_repeats (compAtlas P hp)
  intro side
  have ho := comp_indices_order P
  let tj := (compJ P-1).toNat
  let ta := (compA P-1).toNat
  let e := if side then 2*tj+1 else 2*tj
  let N := if side then 2*ta else 2*ta+1
  have hcastj : (tj : ℤ)=compJ P-1 := by dsimp [tj]; omega
  have hcasta : (ta : ℤ)=compA P-1 := by dsimp [ta]; omega
  have he : 0<e ∧ e<N ∧ N≤(2*(compAtlas P hp).A).toNat := by
    cases side <;> dsimp [e,N,compAtlas] <;> omega
  let xi : ℤ := if side then 1 else 0
  have hpoint : zigzag side e=(compJ P-1,xi) := by
    cases side <;> simp only [e,xi,Bool.false_eq_true,ite_false,ite_true,zigzag_even,zigzag_odd]
    all_goals apply Prod.ext <;> dsimp <;> omega
  have htarget : zigzag side N=compG P (compJ P-1,xi) := by
    cases side
    · simp only [N,xi,Bool.false_eq_true,ite_false,zigzag_odd,comp_lower_collision]
      apply Prod.ext <;> dsimp <;> omega
    · simp only [N,xi,ite_true,zigzag_even,comp_upper_collision]
      apply Prod.ext <;> dsimp <;> omega
  have hr := zigzag_region (compAtlas P hp) side e (by omega)
  have hrs := zigzag_nonzero side e he.1
  have hn := zigzag_region (compAtlas P hp) side N he.2.2
  have hns := zigzag_nonzero side N (by omega)
  simp only [hpoint] at hr hrs
  simp only [htarget] at hn hns
  have hret := comp_return_vertex P hp xi (by dsimp [xi]; cases side <;> simp) (by dsimp [xi]; cases side <;> simp) hr hrs hn hns
  have heq := trace_strip (compAtlas P hp) side e he.1 (by omega)
  have hNq := trace_strip (compAtlas P hp) side N (by omega) he.2.2
  simp only [hpoint] at heq
  simp only [htarget] at hNq
  exact ⟨e,N,he.2.1,he.2.2,heq.trans (hret.symm.trans hNq.symm)⟩

end R002.GCNeg
