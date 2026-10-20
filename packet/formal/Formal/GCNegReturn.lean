import Formal.GCNegTrace

namespace R002.GCNeg
open Icosahedron GCPrimitive GCPrimitiveSurface GCSector

def Same (S : Atlas) (p q : Lattice) : Prop :=
  ∀ hp hpn hq hqn, stripVertex S p hp hpn=stripVertex S q hq hqn

theorem same_of_charts (S : Atlas) (p q : Lattice) (t u : Tile)
    (ht : Interior S.k S.l (tileLocal S.k S.l t p))
    (hu : Interior S.k S.l (tileLocal S.k S.l u q))
    (hf : (S.dart t).1=(S.dart u).1)
    (hc : unframe S.k S.l (S.dart t).2 (tileLocal S.k S.l t p)=
      unframe S.k S.l (S.dart u).2 (tileLocal S.k S.l u q)) : Same S p q := by
  intro hp hpn hq hqn
  rw [stripVertex_eq_chart S p hp hpn t ht,stripVertex_eq_chart S q hq hqn u hu]
  unfold chartVertex
  apply congrArg vertex
  exact Prod.ext hf (congrArg Sum.inr (Subtype.ext hc))

theorem rotated_position (k l : ℤ) (r : Rotation) (f : Face) (e : Corner) (p q : Lattice)
    (h : unframe k l e p=q) :
    unframe k l (rotateDart r (f,e)).2 p=unframe k l (rotateDart r (f,0)).2 q := by
  change unframe k l (e+_) p=unframe k l (0+_) q
  rw [zero_add,← unframe_add,h]

theorem no_G_path (S : Atlas) (J : ℤ) (G : Lattice → Lattice) (hj : 1<J ∧ J<S.A)
    (hup : G (J-1,1)=(S.A-1,0)) (hlo : G (J-1,0)=(S.A,-1))
    (H : ∀ xi : ℤ, 0≤xi → xi≤1 → Same S (J-1,xi) (G (J-1,xi))) :
    ¬∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph S.k S.l) n p := by
  apply no_challenge_of_repeats S
  intro side
  have ho := hj
  let tj := (J-1).toNat
  let ta := (S.A-1).toNat
  let e := if side then 2*tj+1 else 2*tj
  let N := if side then 2*ta else 2*ta+1
  have hcastj : (tj : ℤ)=J-1 := by dsimp [tj]; omega
  have hcasta : (ta : ℤ)=S.A-1 := by dsimp [ta]; omega
  have he : 0<e ∧ e<N ∧ N≤(2*S.A).toNat := by
    cases side <;> dsimp [e,N] <;> omega
  let xi : ℤ := if side then 1 else 0
  have hpoint : zigzag side e=(J-1,xi) := by
    cases side <;> simp only [e,xi,Bool.false_eq_true,ite_false,ite_true,zigzag_even,zigzag_odd]
    all_goals apply Prod.ext <;> dsimp <;> omega
  have htarget : zigzag side N=G (J-1,xi) := by
    cases side
    · simp only [N,xi,Bool.false_eq_true,ite_false,zigzag_odd,hlo]
      apply Prod.ext <;> dsimp <;> omega
    · simp only [N,xi,ite_true,zigzag_even,hup]
      apply Prod.ext <;> dsimp <;> omega
  have hr := zigzag_region S side e (by omega)
  have hrs := zigzag_nonzero side e he.1
  have hn := zigzag_region S side N he.2.2
  have hns := zigzag_nonzero side N (by omega)
  simp only [hpoint] at hr hrs
  simp only [htarget] at hn hns
  have hret := H xi (by dsimp [xi]; cases side <;> simp) (by dsimp [xi]; cases side <;> simp) hr hrs hn hns
  have heq := trace_strip S side e he.1 (by omega)
  have hNq := trace_strip S side N (by omega) he.2.2
  simp only [hpoint] at heq
  simp only [htarget] at hNq
  exact ⟨e,N,he.2.1,he.2.2,heq.trans (hret.trans hNq.symm)⟩


theorem no_H_path (S : Atlas) (J : ℤ) (Hmap : Lattice → Lattice) (hj : 1<J ∧ J<S.A)
    (hup : Hmap (J-1,0)=(S.A-1,1)) (hlo : Hmap (J,-1)=(S.A-1,0))
    (H : ∀ eta : ℤ, 0≤eta → eta≤1 → Same S (J-1+eta,-eta) (Hmap (J-1+eta,-eta))) :
    ¬∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph S.k S.l) n p := by
  apply no_challenge_of_repeats S
  intro side
  let tj := (J-1).toNat
  let ta := (S.A-1).toNat
  let e := if side then 2*tj else 2*tj+1
  let N := if side then 2*ta+1 else 2*ta
  have hcastj : (tj : ℤ)=J-1 := by dsimp [tj]; omega
  have hcasta : (ta : ℤ)=S.A-1 := by dsimp [ta]; omega
  have he : 0<e ∧ e<N ∧ N≤(2*S.A).toNat := by cases side <;> dsimp [e,N] <;> omega
  let eta : ℤ := if side then 0 else 1
  have hpoint : zigzag side e=(J-1+eta,-eta) := by
    cases side <;> simp only [e,eta,Bool.false_eq_true,ite_false,ite_true,zigzag_even,zigzag_odd]
    all_goals apply Prod.ext <;> dsimp <;> omega
  have htarget : zigzag side N=Hmap (J-1+eta,-eta) := by
    cases side
    · simp only [N,eta,Bool.false_eq_true,ite_false,zigzag_even]
      have hh : (J-1+1,-(1:ℤ))=(J,-1) := by ext <;> ring
      rw [hh,hlo]
      apply Prod.ext <;> dsimp <;> omega
    · simp only [N,eta,ite_true,zigzag_odd]
      have hh : (J-1+0,-(0:ℤ))=(J-1,0) := by ext <;> ring
      rw [hh,hup]
      apply Prod.ext <;> dsimp <;> omega
  have hr := zigzag_region S side e (by omega)
  have hrs := zigzag_nonzero side e he.1
  have hn := zigzag_region S side N he.2.2
  have hns := zigzag_nonzero side N (by omega)
  simp only [hpoint] at hr hrs
  simp only [htarget] at hn hns
  have hret := H eta (by dsimp [eta]; cases side <;> simp) (by dsimp [eta]; cases side <;> simp) hr hrs hn hns
  have heq := trace_strip S side e he.1 (by omega)
  have hNq := trace_strip S side N (by omega) he.2.2
  simp only [hpoint] at heq
  simp only [htarget] at hNq
  exact ⟨e,N,he.2.1,he.2.2,heq.trans (hret.trans hNq.symm)⟩

end R002.GCNeg
