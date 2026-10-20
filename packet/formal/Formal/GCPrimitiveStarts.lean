import Formal.GCParentRotations

/-! All degree-five starts, derived from actual graph adjacency and degrees. -/
namespace R002.GCPrimitiveSurface
open Icosahedron GCPrimitive GCChallengeBridge
variable {k l : ℤ}

def parent (d : Dart) : Vertex k l := vertex (d.1,.inl d.2)
def fan (hkl : l<k) (hl : 0<l) (d : Dart) : Vertex k l :=
  vertex (d.1,.inr (fanPoint hkl hl d.2))

theorem parent_turn (d : Dart) : parent (k:=k) (l:=l) (Icosahedron.turn d)=parent d := by
  exact toCanonical_injective (congrArg Sum.inl (turn_preserves_vertex d))

theorem parent_turn_iterate (d : Dart) (n : ℕ) :
    parent (k:=k) (l:=l) ((Icosahedron.turn^[n]) d)=parent d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',parent_turn,ih]

theorem fan_adj_parent (hkl : l<k) (hl : 0<l) (d : Dart) :
    (graph k l).Adj (parent d) (fan hkl hl d) := by
  apply (parent_adjacency_iff_fans hkl hl d _).mpr
  exact ⟨d.1,d.2,rfl,rfl⟩

theorem fanPoint_injective (hkl : l<k) (hl : 0<l) :
    Function.Injective (fanPoint hkl hl) := by
  intro e d h
  have hv := congrArg Subtype.val h
  fin_cases e <;> fin_cases d <;>
    simp [fanPoint,unframe,GCPrimitive.turn] at hv ⊢ <;> omega

theorem fan_injective (hkl : l<k) (hl : 0<l) : Function.Injective (fan hkl hl) := by
  intro d e h
  have hc : (d.1,fanPoint hkl hl d.2)=(e.1,fanPoint hkl hl e.2) :=
    Sum.inr.inj (congrArg toCanonical h)
  exact Prod.ext (congrArg (fun z : Face × Point k l => z.1) hc)
    (fanPoint_injective hkl hl (congrArg (fun z : Face × Point k l => z.2) hc))

theorem fan_turn_adj (hkl : l<k) (hl : 0<l) (d : Dart) :
    (graph k l).Adj (fan hkl hl d) (fan hkl hl (Icosahedron.turn d)) := by
  apply rawEdge_adj
  refine Or.inr (Or.inl ⟨d,fanPoint hkl hl d.2,
    fanPoint hkl hl ((mate d).2+1),rfl,rfl,?_⟩)
  change Unit (frame k l d.2 (unframe k l d.2 (0,1)))
    (opposite k l (frame k l (mate d).2 (unframe k l ((mate d).2+1) (0,1))))
  rw [frame_unframe]
  generalize (mate d).2=e
  fin_cases e <;> refine ⟨5,?_⟩ <;>
    ext <;> simp [frame,unframe,opposite,GCPrimitive.turn,direction] <;> ring

def thirdDart (d : Dart) (side : Bool) : Dart :=
  if side then Icosahedron.turn d else (Icosahedron.turn^[4]) d

theorem thirdDart_parent (d : Dart) (side : Bool) :
    parent (k:=k) (l:=l) (thirdDart d side)=parent d := by
  cases side
  · exact parent_turn_iterate d 4
  · exact parent_turn d

theorem thirdDart_distinct : ∀ d : Dart, thirdDart d false≠thirdDart d true := by decide +kernel

theorem fan_third_adj (hkl : l<k) (hl : 0<l) (d : Dart) (side : Bool) :
    (graph k l).Adj (fan hkl hl d) (fan hkl hl (thirdDart d side)) := by
  cases side
  · have h := (fan_turn_adj hkl hl ((Icosahedron.turn^[4]) d)).symm
    have hi : Icosahedron.turn ((Icosahedron.turn^[4]) d)=d := by
      simpa only [Function.iterate_succ_apply'] using turn_five d
    simpa only [hi,thirdDart,Bool.false_eq_true,if_false] using h
  · exact fan_turn_adj hkl hl d

def startTriangle (hkl : l<k) (hl : 0<l) (d : Dart) (side : Bool) :
    R002.OrderedTriangle (graph k l) where
  a := parent d
  b := fan hkl hl d
  c := fan hkl hl (thirdDart d side)
  ab := fan_adj_parent hkl hl d
  bc := fan_third_adj hkl hl d side
  ca := by
    have h := (fan_adj_parent hkl hl (thirdDart d side)).symm
    simpa only [thirdDart_parent] using h

theorem start_parent_degree (hkl : l<k) (hl : 0<l) (d : Dart) :
    ClaudeChallenge.deg (graph k l) (parent (k:=k) (l:=l) d)=5 :=
  parent_neighbor_card hkl hl d

theorem start_fan_degree (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) (d : Dart) :
    ClaudeChallenge.deg (graph k l) (fan hkl hl d)=6 :=
  ordinary_neighbor_card (by omega) hl hprim d.1 (fanPoint hkl hl d.2)

abbrev Start (k l : ℤ) := {t : R002.OrderedTriangle (graph k l) //
  ClaudeChallenge.deg (graph k l) t.a=5 ∧ ClaudeChallenge.deg (graph k l) t.b=6}

def parametrizedStart (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (s : Dart × Bool) : Start k l :=
  ⟨startTriangle hkl hl s.1 s.2,start_parent_degree hkl hl s.1,start_fan_degree hkl hl hprim s.1⟩

/-- Two independently exhibited common neighbours exhaust a two-common-neighbour set. -/
theorem common_exhaust {V : Type} (G : SimpleGraph V) (hG : R002.TwoCommonNeighbors G)
    (a b x y : V) (hab : G.Adj a b) (hx : G.Adj a x ∧ G.Adj b x)
    (hy : G.Adj a y ∧ G.Adj b y) (hne : x≠y) (z : V) :
    (G.Adj a z ∧ G.Adj b z) ↔ z=x ∨ z=y := by
  obtain ⟨u,v,huv,h⟩ := hG a b hab
  have hhx := (h x).mp hx
  have hhy := (h y).mp hy
  rcases hhx with rfl|rfl <;> rcases hhy with rfl|rfl
  · exact False.elim (hne rfl)
  · exact h z
  · simpa only [or_comm] using h z
  · exact False.elim (hne rfl)

@[ext] theorem orderedTriangle_ext {V : Type} {G : SimpleGraph V}
    (s t : R002.OrderedTriangle G) (ha : s.a=t.a) (hb : s.b=t.b) (hc : s.c=t.c) : s=t := by
  cases s; cases t; simp_all

theorem parametrizedStart_injective (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) :
    Function.Injective (parametrizedStart hkl hl hprim) := by
  rintro ⟨d,b⟩ ⟨e,c⟩ h
  have hd : d=e := fan_injective hkl hl (congrArg (fun t : Start k l => t.val.b) h)
  subst e
  have ht := fan_injective hkl hl (congrArg (fun t : Start k l => t.val.c) h)
  have hb : b=c := by
    cases b <;> cases c
    · rfl
    · exact False.elim (thirdDart_distinct d ht)
    · exact False.elim (thirdDart_distinct d ht.symm)
    · rfl
  subst c; rfl

theorem parametrizedStart_surjective (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) :
    Function.Surjective (parametrizedStart hkl hl hprim) := by
  intro s
  have ha : ∃ d : Dart, s.val.a=parent d := by
    have hd := s.property.1
    generalize hv : s.val.a=v at hd ⊢
    revert hd
    refine Quotient.inductionOn v ?_
    rintro ⟨f,e|p⟩ hd
    · exact ⟨(f,e),rfl⟩
    · have hh := ordinary_neighbor_card (show 0<k by omega) hl hprim f p
      change ClaudeChallenge.deg (graph k l) (vertex (f,.inr p))=6 at hh
      change ClaudeChallenge.deg (graph k l) (vertex (f,.inr p))=5 at hd
      omega
  obtain ⟨d,hd⟩ := ha
  have hb := s.val.ab
  rw [hd] at hb
  change (graph k l).Adj (vertex (d.1,.inl d.2)) s.val.b at hb
  rw [parent_adjacency_iff_fans hkl hl] at hb
  obtain ⟨f,e,hlabel,hb⟩ := hb
  have ha' : s.val.a=parent (f,e) := hd.trans
    (toCanonical_injective (congrArg Sum.inl hlabel.symm))
  let d' : Dart := (f,e)
  change s.val.b=fan hkl hl d' at hb
  change s.val.a=parent d' at ha'
  let hx := startTriangle hkl hl d' false
  let hy := startTriangle hkl hl d' true
  have ht := (common_exhaust (graph k l) (two_common_neighbors hkl hl hprim)
    (parent d') (fan hkl hl d') hx.c hy.c hx.ab ⟨hx.ca.symm,hx.bc⟩
    ⟨hy.ca.symm,hy.bc⟩ (fun he => thirdDart_distinct d' (fan_injective hkl hl he)) s.val.c).mp
      (by simpa only [← ha',← hb] using And.intro s.val.ca.symm s.val.bc)
  rcases ht with ht|ht
  · refine ⟨(d',false),Subtype.ext ?_⟩
    exact orderedTriangle_ext _ _ ha'.symm hb.symm ht.symm
  · refine ⟨(d',true),Subtype.ext ?_⟩
    exact orderedTriangle_ext _ _ ha'.symm hb.symm ht.symm

noncomputable def startsEquiv (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) :
    (Dart × Bool) ≃ Start k l := Equiv.ofBijective _
      ⟨parametrizedStart_injective hkl hl hprim,parametrizedStart_surjective hkl hl hprim⟩

theorem all_starts_card (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) :
    Nat.card (Start k l)=120 := by
  rw [← Nat.card_congr (startsEquiv hkl hl hprim)]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

end R002.GCPrimitiveSurface
