import Formal.GCPrimitiveDegree

namespace R002.GCPrimitive
open Icosahedron (Corner)

theorem frame_next_corner (k l : ℤ) (e : Corner) :
    frame k l e (corner k l (e+1))=A k l := by
  fin_cases e <;> ext <;> simp [frame,corner,turn,A,B] <;> ring

theorem frame_third_corner (k l : ℤ) (e : Corner) :
    frame k l e (corner k l (e+2))=B k l := by
  fin_cases e <;> ext <;> simp [frame,corner,turn,A,B] <;> ring

theorem unit_opposite_iff (k l : ℤ) (p q : Lattice) :
    Unit (opposite k l p) (opposite k l q) ↔ Unit p q := by
  constructor
  · intro h
    simpa only [opposite_involution] using unit_opposite k l _ _ h
  · exact unit_opposite k l p q

theorem unit_swap_opposite (k l : ℤ) (p q : Lattice) :
    Unit p (opposite k l q) ↔ Unit (opposite k l p) q := by
  simpa only [opposite_involution] using unit_opposite_iff k l (opposite k l p) q

theorem norm_gt_step (k l : ℤ) (hkl : l<k) (hl : 0<l) : k+l<norm k l := by
  have hk : 2≤k := by omega
  have hl1 : 1≤l := by omega
  have hk2 : k≤k*k := by nlinarith
  have hl2 : l≤l*l := by nlinarith
  have hklp : 0<k*l := mul_pos (by omega) hl
  dsimp [norm]
  nlinarith

theorem opposite_third_no_unit (k l : ℤ) (hkl : l<k) (hl : 0<l)
    (p : Lattice) (hp : Closed k l p) : ¬Unit (opposite k l (B k l)) p := by
  rintro ⟨i,rfl⟩
  have ht := norm_gt_step k l hkl hl
  have hb := hp.2.1
  fin_cases i <;> dsimp [opposite,B,direction,b] at hb <;>
    dsimp [norm] at ht <;> nlinarith

end R002.GCPrimitive

namespace R002.GCPrimitiveSurface
open Icosahedron GCPrimitive
variable {k l : ℤ}

theorem ordinary_raw_adj_iff (f g : Face) (p q : Point k l) :
    (graph k l).Adj (vertex (f,.inr p)) (vertex (g,.inr q)) ↔
      (f=g ∧ Unit p.val q.val) ∨ Across (f,.inr p) (g,.inr q) := by
  constructor
  · rintro ⟨_,u,v,hu,hv,he⟩
    have heu := interior_raw_unique u f p (congrArg toCanonical hu)
    have hev := interior_raw_unique v g q (congrArg toCanonical hv)
    subst u; subst v
    exact he.elim Or.inl (fun h => h.elim Or.inr (fun h => Or.inr (across_symm _ _ h)))
  · rintro (h|h)
    · exact rawEdge_adj _ _ (Or.inl h)
    · exact rawEdge_adj _ _ (Or.inr (Or.inl h))

theorem parent_point_adj_iff (hkl : l<k) (hl : 0<l) (f g : Face)
    (e : Corner) (q : Point k l) :
    (graph k l).Adj (vertex (f,.inl e)) (vertex (g,.inr q)) ↔
      ∃ c : Corner, faceVertex g c=faceVertex f e ∧ q=fanPoint hkl hl c := by
  rw [parent_adjacency_iff_fans hkl hl (f,e)]
  constructor
  · rintro ⟨a,c,hc,hq⟩
    have hp : (g,q)=(a,fanPoint hkl hl c) := Sum.inr.inj (congrArg toCanonical hq)
    have hg : g=a := congrArg (fun z : Face × Point k l => z.1) hp
    subst a
    exact ⟨c,hc,congrArg Prod.snd hp⟩
  · rintro ⟨c,hc,rfl⟩
    exact ⟨g,c,hc,rfl⟩

theorem no_parent_parent (hkl : l<k) (hl : 0<l) (f g : Face) (e d : Corner) :
    ¬(graph k l).Adj (vertex (f,.inl e)) (vertex (g,.inl d)) := by
  rw [parent_adjacency_iff_fans hkl hl (f,e)]
  rintro ⟨a,c,_,h⟩
  have hh := congrArg toCanonical h
  simp [toCanonical_vertex,canonical] at hh

theorem same_face_adj_iff_unit (hkl : l<k) (hl : 0<l) (u v : Raw k l)
    (hf : u.1=v.1) : (graph k l).Adj (vertex u) (vertex v) ↔ Unit (position u) (position v) := by
  rcases u with ⟨f,e|p⟩ <;> rcases v with ⟨g,d|q⟩
  · change f=g at hf; subst g
    constructor
    · exact fun h => False.elim (no_parent_parent hkl hl f f e d h)
    · intro h
      have he := unit_from_corner hkl hl f e (f,.inl d) rfl h
      have hs : (Sum.inl d : Corner ⊕ Point k l)=Sum.inr (fanPoint hkl hl e) :=
        congrArg (fun z : Raw k l => z.2) he
      cases hs
  · change f=g at hf; subst g
    rw [parent_point_adj_iff hkl hl]
    simp only [(faceVertex_injective f).eq_iff,exists_eq_left]
    constructor
    · intro h
      exact ((closed_corner_fan k l hkl hl e q.val).mpr (congrArg Subtype.val h)).2
    · intro h
      exact Subtype.ext ((closed_corner_fan k l hkl hl e q.val).mp
        ⟨interior_closed k l _ q.property,h⟩)
  · change f=g at hf; subst g
    rw [(graph k l).adj_comm]
    have hp := parent_point_adj_iff hkl hl f f d p
    simp only [(faceVertex_injective f).eq_iff,exists_eq_left] at hp
    rw [hp]
    constructor
    · intro h
      exact unit_symm _ _ (((closed_corner_fan k l hkl hl d p.val).mpr (congrArg Subtype.val h)).2)
    · intro h
      exact Subtype.ext ((closed_corner_fan k l hkl hl d p.val).mp
        ⟨interior_closed k l _ p.property,unit_symm _ _ h⟩)
  · change f=g at hf; subst g
    rw [ordinary_raw_adj_iff]
    constructor
    · rintro (⟨_,h⟩|h)
      · exact h
      · obtain ⟨d,a,b,ha,hb,_⟩ := h
        have hd : d.1=f := (congrArg Prod.fst ha).symm
        have he : (mate d).1=f := (congrArg Prod.fst hb).symm
        exact False.elim (mate_other_face d (he.trans hd.symm))
    · exact fun h => Or.inl ⟨rfl,h⟩

end R002.GCPrimitiveSurface
