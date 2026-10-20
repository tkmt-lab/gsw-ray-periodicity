import Formal.GCPrimitiveChartEdges

namespace R002.GCPrimitiveSurface
open Icosahedron GCPrimitive
variable {k l : ℤ}

theorem shared_corners : ∀ (f : Face) (d e m : Corner),
    faceVertex (mate (f,d)).1 m=faceVertex f e ↔
      (e=d ∧ m=(mate (f,d)).2+1) ∨ (e=d+1 ∧ m=(mate (f,d)).2) := by decide +kernel

theorem corner_seam_unit (hkl : l<k) (hl : 0<l) (d e m : Corner) (p : Point k l) :
    Unit (frame k l d (corner k l e)) (opposite k l (frame k l m p.val)) ↔
      (e=d ∧ p=fanPoint hkl hl (m+1)) ∨ (e=d+1 ∧ p=fanPoint hkl hl m) := by
  have hc : e=d ∨ e=d+1 ∨ e=d+2 := by fin_cases e <;> fin_cases d <;> decide
  rcases hc with rfl | rfl | rfl
  · rw [frame_corner,unit_swap_opposite]
    have ho : opposite k l (0,0)=A k l := by ext <;> simp [opposite,A]
    rw [ho,← frame_next_corner k l m,frame_unit]
    have hf : Unit (corner k l (m+1)) p.val ↔ p=fanPoint hkl hl (m+1) := by
      constructor
      · exact fun h => Subtype.ext ((closed_corner_fan k l hkl hl _ _).mp ⟨interior_closed k l _ p.property,h⟩)
      · intro h
        exact ((closed_corner_fan k l hkl hl _ _).mpr (congrArg Subtype.val h)).2
    rw [hf]
    have hd : ∀ a : Corner, a≠a+1 := by decide +kernel
    simp [hd]
  · rw [frame_next_corner,unit_swap_opposite]
    have ho : opposite k l (A k l)=(0,0) := by ext <;> simp [opposite,A]
    rw [ho,← frame_corner k l m,frame_unit]
    have hf : Unit (corner k l m) p.val ↔ p=fanPoint hkl hl m := by
      constructor
      · exact fun h => Subtype.ext ((closed_corner_fan k l hkl hl _ _).mp ⟨interior_closed k l _ p.property,h⟩)
      · intro h
        exact ((closed_corner_fan k l hkl hl _ _).mpr (congrArg Subtype.val h)).2
    rw [hf]
    have hd : d+1≠d := by fin_cases d <;> decide
    simp [hd]
  · rw [frame_third_corner,unit_swap_opposite]
    have hn := opposite_third_no_unit k l hkl hl _
      ((closed_frame k l m p.val).mpr (interior_closed k l _ p.property))
    have h0 : d+2≠d := by fin_cases d <;> decide
    have h1 : d+2≠d+1 := by fin_cases d <;> decide
    simp [hn,h0,h1]

theorem ordinary_seam_adj_iff (d : Dart) (p q : Point k l) :
    (graph k l).Adj (vertex (d.1,.inr p)) (vertex ((mate d).1,.inr q)) ↔
      Unit (frame k l d.2 p.val) (opposite k l (frame k l (mate d).2 q.val)) := by
  rw [ordinary_raw_adj_iff]
  constructor
  · rintro (⟨hf,_⟩|⟨e,a,b,ha,hb,h⟩)
    · exact False.elim (mate_other_face d hf.symm)
    · have he : e.1=d.1 := (congrArg Prod.fst ha).symm
      have hf : (mate e).1=(mate d).1 := (congrArg Prod.fst hb).symm
      have hf' : (mate (d.1,e.2)).1=(mate (d.1,d.2)).1 := by
        change (mate (e.1,e.2)).1=(mate (d.1,d.2)).1 at hf
        rw [he] at hf
        exact hf
      have hd : e=d := Prod.ext he (neighborFace_injective d.1 hf')
      subst e
      have hp : p=a := Sum.inr.inj (congrArg Prod.snd ha)
      have hq : q=b := Sum.inr.inj (congrArg Prod.snd hb)
      subst a; subst b; exact h
  · exact fun h => Or.inr ⟨d,p,q,rfl,rfl,h⟩

theorem parent_seam_adj_iff (hkl : l<k) (hl : 0<l) (d : Dart) (e : Corner) (q : Point k l) :
    (graph k l).Adj (vertex (d.1,.inl e)) (vertex ((mate d).1,.inr q)) ↔
      Unit (frame k l d.2 (corner k l e)) (opposite k l (frame k l (mate d).2 q.val)) := by
  rw [parent_point_adj_iff hkl hl,corner_seam_unit hkl hl]
  constructor
  · rintro ⟨c,hc,hq⟩
    rcases (shared_corners d.1 d.2 e c).mp hc with ⟨he,hc⟩ | ⟨he,hc⟩
    · exact Or.inl ⟨he,hc ▸ hq⟩
    · exact Or.inr ⟨he,hc ▸ hq⟩
  · rintro (⟨he,hq⟩|⟨he,hq⟩)
    · exact ⟨(mate d).2+1,(shared_corners d.1 d.2 e _).mpr (Or.inl ⟨he,rfl⟩),hq⟩
    · exact ⟨(mate d).2,(shared_corners d.1 d.2 e _).mpr (Or.inr ⟨he,rfl⟩),hq⟩

theorem corners_no_seam_unit (hkl : l<k) (hl : 0<l) (d e m c : Corner) :
    ¬Unit (frame k l d (corner k l e))
      (opposite k l (frame k l m (corner k l c))) := by
  have hc : e=d ∨ e=d+1 ∨ e=d+2 := by fin_cases e <;> fin_cases d <;> decide
  rcases hc with rfl | rfl | rfl
  · rw [frame_corner,unit_swap_opposite]
    have ho : opposite k l (0,0)=A k l := by ext <;> simp [opposite,A]
    rw [ho,← frame_next_corner k l m,frame_unit]
    intro h
    have hp := (closed_corner_fan k l hkl hl (m+1) _).mp
      ⟨corner_closed k l (by omega) hl.le c,h⟩
    exact corner_not_interior k l c (hp ▸ (fanPoint hkl hl (m+1)).property)
  · rw [frame_next_corner,unit_swap_opposite]
    have ho : opposite k l (A k l)=(0,0) := by ext <;> simp [opposite,A]
    rw [ho,← frame_corner k l m,frame_unit]
    intro h
    have hp := (closed_corner_fan k l hkl hl m _).mp
      ⟨corner_closed k l (by omega) hl.le c,h⟩
    exact corner_not_interior k l c (hp ▸ (fanPoint hkl hl m).property)
  · rw [frame_third_corner,unit_swap_opposite]
    exact opposite_third_no_unit k l hkl hl _
      ((closed_frame k l m _).mpr (corner_closed k l (by omega) hl.le c))

/-- All raw corner/interior combinations, including corner aliases across a seam. -/
theorem seam_adj_iff_unit (hkl : l<k) (hl : 0<l) (d : Dart)
    (u v : Corner ⊕ Point k l) :
    (graph k l).Adj (vertex (d.1,u)) (vertex ((mate d).1,v)) ↔
      Unit (frame k l d.2 (position (d.1,u)))
        (opposite k l (frame k l (mate d).2 (position ((mate d).1,v)))) := by
  cases u with
  | inl e =>
    cases v with
    | inl c => simp only [position,no_parent_parent hkl hl,corners_no_seam_unit hkl hl]
    | inr q => exact parent_seam_adj_iff hkl hl d e q
  | inr p =>
    cases v with
    | inl c =>
      rw [(graph k l).adj_comm]
      have h := parent_seam_adj_iff hkl hl (mate d) c p
      rw [mate_involutive] at h
      refine h.trans ?_
      constructor <;> intro hu
      · exact unit_seam_swap _ _ hu
      · exact unit_seam_swap _ _ hu
    | inr q => exact ordinary_seam_adj_iff d p q

end R002.GCPrimitiveSurface
