import Formal.Claude2K3Inv3

/-!
# K3 aligned surface: generic degree lemmas for edge points and interior points

Written by a Claude worker (2026-10-19, K3 necessity session).

* `deg_edge_gen` : a lattice point `z` strictly inside the edge (direction `d`) of a cell `c`,
                   glued to the cell `f` by `gmap m τ`, has degree 6, provided finitely many
                   explicit membership facts, the list of its sites (`hfib`) and distinctness of
                   seven invariant values;
* `deg_int_gen`  : a lattice point all of whose six lattice neighbours lie in its cell, and which is
                   the only site of its vertex, has degree 6;
* `corner_in`, `V_corner_glue` : corners of cells, and the identification of corners by a gluing.

The hypotheses are discharged per edge (in `Claude2K3Classify.lean`) by `simp` and `omega`.
-/

namespace Claude2K3

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

/-- The gluing map `z ↦ rotN m z + τ`. -/
def gmap (m : ℕ) (τ z : ℤ × ℤ) : ℤ × ℤ := rotN m z + τ

theorem gmap_add (m : ℕ) (τ z u : ℤ × ℤ) : gmap m τ (z + u) = gmap m τ z + rotN m u := by
  simp only [gmap, rotN_add_pt]; abel

theorem nodup_V3 (hr : 0 < r) (hs : 0 < s) (P : List (Fin 11 × (ℤ × ℤ)))
    (hP : ∀ p ∈ P, CellIn r s p.1 p.2) (hinj : (P.map (inv3 r s)).Nodup) :
    (P.map (fun p => V r s p.1 p.2)).Nodup := by
  apply List.Nodup.of_map (vinv3 hr hs)
  rw [List.map_map]
  have : P.map (vinv3 hr hs ∘ fun p => V r s p.1 p.2) = P.map (inv3 r s) :=
    List.map_congr_left (fun p hp => by simp [Function.comp, vinv3_V hr hs (hP p hp)])
  rw [this]; exact hinj

theorem rot_unit {d : ℤ × ℤ} (hd : d ∈ unitVec) : rot d ∈ unitVec := rotN_unit 1 hd

theorem deg_edge_gen (hr : 0 < r) (hs : 0 < s) {c f : Fin 11} {i j m : ℕ} {τ : ℤ × ℤ}
    (hG : (k3Sig r s).Glue c i f j m τ) (z d : ℤ × ℤ) (hd : d ∈ unitVec)
    (h1 : CellIn r s c z) (h2 : CellIn r s c (z + d)) (h3 : CellIn r s c (z + -d))
    (h4 : CellIn r s c (z + rot d)) (h5 : CellIn r s c (z + rot (rot d)))
    (h6 : ¬ CellIn r s c (z + -rot d)) (h7 : ¬ CellIn r s c (z + -rot (rot d)))
    (k1 : CellIn r s f (gmap m τ z)) (k2 : CellIn r s f (gmap m τ (z + d)))
    (k3 : CellIn r s f (gmap m τ (z + -d)))
    (k4 : CellIn r s f (gmap m τ (z + -rot d)))
    (k5 : CellIn r s f (gmap m τ (z + -rot (rot d))))
    (k6 : ¬ CellIn r s f (gmap m τ (z + rot d)))
    (k7 : ¬ CellIn r s f (gmap m τ (z + rot (rot d))))
    (hfib : ∀ g w, CellIn r s g w → inv3 r s (g, w) = inv3 r s (c, z) →
      (g, w) = (c, z) ∨ (g, w) = (f, gmap m τ z))
    (hnd : [inv3 r s (c, z + d), inv3 r s (c, z + -d), inv3 r s (c, z + rot d),
      inv3 r s (c, z + rot (rot d)), inv3 r s (f, gmap m τ (z + -rot d)),
      inv3 r s (f, gmap m τ (z + -rot (rot d)))].Nodup) :
    deg (k3Graph r s) (V r s c z) = 6 := by
  have hglue : ∀ w, CellIn r s c w → CellIn r s f (gmap m τ w) →
      V r s c w = V r s f (gmap m τ w) :=
    fun w hw hw' => V_glue hr hs hG rfl hw hw'
  have hv : V r s c z = V r s f (gmap m τ z) := hglue z h1 k1
  have hrd := rot_unit hd
  have hrrd := rot_unit hrd
  rw [deg_eq hr hs (V r s c z) [(c, z), (f, gmap m τ z)]
    ([(c, z + d), (c, z + -d), (c, z + rot d), (c, z + rot (rot d)), (f, gmap m τ (z + -rot d)),
      (f, gmap m τ (z + -rot (rot d)))].map (fun p => V r s p.1 p.2)) ?_ ?_ ?_ ?_]
  · rfl
  · intro g w hw hV
    have := hfib g w hw (V_inv3 hr hs hw h1 hV)
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact this
  · intro p hp u hu hcell
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only at hcell ⊢
    · rcases unit_cases hd hu with h | h | h | h | h | h <;> rw [h] at hcell ⊢
      · exact Or.inr (List.mem_map.2 ⟨(c, z + d), by simp, rfl⟩)
      · exact Or.inr (List.mem_map.2 ⟨(c, z + rot d), by simp, rfl⟩)
      · exact Or.inr (List.mem_map.2 ⟨(c, z + rot (rot d)), by simp, rfl⟩)
      · exact Or.inr (List.mem_map.2 ⟨(c, z + -d), by simp, rfl⟩)
      · exact absurd hcell h6
      · exact absurd hcell h7
    · obtain ⟨u0, hu0, rfl⟩ := rotN_unit_surj m hu
      rw [← gmap_add] at hcell ⊢
      rcases unit_cases hd hu0 with h | h | h | h | h | h <;> rw [h] at hcell ⊢
      · exact Or.inr (List.mem_map.2 ⟨(c, z + d), by simp, hglue _ h2 k2⟩)
      · exact absurd hcell k6
      · exact absurd hcell k7
      · exact Or.inr (List.mem_map.2 ⟨(c, z + -d), by simp, hglue _ h3 k3⟩)
      · exact Or.inr (List.mem_map.2 ⟨(f, gmap m τ (z + -rot d)), by simp, rfl⟩)
      · exact Or.inr (List.mem_map.2 ⟨(f, gmap m τ (z + -rot (rot d))), by simp, rfl⟩)
  · intro w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · exact V_adj_cell hr hs h1 h2 (by simpa using hd)
    · exact V_adj_cell hr hs h1 h3 (by simpa using unitVec_neg hd)
    · exact V_adj_cell hr hs h1 h4 (by simpa using hrd)
    · exact V_adj_cell hr hs h1 h5 (by simpa using hrrd)
    · rw [hv]; refine V_adj_cell hr hs k1 k4 ?_
      rw [gmap_add]; simpa using rotN_unit m (unitVec_neg hrd)
    · rw [hv]; refine V_adj_cell hr hs k1 k5 ?_
      rw [gmap_add]; simpa using rotN_unit m (unitVec_neg hrrd)
  · apply nodup_V3 hr hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl | rfl | rfl) <;> assumption
    · simpa using hnd

theorem unitVec_nodup_add (z : ℤ × ℤ) : (unitVec.map (fun u => z + u)).Nodup := by
  apply List.Nodup.map (fun a b h => add_left_cancel h)
  decide

theorem deg_int_gen (hr : 0 < r) (hs : 0 < s) {c : Fin 11} (z : ℤ × ℤ) (h1 : CellIn r s c z)
    (hin : ∀ u ∈ unitVec, CellIn r s c (z + u))
    (hfib : ∀ g w, CellIn r s g w → inv3 r s (g, w) = inv3 r s (c, z) → (g, w) = (c, z)) :
    deg (k3Graph r s) (V r s c z) = 6 := by
  rw [deg_eq hr hs (V r s c z) [(c, z)]
    ((unitVec.map (fun u => (c, z + u))).map (fun p => V r s p.1 p.2)) ?_ ?_ ?_ ?_]
  · rfl
  · intro g w hw hV
    have := hfib g w hw (V_inv3 hr hs hw h1 hV)
    simpa using this
  · intro p hp u hu _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact Or.inr (List.mem_map.2 ⟨(c, z + u), List.mem_map.2 ⟨u, hu, rfl⟩, rfl⟩)
  · intro w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hp
    exact V_adj_cell hr hs h1 (hin u hu) (by simpa using hu)
  · apply nodup_V3 hr hs
    · intro p hp
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hp
      exact hin u hu
    · rw [List.map_map]
      have hnd := unitVec_nodup_add z
      have : unitVec.map (inv3 r s ∘ fun u => (c, z + u)) =
          (unitVec.map (fun u => z + u)).map (fun w => inv3 r s (c, w)) := by
        rw [List.map_map]; rfl
      rw [this]
      refine List.Nodup.map_on ?_ hnd
      intro a ha b hb hab
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ha
      obtain ⟨u', hu', rfl⟩ := List.mem_map.1 hb
      exact inv3_inj_cell hr hs (hin u hu) (hin u' hu') hab

theorem k3_poly_len (r s : ℤ) (c : Fin 11) :
    ((k3Sig r s).poly c).length = if c.val < 8 then 3 else 6 := by
  fin_cases c <;> rfl

/-- Every corner of a cell lies in the cell. -/
theorem corner_in (hr : 0 < r) (hs : 0 < s) (c : Fin 11) (i : ℕ) :
    CellIn r s c ((k3Sig r s).pt c i) := by
  have h3 : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have h6 : i % 6 < 6 := Nat.mod_lt _ (by norm_num)
  fin_cases c <;> simp only [Sig.pt, k3_poly_len] <;> norm_num
  all_goals first
    | (generalize i % 3 = k at h3 ⊢; interval_cases k <;>
        simp [k3Sig, k3Poly, walk, rotN, rot, CellIn, TriIn, HexIn] <;> omega)
    | (generalize i % 6 = k at h6 ⊢; interval_cases k <;>
        simp [k3Sig, k3Poly, walk, rotN, rot, CellIn, TriIn, HexIn] <;> omega)

/-- A gluing identifies corner `i` of `g` with corner `j + 1` of `f`. -/
theorem V_corner_glue (hr : 0 < r) (hs : 0 < s) {g f : Fin 11} {i j m : ℕ} {τ : ℤ × ℤ}
    (hG : (k3Sig r s).Glue g i f j m τ) :
    V r s g ((k3Sig r s).pt g i) = V r s f ((k3Sig r s).pt f (j + 1)) :=
  V_glue hr hs hG hG.2.2.2.2.1 (corner_in hr hs g i) (corner_in hr hs f (j + 1))

end Claude2K3

#print axioms Claude2K3.deg_edge_gen
#print axioms Claude2K3.deg_int_gen
