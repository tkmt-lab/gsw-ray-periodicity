import Formal.Claude4K3SeamEdge

/-!
# K3 pieces: cap edges and tube edges between seam points

Written by a Claude worker (2026-10-20, K3 bridge).

* `seam_cases_top/bot` : a cap edge between two outer points runs along an outer edge
  (`AlongT/B`) or is the chord across the corner of the cell (`ChordST/SB`);
* `along_TA_*`  : an edge along an outer edge is a tube step of the invariants;
* `along_uniq_*` : only one unit triangle of `Δ` lies on an edge along an outer edge;
* `chord_*`     : the invariants of a chord;
* `tube_seam_*` : a tube edge between two seam points of a hexagon is a cap edge along a side of
  `Δ`, with only one unit triangle of `Δ` on it.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Claude4K3

open ClaudeChallenge Claude2Aligned Claude2K3

variable {r s : ℤ}

def AlongT (f : Fin 11) (z d : ℤ × ℤ) : Prop :=
  f.val < 3 ∧ ((z.2 = 0 ∧ d.2 = 0) ∨ (z.1 = 0 ∧ d.1 = 0))

def ChordST (f : Fin 11) (z d : ℤ × ℤ) : Prop :=
  f.val < 3 ∧ ((z.1 = 1 ∧ z.2 = 0 ∧ d.1 = -1 ∧ d.2 = 1) ∨ (z.1 = 0 ∧ z.2 = 1 ∧ d.1 = 1 ∧ d.2 = -1))

def AlongB (r : ℤ) (f : Fin 11) (z d : ℤ × ℤ) : Prop :=
  4 ≤ f.val ∧ f.val < 7 ∧ ((z.1 + z.2 = r ∧ d.1 + d.2 = 0) ∨ (z.1 = 0 ∧ d.1 = 0))

def ChordSB (r : ℤ) (f : Fin 11) (z d : ℤ × ℤ) : Prop :=
  4 ≤ f.val ∧ f.val < 7 ∧
    ((z.1 = 1 ∧ z.2 = r - 1 ∧ d.1 = -1 ∧ d.2 = 0) ∨ (z.1 = 0 ∧ z.2 = r - 1 ∧ d.1 = 1 ∧ d.2 = 0))

theorem tri_of_cell {f : Fin 11} {z : ℤ × ℤ} (hf : f.val < 8) (h : CellIn r s f z) : TriIn r z := by
  simpa [CellIn, hf] using h

theorem seam_cases_top (hr : 2 ≤ r) {f : Fin 11} {z d : ℤ × ℤ} (hf : f.val < 4)
    (hz : CellIn r s f z) (hz' : CellIn r s f (z + d)) (hd : d ∈ unitVec)
    (o1 : OuterT r f z) (o2 : OuterT r f (z + d)) : AlongT f z d ∨ ChordST f z d := by
  have t1 := tri_of_cell (by omega) hz
  have t2 := tri_of_cell (by omega) hz'
  obtain ⟨x, y⟩ := z
  simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [OuterT, AlongT, ChordST, TriIn] at * <;> omega

theorem seam_cases_bot (hr : 2 ≤ r) {f : Fin 11} {z d : ℤ × ℤ} (hf1 : 4 ≤ f.val) (hf : f.val < 8)
    (hz : CellIn r s f z) (hz' : CellIn r s f (z + d)) (hd : d ∈ unitVec)
    (o1 : OuterB r f z) (o2 : OuterB r f (z + d)) : AlongB r f z d ∨ ChordSB r f z d := by
  have t1 := tri_of_cell hf hz
  have t2 := tri_of_cell hf hz'
  obtain ⟨x, y⟩ := z
  simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [OuterB, AlongB, ChordSB, TriIn] at * <;> omega

macro "inv_tac" : tactic =>
  `(tactic| (simp [inv, hgt, ang, nrm, AE, CellIn, TriIn] at * <;> (try split_ifs) <;> omega))

set_option maxHeartbeats 2000000 in
theorem along_TA_top (hr : 2 ≤ r) {f : Fin 11} {z d : ℤ × ℤ} (h : AlongT f z d)
    (hd : d ∈ unitVec) (hz : CellIn r s f z) (hz' : CellIn r s f (z + d)) :
    TA r (inv r s (f, z)) (inv r s (f, z + d)) := by
  obtain ⟨hf, h⟩ := h
  obtain ⟨x, y⟩ := z
  simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h
  · fin_cases f <;> simp at hf <;> apply ta_2 <;> inv_tac
  · fin_cases f <;> simp at hf <;> apply ta_4 <;> inv_tac
  · fin_cases f <;> simp at hf <;> apply ta_1 <;> inv_tac
  · fin_cases f <;> simp at hf <;> apply ta_3 <;> inv_tac

set_option maxHeartbeats 2000000 in
theorem along_TA_bot (hr : 2 ≤ r) {f : Fin 11} {z d : ℤ × ℤ} (h : AlongB r f z d)
    (hd : d ∈ unitVec) (hz : CellIn r s f z) (hz' : CellIn r s f (z + d)) :
    TA r (inv r s (f, z)) (inv r s (f, z + d)) := by
  obtain ⟨hf1, hf, h⟩ := h
  obtain ⟨x, y⟩ := z
  simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h
  · fin_cases f <;> simp at hf hf1 <;> apply ta_2 <;> inv_tac
  · fin_cases f <;> simp at hf hf1 <;> apply ta_4 <;> inv_tac
  · fin_cases f <;> simp at hf hf1 <;> apply ta_1 <;> inv_tac
  · fin_cases f <;> simp at hf hf1 <;> apply ta_3 <;> inv_tac

set_option maxHeartbeats 2000000 in
theorem along_uniq_top (hr : 2 ≤ r) {f : Fin 11} {z d p q : ℤ × ℤ} (h : AlongT f z d)
    (hd : d ∈ unitVec) (hz : CellIn r s f z) (hz' : CellIn r s f (z + d))
    (hp : InD r p) (hq : InD r q) (hp1 : Unit (p - dC r f z)) (hp2 : Unit (p - dC r f (z + d)))
    (hq1 : Unit (q - dC r f z)) (hq2 : Unit (q - dC r f (z + d))) : p = q := by
  obtain ⟨hf, h⟩ := h
  have hu := cap_edge (r := r) (z := z) (by simp only [capOf]; split_ifs <;> omega : capOf f < 2) hd
  have ap := planar_apex hu hp1 hp2
  have aq := planar_apex hu hq1 hq2
  have t1 := tri_of_cell (by omega) hz
  obtain ⟨x, y⟩ := z; obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h <;>
  fin_cases f <;> simp at hf <;> simp [dC, InD, TriIn, Prod.ext_iff] at * <;> omega

set_option maxHeartbeats 2000000 in
theorem along_uniq_bot (hr : 2 ≤ r) {f : Fin 11} {z d p q : ℤ × ℤ} (h : AlongB r f z d)
    (hd : d ∈ unitVec) (hz : CellIn r s f z) (hz' : CellIn r s f (z + d))
    (hp : InD r p) (hq : InD r q) (hp1 : Unit (p - dC r f z)) (hp2 : Unit (p - dC r f (z + d)))
    (hq1 : Unit (q - dC r f z)) (hq2 : Unit (q - dC r f (z + d))) : p = q := by
  obtain ⟨hf1, hf, h⟩ := h
  have hu := cap_edge (r := r) (z := z) (by simp only [capOf]; split_ifs <;> omega : capOf f < 2) hd
  have ap := planar_apex hu hp1 hp2
  have aq := planar_apex hu hq1 hq2
  have t1 := tri_of_cell (by omega) hz
  obtain ⟨x, y⟩ := z; obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h <;>
  fin_cases f <;> simp at hf hf1 <;> simp [dC, InD, TriIn, Prod.ext_iff] at * <;> omega

set_option maxHeartbeats 2000000 in
theorem chord_top (hr : 2 ≤ r) {f : Fin 11} {z d : ℤ × ℤ} (h : ChordST f z d) :
    ChordT r (inv r s (f, z)) (inv r s (f, z + d)) := by
  obtain ⟨hf, h⟩ := h
  obtain ⟨x, y⟩ := z; obtain ⟨d1, d2⟩ := d
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
  fin_cases f <;> simp at hf <;> simp [ChordT, inv, hgt, ang, nrm] <;> (try split_ifs) <;> omega

set_option maxHeartbeats 2000000 in
theorem chord_bot (hr : 2 ≤ r) {f : Fin 11} {z d : ℤ × ℤ} (h : ChordSB r f z d) :
    ChordB r s (inv r s (f, z)) (inv r s (f, z + d)) := by
  obtain ⟨hf1, hf, h⟩ := h
  obtain ⟨x, y⟩ := z; obtain ⟨d1, d2⟩ := d
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
  fin_cases f <;> simp at hf hf1 <;>
    simp [ChordB, ChordT, tau, inv, hgt, ang, nrm] <;> (try split_ifs) <;> omega

set_option maxHeartbeats 4000000 in
theorem tube_seam_top (hr : 2 ≤ r) (hs : 2 ≤ s) {g : Fin 11} {w d : ℤ × ℤ} (hg : 8 ≤ g.val)
    (hw : CellIn r s g w) (hw' : CellIn r s g (w + d)) (hd : d ∈ unitVec)
    (e1 : TopEdge r w) (e2 : TopEdge r (w + d)) :
    Unit (bTg r g (w + d) - bTg r g w) ∧ ∀ p q : ℤ × ℤ, InD r p → InD r q →
      Unit (p - bTg r g w) → Unit (p - bTg r g (w + d)) → Unit (q - bTg r g w) →
      Unit (q - bTg r g (w + d)) → p = q := by
  have key : Unit (bTg r g (w + d) - bTg r g w) := by
    obtain ⟨x, y⟩ := w
    simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases g <;> simp at hg <;>
    simp [bTg, Unit, TopEdge, CellIn, HexIn] at * <;> omega
  refine ⟨key, fun p q hp hq hp1 hp2 hq1 hq2 => ?_⟩
  have ap := planar_apex key hp1 hp2
  have aq := planar_apex key hq1 hq2
  obtain ⟨x, y⟩ := w; obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
  fin_cases g <;> simp at hg <;>
  simp [bTg, InD, TopEdge, CellIn, HexIn, Prod.ext_iff] at * <;> omega

set_option maxHeartbeats 4000000 in
theorem tube_seam_bot (hr : 2 ≤ r) (hs : 2 ≤ s) {g : Fin 11} {w d : ℤ × ℤ} (hg : 8 ≤ g.val)
    (hw : CellIn r s g w) (hw' : CellIn r s g (w + d)) (hd : d ∈ unitVec)
    (e1 : BotEdge r s w) (e2 : BotEdge r s (w + d)) :
    Unit (bBg r g (w + d) - bBg r g w) ∧ ∀ p q : ℤ × ℤ, InD r p → InD r q →
      Unit (p - bBg r g w) → Unit (p - bBg r g (w + d)) → Unit (q - bBg r g w) →
      Unit (q - bBg r g (w + d)) → p = q := by
  have key : Unit (bBg r g (w + d) - bBg r g w) := by
    obtain ⟨x, y⟩ := w
    simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases g <;> simp at hg <;>
    simp [bBg, Unit, BotEdge, CellIn, HexIn] at * <;> omega
  refine ⟨key, fun p q hp hq hp1 hp2 hq1 hq2 => ?_⟩
  have ap := planar_apex key hp1 hp2
  have aq := planar_apex key hq1 hq2
  obtain ⟨x, y⟩ := w; obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  simp only [unitVec, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
  fin_cases g <;> simp at hg <;>
  simp [bBg, InD, BotEdge, CellIn, HexIn, Prod.ext_iff] at * <;> omega

end Claude4K3
