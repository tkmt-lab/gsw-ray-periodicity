import Formal.Claude4K3SeamAlong
import Formal.Claude2K3NecGcd

/-!
# K3 pieces: vertex-level facts

Written by a Claude worker (2026-10-20, K3 bridge).  For `r, s ≥ 2`:

* `InT`, `InB`, `InM` : the vertex has a site in the top cap, bottom cap, tube;
* `Pos k v p`        : `p ∈ Δ` is the position of `v` in cap `k` (unique `pos_unique`, injective
                       `pos_inj`); `th v` is the tube invariant (injective on tube vertices);
* `RT`, `RB`, `RM'`  : an edge realised in a top cap, bottom cap, tube cell;
* `e_top`, `e_tube`, `e_top_seam`, `e_tube_seam` (and bottom versions) : what such an edge means
  in coordinates.
-/

set_option linter.unusedVariables false

namespace Claude4K3

open ClaudeChallenge Claude2Aligned Claude2K3

variable {r s : ℤ}

abbrev W (r s : ℤ) : Type := (k3Sig r s).Vertex

theorem p0 {r : ℤ} (hr : 2 ≤ r) : 0 < r := by omega

/-- The tube invariant of a vertex. -/
noncomputable def th (hr : 2 ≤ r) (hs : 2 ≤ s) (v : W r s) : ℤ × ℤ := vinv (p0 hr) (p0 hs) v

theorem th_V (hr : 2 ≤ r) (hs : 2 ≤ s) {f : Fin 11} {z : ℤ × ℤ} (hz : CellIn r s f z) :
    th hr hs (V r s f z) = inv r s (f, z) := vinv_V (p0 hr) (p0 hs) hz

def InT (r s : ℤ) (v : W r s) : Prop := ∃ f z, f.val < 4 ∧ CellIn r s f z ∧ V r s f z = v
def InB (r s : ℤ) (v : W r s) : Prop :=
  ∃ f z, 4 ≤ f.val ∧ f.val < 8 ∧ CellIn r s f z ∧ V r s f z = v
def InM (r s : ℤ) (v : W r s) : Prop := ∃ g w, 8 ≤ g.val ∧ CellIn r s g w ∧ V r s g w = v

def Pos (r s : ℤ) (k : ℕ) (v : W r s) (p : ℤ × ℤ) : Prop :=
  ∃ f z, capOf f = k ∧ CellIn r s f z ∧ V r s f z = v ∧ dC r f z = p

theorem capOf_top {f : Fin 11} : capOf f = 0 ↔ f.val < 4 := by
  fin_cases f <;> simp [capOf]

theorem capOf_bot {f : Fin 11} : capOf f = 1 ↔ (4 ≤ f.val ∧ f.val < 8) := by
  fin_cases f <;> simp [capOf]

theorem pos_unique (hr : 2 ≤ r) (hs : 2 ≤ s) {k : ℕ} (hk : k < 2) {v : W r s} {p q : ℤ × ℤ}
    (hp : Pos r s k v p) (hq : Pos r s k v q) : p = q := by
  obtain ⟨f, z, hf, hz, rfl, rfl⟩ := hp
  obtain ⟨g, w, hg, hw, he, rfl⟩ := hq
  exact dC_wd hr hs (by omega) (by omega) hz hw (V_inv3 (p0 hr) (p0 hs) hz hw he.symm)

theorem pos_inj (hr : 2 ≤ r) (hs : 2 ≤ s) {k : ℕ} (hk : k < 2) {v w : W r s} {p : ℤ × ℤ}
    (hv : Pos r s k v p) (hw : Pos r s k w p) : v = w := by
  obtain ⟨f, z, hf, hz, rfl, rfl⟩ := hv
  obtain ⟨g, u, hg, hu, rfl, he⟩ := hw
  exact dC_inj hr hs (by omega) (by omega) hz hu he.symm

theorem th_inj (hr : 2 ≤ r) (hs : 2 ≤ s) {v w : W r s} (hv : InM r s v) (hw : InM r s w)
    (h : th hr hs v = th hr hs w) : v = w := by
  obtain ⟨g, a, hg, ha, rfl⟩ := hv
  obtain ⟨g', b, hg', hb, rfl⟩ := hw
  rw [th_V hr hs ha, th_V hr hs hb] at h
  exact tube_inj hr hs hg hg' ha hb h

theorem pos_of_T {v : W r s} (h : InT r s v) : ∃ p, Pos r s 0 v p := by
  obtain ⟨f, z, hf, hz, rfl⟩ := h
  exact ⟨_, f, z, capOf_top.2 hf, hz, rfl, rfl⟩

theorem T_of_pos {v : W r s} {p : ℤ × ℤ} (h : Pos r s 0 v p) : InT r s v := by
  obtain ⟨f, z, hf, hz, rfl, -⟩ := h
  exact ⟨f, z, capOf_top.1 hf, hz, rfl⟩

theorem pos_of_B {v : W r s} (h : InB r s v) : ∃ p, Pos r s 1 v p := by
  obtain ⟨f, z, hf1, hf, hz, rfl⟩ := h
  exact ⟨_, f, z, capOf_bot.2 ⟨hf1, hf⟩, hz, rfl, rfl⟩

theorem B_of_pos {v : W r s} {p : ℤ × ℤ} (h : Pos r s 1 v p) : InB r s v := by
  obtain ⟨f, z, hf, hz, rfl, -⟩ := h
  exact ⟨f, z, (capOf_bot.1 hf).1, (capOf_bot.1 hf).2, hz, rfl⟩

theorem pos_InD (hr : 2 ≤ r) (hs : 2 ≤ s) {k : ℕ} {v : W r s} {p : ℤ × ℤ}
    (h : Pos r s k v p) (hk : k < 2) : InD r p := by
  obtain ⟨f, z, hf, hz, rfl, rfl⟩ := h
  by_cases h4 : f.val < 4
  · exact (val_top hr hs h4 hz).2.2.1
  · have : 4 ≤ f.val ∧ f.val < 8 := capOf_bot.1 (by simp only [capOf] at hf ⊢; split_ifs at hf ⊢ <;> omega)
    exact (val_bot hr hs this.1 this.2 hz).2.2.1

theorem RM_of_M (hr : 2 ≤ r) (hs : 2 ≤ s) {v : W r s} (h : InM r s v) : RM r s (th hr hs v) := by
  obtain ⟨g, w, hg, hw, rfl⟩ := h
  rw [th_V hr hs hw]; exact val_tube hr hs hg hw

theorem TopB_of_TM (hr : 2 ≤ r) (hs : 2 ≤ s) {v : W r s} (ht : InT r s v) (hm : InM r s v) :
    TopB r (th hr hs v) := by
  have h1 := RM_of_M hr hs hm
  obtain ⟨f, z, hf, hz, rfl⟩ := ht
  rw [th_V hr hs hz] at h1 ⊢
  have h2 := val_top hr hs hf hz
  exact ⟨h2.1, by have := h1.2.1; have := h2.2.1; omega⟩

theorem BotS_of_BM (hr : 2 ≤ r) (hs : 2 ≤ s) {v : W r s} (ht : InB r s v) (hm : InM r s v) :
    BotS r s (th hr hs v) := by
  have h1 := RM_of_M hr hs hm
  obtain ⟨f, z, hf1, hf, hz, rfl⟩ := ht
  rw [th_V hr hs hz] at h1 ⊢
  have h2 := val_bot hr hs hf1 hf hz
  exact ⟨h2.1, by have := h1.2.2; have := h2.2.1; omega⟩

theorem not_TB (hr : 2 ≤ r) (hs : 2 ≤ s) {v : W r s} (ht : InT r s v) (hb : InB r s v) : False := by
  obtain ⟨f, z, hf, hz, rfl⟩ := ht
  obtain ⟨g, w, hg1, hg, hw, he⟩ := hb
  have e := V_inv3 (p0 hr) (p0 hs) hw hz he
  have h1 := (val_top hr hs hf hz).2.2.2
  have h2 := (val_bot hr hs hg1 hg hw).2.2.2
  have : inv r s (g, w) = inv r s (f, z) := congrArg Prod.fst e
  rw [this] at h2
  omega

theorem T_of_M_TopB (hr : 2 ≤ r) (hs : 2 ≤ s) {v : W r s} (hm : InM r s v)
    (h : TopB r (th hr hs v)) : InT r s v := by
  obtain ⟨g, w, hg, hw, rfl⟩ := hm
  rw [th_V hr hs hw] at h
  obtain ⟨f, z, hf, hz, he⟩ := tube_top_cap hr hs hg hw (topEdge_of_TopB hr hs hg hw h)
  exact ⟨f, z, hf, hz, he⟩

theorem B_of_M_BotS (hr : 2 ≤ r) (hs : 2 ≤ s) {v : W r s} (hm : InM r s v)
    (h : BotS r s (th hr hs v)) : InB r s v := by
  obtain ⟨g, w, hg, hw, rfl⟩ := hm
  rw [th_V hr hs hw] at h
  obtain ⟨f, z, hf1, hf, hz, he⟩ := tube_bot_cap hr hs hg hw (botEdge_of_BotS hr hs hg hw h)
  exact ⟨f, z, hf1, hf, hz, he⟩

/-! ## Edges -/

def Real (r s : ℤ) (f : Fin 11) (u v : W r s) : Prop :=
  ∃ z d, d ∈ unitVec ∧ CellIn r s f z ∧ CellIn r s f (z + d) ∧ V r s f z = u ∧ V r s f (z + d) = v

theorem real_symm {f : Fin 11} {u v : W r s} (h : Real r s f u v) : Real r s f v u := by
  obtain ⟨z, d, hd, hz, hz', rfl, rfl⟩ := h
  exact ⟨z + d, -d, unitVec_neg hd, hz', by simpa using hz, rfl, by simp⟩

theorem real_of_adj (hr : 2 ≤ r) (hs : 2 ≤ s) {u v : W r s} (h : (k3Graph r s).Adj u v) :
    ∃ f, Real r s f u v := by
  obtain ⟨f, z, d, hd, hz, hz', e1, e2⟩ := first_edge (p0 hr) (p0 hs) h
  exact ⟨f, z, d, hd, hz, hz', e1, e2⟩

def RT (r s : ℤ) (u v : W r s) : Prop := ∃ f, f.val < 4 ∧ Real r s f u v
def RB (r s : ℤ) (u v : W r s) : Prop := ∃ f, 4 ≤ f.val ∧ f.val < 8 ∧ Real r s f u v
def RMr (r s : ℤ) (u v : W r s) : Prop := ∃ f, 8 ≤ f.val ∧ Real r s f u v

theorem adj_types (hr : 2 ≤ r) (hs : 2 ≤ s) {u v : W r s} (h : (k3Graph r s).Adj u v) :
    RT r s u v ∨ RB r s u v ∨ RMr r s u v := by
  obtain ⟨f, hf⟩ := real_of_adj hr hs h
  by_cases h4 : f.val < 4
  · exact Or.inl ⟨f, h4, hf⟩
  by_cases h8 : f.val < 8
  · exact Or.inr (Or.inl ⟨f, by omega, h8, hf⟩)
  · exact Or.inr (Or.inr ⟨f, by omega, hf⟩)

theorem RT_symm {u v : W r s} (h : RT r s u v) : RT r s v u := by
  obtain ⟨f, hf, h⟩ := h; exact ⟨f, hf, real_symm h⟩
theorem RB_symm {u v : W r s} (h : RB r s u v) : RB r s v u := by
  obtain ⟨f, hf1, hf, h⟩ := h; exact ⟨f, hf1, hf, real_symm h⟩
theorem RMr_symm {u v : W r s} (h : RMr r s u v) : RMr r s v u := by
  obtain ⟨f, hf, h⟩ := h; exact ⟨f, hf, real_symm h⟩

theorem T_of_RT {u v : W r s} (h : RT r s u v) : InT r s u ∧ InT r s v := by
  obtain ⟨f, hf, z, d, hd, hz, hz', rfl, rfl⟩ := h
  exact ⟨⟨f, z, hf, hz, rfl⟩, ⟨f, z + d, hf, hz', rfl⟩⟩
theorem B_of_RB {u v : W r s} (h : RB r s u v) : InB r s u ∧ InB r s v := by
  obtain ⟨f, hf1, hf, z, d, hd, hz, hz', rfl, rfl⟩ := h
  exact ⟨⟨f, z, hf1, hf, hz, rfl⟩, ⟨f, z + d, hf1, hf, hz', rfl⟩⟩
theorem M_of_RMr {u v : W r s} (h : RMr r s u v) : InM r s u ∧ InM r s v := by
  obtain ⟨f, hf, z, d, hd, hz, hz', rfl, rfl⟩ := h
  exact ⟨⟨f, z, hf, hz, rfl⟩, ⟨f, z + d, hf, hz', rfl⟩⟩

/-- Cap adjacency in coordinates. -/
def CE (r s : ℤ) (k : ℕ) (u v : W r s) : Prop :=
  ∃ p q, Pos r s k u p ∧ Pos r s k v q ∧ Unit (q - p)

/-- Only one unit triangle of `Δ` on the cap edge `u v`. -/
def Uniq (r s : ℤ) (k : ℕ) (u v : W r s) : Prop :=
  ∀ pu pv p q, Pos r s k u pu → Pos r s k v pv → InD r p → InD r q → Unit (p - pu) →
    Unit (p - pv) → Unit (q - pu) → Unit (q - pv) → p = q

theorem e_top {u v : W r s} (h : RT r s u v) : CE r s 0 u v := by
  obtain ⟨f, hf, z, d, hd, hz, hz', rfl, rfl⟩ := h
  exact ⟨_, _, ⟨f, z, capOf_top.2 hf, hz, rfl, rfl⟩, ⟨f, z + d, capOf_top.2 hf, hz', rfl, rfl⟩,
    cap_edge (by rw [capOf_top.2 hf]; omega) hd⟩

theorem e_bot {u v : W r s} (h : RB r s u v) : CE r s 1 u v := by
  obtain ⟨f, hf1, hf, z, d, hd, hz, hz', rfl, rfl⟩ := h
  exact ⟨_, _, ⟨f, z, capOf_bot.2 ⟨hf1, hf⟩, hz, rfl, rfl⟩,
    ⟨f, z + d, capOf_bot.2 ⟨hf1, hf⟩, hz', rfl, rfl⟩, cap_edge (by rw [capOf_bot.2 ⟨hf1, hf⟩]; omega) hd⟩

theorem e_tube (hr : 2 ≤ r) (hs : 2 ≤ s) {u v : W r s} (h : RMr r s u v) :
    TA r (th hr hs u) (th hr hs v) := by
  obtain ⟨g, hg, z, d, hd, hz, hz', rfl, rfl⟩ := h
  rw [th_V hr hs hz, th_V hr hs hz']
  exact tube_edge hr hs hg hz hz' hd

theorem e_top_seam (hr : 2 ≤ r) (hs : 2 ≤ s) {u v : W r s} (h : RT r s u v) (hu : InM r s u)
    (hv : InM r s v) :
    (TA r (th hr hs u) (th hr hs v) ∧ Uniq r s 0 u v) ∨ ChordT r (th hr hs u) (th hr hs v) := by
  have tu := TopB_of_TM hr hs (T_of_RT h).1 hu
  have tv := TopB_of_TM hr hs (T_of_RT h).2 hv
  obtain ⟨f, hf, z, d, hd, hz, hz', rfl, rfl⟩ := h
  rw [th_V hr hs hz] at tu ⊢
  rw [th_V hr hs hz'] at tv ⊢
  rcases seam_cases_top hr hf hz hz' hd (outer_top hr hs hf hz tu) (outer_top hr hs hf hz' tv)
    with ha | hc
  · refine Or.inl ⟨along_TA_top hr ha hd hz hz', ?_⟩
    intro pu pv p q hpu hpv hp hq h1 h2 h3 h4
    have e1 := pos_unique hr hs (by omega) hpu ⟨f, z, capOf_top.2 hf, hz, rfl, rfl⟩
    have e2 := pos_unique hr hs (by omega) hpv ⟨f, z + d, capOf_top.2 hf, hz', rfl, rfl⟩
    subst e1; subst e2
    exact along_uniq_top hr ha hd hz hz' hp hq h1 h2 h3 h4
  · exact Or.inr (chord_top hr hc)

theorem e_bot_seam (hr : 2 ≤ r) (hs : 2 ≤ s) {u v : W r s} (h : RB r s u v) (hu : InM r s u)
    (hv : InM r s v) :
    (TA r (th hr hs u) (th hr hs v) ∧ Uniq r s 1 u v) ∨ ChordB r s (th hr hs u) (th hr hs v) := by
  have tu := BotS_of_BM hr hs (B_of_RB h).1 hu
  have tv := BotS_of_BM hr hs (B_of_RB h).2 hv
  obtain ⟨f, hf1, hf, z, d, hd, hz, hz', rfl, rfl⟩ := h
  rw [th_V hr hs hz] at tu ⊢
  rw [th_V hr hs hz'] at tv ⊢
  rcases seam_cases_bot hr hf1 hf hz hz' hd (outer_bot hr hs hf1 hf hz tu)
    (outer_bot hr hs hf1 hf hz' tv) with ha | hc
  · refine Or.inl ⟨along_TA_bot hr ha hd hz hz', ?_⟩
    intro pu pv p q hpu hpv hp hq h1 h2 h3 h4
    have e1 := pos_unique hr hs (by omega) hpu ⟨f, z, capOf_bot.2 ⟨hf1, hf⟩, hz, rfl, rfl⟩
    have e2 := pos_unique hr hs (by omega) hpv ⟨f, z + d, capOf_bot.2 ⟨hf1, hf⟩, hz', rfl, rfl⟩
    subst e1; subst e2
    exact along_uniq_bot hr ha hd hz hz' hp hq h1 h2 h3 h4
  · exact Or.inr (chord_bot hr hc)

theorem e_tube_seam_top (hr : 2 ≤ r) (hs : 2 ≤ s) {u v : W r s} (h : RMr r s u v)
    (hu : InT r s u) (hv : InT r s v) : CE r s 0 u v ∧ Uniq r s 0 u v := by
  obtain ⟨g, hg, w, d, hd, hw, hw', rfl, rfl⟩ := h
  obtain ⟨f1, z1, hf1, hz1, e1⟩ := hu
  obtain ⟨f2, z2, hf2, hz2, e2⟩ := hv
  obtain ⟨t1, b1⟩ := bc_top hr hs hf1 hg hz1 hw (V_inv3 (p0 hr) (p0 hs) hz1 hw e1)
  obtain ⟨t2, b2⟩ := bc_top hr hs hf2 hg hz2 hw' (V_inv3 (p0 hr) (p0 hs) hz2 hw' e2)
  obtain ⟨k1, k2⟩ := tube_seam_top hr hs hg hw hw' hd t1 t2
  have P1 : Pos r s 0 (V r s g w) (bTg r g w) := ⟨f1, z1, capOf_top.2 hf1, hz1, e1, b1⟩
  have P2 : Pos r s 0 (V r s g (w + d)) (bTg r g (w + d)) := ⟨f2, z2, capOf_top.2 hf2, hz2, e2, b2⟩
  refine ⟨⟨_, _, P1, P2, k1⟩, ?_⟩
  intro pu pv p q hpu hpv hp hq h1 h2 h3 h4
  have q1 := pos_unique hr hs (by omega) hpu P1
  have q2 := pos_unique hr hs (by omega) hpv P2
  subst q1; subst q2
  exact k2 p q hp hq h1 h2 h3 h4

theorem e_tube_seam_bot (hr : 2 ≤ r) (hs : 2 ≤ s) {u v : W r s} (h : RMr r s u v)
    (hu : InB r s u) (hv : InB r s v) : CE r s 1 u v ∧ Uniq r s 1 u v := by
  obtain ⟨g, hg, w, d, hd, hw, hw', rfl, rfl⟩ := h
  obtain ⟨f1, z1, hf1', hf1, hz1, e1⟩ := hu
  obtain ⟨f2, z2, hf2', hf2, hz2, e2⟩ := hv
  obtain ⟨t1, b1⟩ := bc_bot hr hs hf1' hf1 hg hz1 hw (V_inv3 (p0 hr) (p0 hs) hz1 hw e1)
  obtain ⟨t2, b2⟩ := bc_bot hr hs hf2' hf2 hg hz2 hw' (V_inv3 (p0 hr) (p0 hs) hz2 hw' e2)
  obtain ⟨k1, k2⟩ := tube_seam_bot hr hs hg hw hw' hd t1 t2
  have P1 : Pos r s 1 (V r s g w) (bBg r g w) := ⟨f1, z1, capOf_bot.2 ⟨hf1', hf1⟩, hz1, e1, b1⟩
  have P2 : Pos r s 1 (V r s g (w + d)) (bBg r g (w + d)) :=
    ⟨f2, z2, capOf_bot.2 ⟨hf2', hf2⟩, hz2, e2, b2⟩
  refine ⟨⟨_, _, P1, P2, k1⟩, ?_⟩
  intro pu pv p q hpu hpv hp hq h1 h2 h3 h4
  have q1 := pos_unique hr hs (by omega) hpu P1
  have q2 := pos_unique hr hs (by omega) hpv P2
  subst q1; subst q2
  exact k2 p q hp hq h1 h2 h3 h4

end Claude4K3
