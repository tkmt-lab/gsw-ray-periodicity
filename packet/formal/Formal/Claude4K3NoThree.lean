import Formal.Claude4K3Vtx
import Formal.Claude2K3TwoCommon

/-!
# K3: no edge has three common neighbours (every triangle is a face)

Written by a Claude worker (2026-10-20, K3 bridge).

For `r, s ≥ 2` the sphere K3(r,s) is cut into the top cap, the tube and the bottom cap.  Each cap
is a flat triangle `Δ` (position `Pos`, injective), the tube is a flat cylinder (invariant `th`,
injective).  Every edge lies in one piece.

* `classify` : the three edges of a triangle of the graph lie, in coordinates, in one piece: three
  pairwise adjacent points of `Δ` (`CapMode`) or of the tube (`TubeMode`).  At the seams this uses
  that a tube edge between seam points is a cap edge, and that a chord across a cap corner has no
  common tube neighbour off the seam;
* `noThree` : hence an edge has at most two common neighbours: in one piece by the planar count,
  across a seam because only one unit triangle on a seam edge lies in each piece;
* `k3_statement` : **the K3 classification `Claude2Aligned.K3Statement`** (from
  `k3_statement_of_no_three`).
-/

namespace Claude4K3

open ClaudeChallenge Claude2Aligned Claude2K3

variable {r s : ℤ}

theorem unit_neg {d : ℤ × ℤ} (h : Unit d) : Unit (-d) := by
  obtain ⟨d1, d2⟩ := d
  simp only [Unit, Prod.fst_neg, Prod.snd_neg] at h ⊢
  omega

theorem unit_swap {p q : ℤ × ℤ} (h : Unit (q - p)) : Unit (p - q) := by
  have := unit_neg h; rwa [neg_sub] at this

theorem TA_symm {t u : ℤ × ℤ} (h : TA r t u) : TA r u t := by
  simp only [TA, AE] at h ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  · exact Or.inl ⟨by omega, by omega⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))

theorem CE_symm {k : ℕ} {u v : W r s} (h : CE r s k u v) : CE r s k v u := by
  obtain ⟨p, q, hp, hq, h⟩ := h
  exact ⟨q, p, hq, hp, unit_swap h⟩

/-- Three vertices placed at pairwise adjacent points of one cap. -/
def CapMode (r s : ℤ) (k : ℕ) (a b c : W r s) : Prop :=
  ∃ pa pb pc, Pos r s k a pa ∧ Pos r s k b pb ∧ Pos r s k c pc ∧ Unit (pb - pa) ∧
    Unit (pc - pa) ∧ Unit (pc - pb)

/-- Three tube vertices with pairwise adjacent invariants. -/
def TubeMode (hr : 2 ≤ r) (hs : 2 ≤ s) (a b c : W r s) : Prop :=
  InM r s a ∧ InM r s b ∧ InM r s c ∧ TA r (th hr hs a) (th hr hs b) ∧
    TA r (th hr hs a) (th hr hs c) ∧ TA r (th hr hs b) (th hr hs c)

theorem cm_of_CE (hr : 2 ≤ r) (hs : 2 ≤ s) {k : ℕ} (hk : k < 2) {a b c : W r s}
    (h1 : CE r s k a b) (h2 : CE r s k a c) (h3 : CE r s k b c) : CapMode r s k a b c := by
  obtain ⟨pa, pb, ha, hb, u1⟩ := h1
  obtain ⟨pa', pc, ha', hc, u2⟩ := h2
  obtain ⟨pb', pc', hb', hc', u3⟩ := h3
  have e1 := pos_unique hr hs hk ha ha'
  have e2 := pos_unique hr hs hk hb hb'
  have e3 := pos_unique hr hs hk hc hc'
  subst e1; subst e2; subst e3
  exact ⟨pa, pb, pc, ha, hb, hc, u1, u2, u3⟩

theorem cm_swap {k : ℕ} {a b c : W r s} (h : CapMode r s k a b c) : CapMode r s k a c b := by
  obtain ⟨pa, pb, pc, ha, hb, hc, u1, u2, u3⟩ := h
  exact ⟨pa, pc, pb, ha, hc, hb, u2, u1, unit_swap u3⟩

theorem cm_rot {k : ℕ} {a b c : W r s} (h : CapMode r s k a b c) : CapMode r s k b c a := by
  obtain ⟨pa, pb, pc, ha, hb, hc, u1, u2, u3⟩ := h
  exact ⟨pb, pc, pa, hb, hc, ha, u3, unit_swap u1, unit_swap u2⟩

theorem tm_swap {hr : 2 ≤ r} {hs : 2 ≤ s} {a b c : W r s} (h : TubeMode hr hs a b c) :
    TubeMode hr hs a c b := by
  obtain ⟨ha, hb, hc, t1, t2, t3⟩ := h
  exact ⟨ha, hc, hb, t2, t1, TA_symm t3⟩

theorem tm_rot {hr : 2 ≤ r} {hs : 2 ≤ s} {a b c : W r s} (h : TubeMode hr hs a b c) :
    TubeMode hr hs b c a := by
  obtain ⟨ha, hb, hc, t1, t2, t3⟩ := h
  exact ⟨hb, hc, ha, t3, TA_symm t1, TA_symm t2⟩

/-- Some mode. -/
def Mode (hr : 2 ≤ r) (hs : 2 ≤ s) (a b c : W r s) : Prop :=
  CapMode r s 0 a b c ∨ CapMode r s 1 a b c ∨ TubeMode hr hs a b c

theorem mode_swap {hr : 2 ≤ r} {hs : 2 ≤ s} {a b c : W r s} (h : Mode hr hs a b c) :
    Mode hr hs a c b := by
  rcases h with h | h | h
  · exact Or.inl (cm_swap h)
  · exact Or.inr (Or.inl (cm_swap h))
  · exact Or.inr (Or.inr (tm_swap h))

theorem mode_rot {hr : 2 ≤ r} {hs : 2 ≤ s} {a b c : W r s} (h : Mode hr hs a b c) :
    Mode hr hs b c a := by
  rcases h with h | h | h
  · exact Or.inl (cm_rot h)
  · exact Or.inr (Or.inl (cm_rot h))
  · exact Or.inr (Or.inr (tm_rot h))

/-! ## Classification of triangles -/

theorem cl_T (hr : 2 ≤ r) (hs : 2 ≤ s) {u v y : W r s} (h : RT r s u v)
    (hu : (k3Graph r s).Adj u y) (hv : (k3Graph r s).Adj v y) : Mode hr hs u v y := by
  obtain ⟨tu, tv⟩ := T_of_RT h
  by_cases hy : InT r s y
  · have c1 : CE r s 0 u y := by
      rcases adj_types hr hs hu with k | k | k
      · exact e_top k
      · exact absurd (not_TB hr hs tu (B_of_RB k).1) id
      · exact (e_tube_seam_top hr hs k tu hy).1
    have c2 : CE r s 0 v y := by
      rcases adj_types hr hs hv with k | k | k
      · exact e_top k
      · exact absurd (not_TB hr hs tv (B_of_RB k).1) id
      · exact (e_tube_seam_top hr hs k tv hy).1
    exact Or.inl (cm_of_CE hr hs (by omega) (e_top h) c1 c2)
  · have m1 : RMr r s u y := by
      rcases adj_types hr hs hu with k | k | k
      · exact absurd (T_of_RT k).2 hy
      · exact absurd (not_TB hr hs tu (B_of_RB k).1) id
      · exact k
    have m2 : RMr r s v y := by
      rcases adj_types hr hs hv with k | k | k
      · exact absurd (T_of_RT k).2 hy
      · exact absurd (not_TB hr hs tv (B_of_RB k).1) id
      · exact k
    have mu := (M_of_RMr m1).1
    have my := (M_of_RMr m1).2
    have mv := (M_of_RMr m2).1
    rcases e_top_seam hr hs h mu mv with ⟨k, -⟩ | k
    · exact Or.inr (Or.inr ⟨mu, mv, my, k, e_tube hr hs m1, e_tube hr hs m2⟩)
    · exact absurd (T_of_M_TopB hr hs my
        (chordT_apex hr k (RM_of_M hr hs my) (e_tube hr hs m1) (e_tube hr hs m2))) hy

theorem cl_B (hr : 2 ≤ r) (hs : 2 ≤ s) {u v y : W r s} (h : RB r s u v)
    (hu : (k3Graph r s).Adj u y) (hv : (k3Graph r s).Adj v y) : Mode hr hs u v y := by
  obtain ⟨tu, tv⟩ := B_of_RB h
  by_cases hy : InB r s y
  · have c1 : CE r s 1 u y := by
      rcases adj_types hr hs hu with k | k | k
      · exact absurd (not_TB hr hs (T_of_RT k).1 tu) id
      · exact e_bot k
      · exact (e_tube_seam_bot hr hs k tu hy).1
    have c2 : CE r s 1 v y := by
      rcases adj_types hr hs hv with k | k | k
      · exact absurd (not_TB hr hs (T_of_RT k).1 tv) id
      · exact e_bot k
      · exact (e_tube_seam_bot hr hs k tv hy).1
    exact Or.inr (Or.inl (cm_of_CE hr hs (by omega) (e_bot h) c1 c2))
  · have m1 : RMr r s u y := by
      rcases adj_types hr hs hu with k | k | k
      · exact absurd (not_TB hr hs (T_of_RT k).1 tu) id
      · exact absurd (B_of_RB k).2 hy
      · exact k
    have m2 : RMr r s v y := by
      rcases adj_types hr hs hv with k | k | k
      · exact absurd (not_TB hr hs (T_of_RT k).1 tv) id
      · exact absurd (B_of_RB k).2 hy
      · exact k
    have mu := (M_of_RMr m1).1
    have my := (M_of_RMr m1).2
    have mv := (M_of_RMr m2).1
    rcases e_bot_seam hr hs h mu mv with ⟨k, -⟩ | k
    · exact Or.inr (Or.inr ⟨mu, mv, my, k, e_tube hr hs m1, e_tube hr hs m2⟩)
    · exact absurd (B_of_M_BotS hr hs my
        (chordB_apex hr k (RM_of_M hr hs my) (e_tube hr hs m1) (e_tube hr hs m2))) hy

/-- **Every triangle of the graph is flat in one piece.** -/
theorem classify (hr : 2 ≤ r) (hs : 2 ≤ s) {b c x : W r s} (h1 : (k3Graph r s).Adj b c)
    (h2 : (k3Graph r s).Adj b x) (h3 : (k3Graph r s).Adj c x) : Mode hr hs b c x := by
  rcases adj_types hr hs h1 with k | k | k1
  · exact cl_T hr hs k h2 h3
  · exact cl_B hr hs k h2 h3
  rcases adj_types hr hs h2 with k | k | k2
  · exact mode_swap (cl_T hr hs k h1 (h3.symm))
  · exact mode_swap (cl_B hr hs k h1 (h3.symm))
  rcases adj_types hr hs h3 with k | k | k3
  · exact mode_rot (mode_rot (cl_T hr hs k h1.symm h2.symm))
  · exact mode_rot (mode_rot (cl_B hr hs k h1.symm h2.symm))
  exact Or.inr (Or.inr ⟨(M_of_RMr k1).1, (M_of_RMr k1).2, (M_of_RMr k2).2, e_tube hr hs k1,
    e_tube hr hs k2, e_tube hr hs k3⟩)

/-! ## Counting common neighbours -/

theorem cap_three (hr : 2 ≤ r) (hs : 2 ≤ s) {k : ℕ} (hk : k < 2) {b c x y z : W r s}
    (hx : CapMode r s k b c x) (hy : CapMode r s k b c y) (hz : CapMode r s k b c z) :
    x = y ∨ x = z ∨ y = z := by
  obtain ⟨pb, pc, px, hb, hc, hpx, u1, u2, u3⟩ := hx
  obtain ⟨pb', pc', py, hb', hc', hpy, v1, v2, v3⟩ := hy
  obtain ⟨pb'', pc'', pz, hb'', hc'', hpz, w1, w2, w3⟩ := hz
  have e1 := pos_unique hr hs hk hb hb'
  have e2 := pos_unique hr hs hk hc hc'
  have e3 := pos_unique hr hs hk hb hb''
  have e4 := pos_unique hr hs hk hc hc''
  subst e1; subst e2; subst e3; subst e4
  rcases planar_three u1 u2 u3 v2 v3 w2 w3 with h | h | h
  · subst h; exact Or.inl (pos_inj hr hs hk hpx hpy)
  · subst h; exact Or.inr (Or.inl (pos_inj hr hs hk hpx hpz))
  · subst h; exact Or.inr (Or.inr (pos_inj hr hs hk hpy hpz))

theorem tube_three' (hr : 2 ≤ r) (hs : 2 ≤ s) {b c x y z : W r s}
    (hx : TubeMode hr hs b c x) (hy : TubeMode hr hs b c y) (hz : TubeMode hr hs b c z) :
    x = y ∨ x = z ∨ y = z := by
  obtain ⟨mb, mc, mx, t1, t2, t3⟩ := hx
  obtain ⟨-, -, my, -, v2, v3⟩ := hy
  obtain ⟨-, -, mz, -, w2, w3⟩ := hz
  rcases tube_three hr (RM_of_M hr hs mx).1 (RM_of_M hr hs my).1 (RM_of_M hr hs mz).1
    t1 t2 t3 v2 v3 w2 w3 with h | h | h
  · exact Or.inl (th_inj hr hs mx my h)
  · exact Or.inr (Or.inl (th_inj hr hs mx mz h))
  · exact Or.inr (Or.inr (th_inj hr hs my mz h))

/-- Two cap-mode common neighbours coincide when the edge has a unique cap triangle. -/
theorem cap_two (hr : 2 ≤ r) (hs : 2 ≤ s) {k : ℕ} (hk : k < 2) {b c x y : W r s}
    (hu : Uniq r s k b c) (hx : CapMode r s k b c x) (hy : CapMode r s k b c y) : x = y := by
  obtain ⟨pb, pc, px, hb, hc, hpx, u1, u2, u3⟩ := hx
  obtain ⟨pb', pc', py, hb', hc', hpy, v1, v2, v3⟩ := hy
  have e1 := pos_unique hr hs hk hb hb'
  have e2 := pos_unique hr hs hk hc hc'
  subst e1; subst e2
  have := hu pb pc px py hb hc (pos_InD hr hs hpx hk) (pos_InD hr hs hpy hk) u2 u3 v2 v3
  subst this
  exact pos_inj hr hs hk hpx hpy

/-- Mixed top cap / tube: the edge is a seam edge with one triangle on each side. -/
theorem mixed_T (hr : 2 ≤ r) (hs : 2 ≤ s) {b c x y : W r s} (hbc : (k3Graph r s).Adj b c)
    (hx : CapMode r s 0 b c x) (hy : TubeMode hr hs b c y) :
    Uniq r s 0 b c ∧ ∀ y', TubeMode hr hs b c y' → y' = y := by
  obtain ⟨pb, pc, px, hb, hc, -, -, -, -⟩ := hx
  obtain ⟨mb, mc, my, t1, t2, t3⟩ := hy
  have tb := T_of_pos hb
  have tc := T_of_pos hc
  refine ⟨?_, fun y' hy' => ?_⟩
  · rcases adj_types hr hs hbc with k | k | k
    · rcases e_top_seam hr hs k mb mc with ⟨-, hu⟩ | hch
      · exact hu
      · exact absurd t1 (chordT_not_TA hr hch)
    · exact absurd (not_TB hr hs tb (B_of_RB k).1) id
    · exact (e_tube_seam_top hr hs k tb tc).2
  · obtain ⟨-, -, my', -, v2, v3⟩ := hy'
    exact th_inj hr hs my' my (top_tube_apex hr (TopB_of_TM hr hs tb mb) (TopB_of_TM hr hs tc mc)
      t1 (RM_of_M hr hs my') (RM_of_M hr hs my) v2 v3 t2 t3)

theorem mixed_B (hr : 2 ≤ r) (hs : 2 ≤ s) {b c x y : W r s} (hbc : (k3Graph r s).Adj b c)
    (hx : CapMode r s 1 b c x) (hy : TubeMode hr hs b c y) :
    Uniq r s 1 b c ∧ ∀ y', TubeMode hr hs b c y' → y' = y := by
  obtain ⟨pb, pc, px, hb, hc, -, -, -, -⟩ := hx
  obtain ⟨mb, mc, my, t1, t2, t3⟩ := hy
  have tb := B_of_pos hb
  have tc := B_of_pos hc
  refine ⟨?_, fun y' hy' => ?_⟩
  · rcases adj_types hr hs hbc with k | k | k
    · exact absurd (not_TB hr hs (T_of_RT k).1 tb) id
    · rcases e_bot_seam hr hs k mb mc with ⟨-, hu⟩ | hch
      · exact hu
      · exact absurd t1 (chordB_not_TA hr hch)
    · exact (e_tube_seam_bot hr hs k tb tc).2
  · obtain ⟨-, -, my', -, v2, v3⟩ := hy'
    exact th_inj hr hs my' my (bot_tube_apex hr (BotS_of_BM hr hs tb mb) (BotS_of_BM hr hs tc mc)
      t1 (RM_of_M hr hs my') (RM_of_M hr hs my) v2 v3 t2 t3)

theorem not_TB_mode {b c x y : W r s} (hr : 2 ≤ r) (hs : 2 ≤ s) (hx : CapMode r s 0 b c x)
    (hy : CapMode r s 1 b c y) : False := by
  obtain ⟨pb, -, -, hb, -⟩ := hx
  obtain ⟨pb', -, -, hb', -⟩ := hy
  exact not_TB hr hs (T_of_pos hb) (B_of_pos hb')

/-- Two common neighbours in the same mode, and a third one: contradiction. -/
theorem two_same (hr : 2 ≤ r) (hs : 2 ≤ s) {b c x y z : W r s} (hbc : (k3Graph r s).Adj b c)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hz : Mode hr hs b c z)
    (h : (CapMode r s 0 b c x ∧ CapMode r s 0 b c y) ∨ (CapMode r s 1 b c x ∧ CapMode r s 1 b c y) ∨
      (TubeMode hr hs b c x ∧ TubeMode hr hs b c y)) : False := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rcases hz with hz | hz | hz
    · rcases cap_three hr hs (by omega) hx hy hz with e | e | e <;> contradiction
    · exact not_TB_mode hr hs hx hz
    · exact hxy (cap_two hr hs (by omega) (mixed_T hr hs hbc hx hz).1 hx hy)
  · rcases hz with hz | hz | hz
    · exact not_TB_mode hr hs hz hx
    · rcases cap_three hr hs (by omega) hx hy hz with e | e | e <;> contradiction
    · exact hxy (cap_two hr hs (by omega) (mixed_B hr hs hbc hx hz).1 hx hy)
  · rcases hz with hz | hz | hz
    · exact hxy (((mixed_T hr hs hbc hz hx).2 x hx).trans ((mixed_T hr hs hbc hz hx).2 y hy).symm)
    · exact hxy (((mixed_B hr hs hbc hz hx).2 x hx).trans ((mixed_B hr hs hbc hz hx).2 y hy).symm)
    · rcases tube_three' hr hs hx hy hz with e | e | e <;> contradiction

/-- **No edge of K3(r,s) has three common neighbours** (`r, s ≥ 2`). -/
theorem noThree (hr : 2 ≤ r) (hs : 2 ≤ s) : NoThreeCommon r s := by
  intro b c x y z hbc hx hy hz hxy hxz hyz
  have mx := classify hr hs hbc hx.1 hx.2
  have my := classify hr hs hbc hy.1 hy.2
  have mz := classify hr hs hbc hz.1 hz.2
  rcases mx with ax | ax | ax <;> rcases my with ay | ay | ay
  · exact two_same hr hs hbc hxy hxz hyz mz (Or.inl ⟨ax, ay⟩)
  · exact not_TB_mode hr hs ax ay
  · rcases mz with az | az | az
    · exact two_same hr hs hbc hxz hxy (Ne.symm hyz) (Or.inr (Or.inr ay))
        (Or.inl ⟨ax, az⟩)
    · exact not_TB_mode hr hs ax az
    · exact two_same hr hs hbc hyz (Ne.symm hxy) (Ne.symm hxz) (Or.inl ax) (Or.inr (Or.inr ⟨ay, az⟩))
  · exact not_TB_mode hr hs ay ax
  · exact two_same hr hs hbc hxy hxz hyz mz (Or.inr (Or.inl ⟨ax, ay⟩))
  · rcases mz with az | az | az
    · exact not_TB_mode hr hs az ax
    · exact two_same hr hs hbc hxz hxy (Ne.symm hyz) (Or.inr (Or.inr ay))
        (Or.inr (Or.inl ⟨ax, az⟩))
    · exact two_same hr hs hbc hyz (Ne.symm hxy) (Ne.symm hxz) (Or.inr (Or.inl ax))
        (Or.inr (Or.inr ⟨ay, az⟩))
  · rcases mz with az | az | az
    · exact two_same hr hs hbc hyz (Ne.symm hxy) (Ne.symm hxz) (Or.inr (Or.inr ax))
        (Or.inl ⟨ay, az⟩)
    · exact not_TB_mode hr hs ay az
    · exact two_same hr hs hbc hxz hxy (Ne.symm hyz) (Or.inl ay)
        (Or.inr (Or.inr ⟨ax, az⟩))
  · rcases mz with az | az | az
    · exact not_TB_mode hr hs az ay
    · exact two_same hr hs hbc hyz (Ne.symm hxy) (Ne.symm hxz) (Or.inr (Or.inr ax))
        (Or.inr (Or.inl ⟨ay, az⟩))
    · exact two_same hr hs hbc hxz hxy (Ne.symm hyz) (Or.inr (Or.inl ay))
        (Or.inr (Or.inr ⟨ax, az⟩))
  · exact two_same hr hs hbc hxy hxz hyz mz (Or.inr (Or.inr ⟨ax, ay⟩))

/-- **The K3 classification** (`Claude2Aligned.K3Statement`): for `r, s ≥ 2`, K3(r,s) has a
literal path iff `s ≡ ±1 (mod r)`. -/
theorem k3_statement : K3Statement :=
  k3_statement_of_no_three fun r s hr hs => noThree (by exact_mod_cast hr) (by exact_mod_cast hs)

end Claude4K3

#print axioms Claude4K3.noThree
#print axioms Claude4K3.k3_statement
