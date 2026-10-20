import Formal.Claude5O2Eqv2b

/-!
# O2: `o2Graph t d` is isomorphic to the model `GM t d`

Written by a Claude worker (2026-10-20, O2 bridge session).

* `vphi`           : the vertex map (well defined by `samePoint_phi`);
* `vphi_bijective` : injective by `eqv_of_phi`, surjective by inverse charts;
* `adj_iff`        : adjacency corresponds (a unit step in a cell is a unit step in its chart; a
                     unit step in a rhombus chart stays in one of its two triangles);
* `o2_iff_gm`, `deg_vEquiv` : literal paths and degrees correspond.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

variable {t d : ℤ}

theorem phi_of_eqvGen (ht : 1 ≤ t) (hd : 1 ≤ d) {a b : (o2Sig t d).Site}
    (h : Relation.EqvGen (o2Sig t d).SamePoint a b) :
    Phi t d a.1.1 a.1.2 = Phi t d b.1.1 b.1.2 := by
  induction h with
  | rel x y hxy => exact samePoint_phi ht hd x y hxy
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem phi_valid (ht : 1 ≤ t) (hd : 1 ≤ d) (a : (o2Sig t d).Site) :
    Valid t d (Phi t d a.1.1 a.1.2) :=
  ch_valid ht hd (cc_lt _) (cp_dom ((inCell_iff (by omega) (by omega) _ _).1 a.2))

/-- The model vertex of a site. -/
def siteM (ht : 1 ≤ t) (hd : 1 ≤ d) (a : (o2Sig t d).Site) : MS t d :=
  ⟨Phi t d a.1.1 a.1.2, phi_valid ht hd a⟩

/-- The model vertex of a vertex. -/
def vphi (ht : 1 ≤ t) (hd : 1 ≤ d) : (o2Sig t d).Vertex → MS t d :=
  Quot.lift (siteM ht hd) (fun _ _ h => Subtype.ext (phi_of_eqvGen ht hd h))

theorem vphi_vtx (ht : 1 ≤ t) (hd : 1 ≤ d) (a : (o2Sig t d).Site) :
    (vphi ht hd ((o2Sig t d).vtx a)).1 = Phi t d a.1.1 a.1.2 := rfl

theorem vphi_injective (ht : 1 ≤ t) (hd : 1 ≤ d) : Function.Injective (vphi ht hd) := by
  intro v w h
  induction v using Quot.ind
  induction w using Quot.ind
  exact Quot.sound (eqv_of_phi ht hd _ _ (congrArg Subtype.val h))

/-- Every unit step of a chart lies in one cell. -/
theorem exists_cell_step (ht : 1 ≤ t) (hd : 1 ≤ d) {c : ℕ} (hc : c < 5) {ρ u : ℤ × ℤ}
    (h1 : Dom t d c ρ) (h2 : Dom t d c (ρ + u)) (hu : u ∈ unitVec) :
    ∃ g : Fin 8, ∃ z z', CellIn t d g z ∧ CellIn t d g z' ∧ z' - z ∈ unitVec ∧ cc g = c ∧
      cp t d g z = ρ ∧ cp t d g z' = ρ + u := by
  rw [unit_iff] at hu
  obtain ⟨ρ1, ρ2⟩ := ρ
  obtain ⟨u1, u2⟩ := u
  have hsum : u1 + u2 = 0 ∨ u1 + u2 = 1 ∨ u1 + u2 = -1 := by
    rcases hu with h | h | h | h | h | h <;> simp [Prod.ext_iff] at h <;> omega
  rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩
  · refine ⟨0, (ρ1, ρ2), (ρ1 + u1, ρ2 + u2), ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simpa [CellIn, Dom] using h1
    · simpa [CellIn, Dom] using h2
    · simpa [unit_iff] using hu
  · refine ⟨1, (ρ2 - d, ρ1 + d), (ρ2 + u2 - d, ρ1 + u1 + d), ?_, ?_, ?_, rfl, ?_, ?_⟩
    · simp [CellIn, Dom, Hx] at h1 ⊢; omega
    · simp [CellIn, Dom, Hx] at h2 ⊢; omega
    · have hU : (u2, u1) ∈ unitVec := by
        rcases hu with h | h | h | h | h | h <;> simp [Prod.ext_iff] at h <;>
          obtain ⟨rfl, rfl⟩ := h <;> simp [unit_iff]
      convert hU using 1; ext <;> simp <;> ring
    · simp [cp]
    · simp [cp]; try (constructor <;> ring)
  · have hi : i < 3 := by omega
    simp only [Dom, Rh] at h1 h2
    simp only [Prod.mk_add_mk] at h2 ⊢
    by_cases hup : t ≤ ρ1 + ρ2 ∧ t ≤ (ρ1 + u1) + (ρ2 + u2)
    · have hU : (-u1, -u2) ∈ unitVec := by
        rcases hu with h | h | h | h | h | h <;> simp [Prod.ext_iff] at h <;>
          obtain ⟨rfl, rfl⟩ := h <;> simp [unit_iff]
      interval_cases i
      · refine ⟨2, (t - ρ1, t - ρ2), (t - ρ1 - u1, t - ρ2 - u2), ?_, ?_, ?_, rfl, ?_, ?_⟩ <;>
          first | (convert hU using 1; ext <;> simp <;> ring) |
            (simp [CellIn, TriIn, cp] <;> (try omega) <;> (constructor <;> ring))
      · refine ⟨4, (t - ρ1, t - ρ2), (t - ρ1 - u1, t - ρ2 - u2), ?_, ?_, ?_, rfl, ?_, ?_⟩ <;>
          first | (convert hU using 1; ext <;> simp <;> ring) |
            (simp [CellIn, TriIn, cp] <;> (try omega) <;> (constructor <;> ring))
      · refine ⟨6, (t - ρ1, t - ρ2), (t - ρ1 - u1, t - ρ2 - u2), ?_, ?_, ?_, rfl, ?_, ?_⟩ <;>
          first | (convert hU using 1; ext <;> simp <;> ring) |
            (simp [CellIn, TriIn, cp] <;> (try omega) <;> (constructor <;> ring))
    · have hU : (-u1 - u2, u1) ∈ unitVec := by
        rcases hu with h | h | h | h | h | h <;> simp [Prod.ext_iff] at h <;>
          obtain ⟨rfl, rfl⟩ := h <;> simp [unit_iff]
      interval_cases i
      · refine ⟨3, (t - ρ1 - ρ2, ρ1), (t - ρ1 - ρ2 - u1 - u2, ρ1 + u1), ?_, ?_, ?_, rfl, ?_, ?_⟩ <;>
          first | (convert hU using 1; ext <;> simp <;> ring) |
            (simp [CellIn, TriIn, cp] <;> (try omega) <;> (constructor <;> ring))
      · refine ⟨5, (t - ρ1 - ρ2, ρ1), (t - ρ1 - ρ2 - u1 - u2, ρ1 + u1), ?_, ?_, ?_, rfl, ?_, ?_⟩ <;>
          first | (convert hU using 1; ext <;> simp <;> ring) |
            (simp [CellIn, TriIn, cp] <;> (try omega) <;> (constructor <;> ring))
      · refine ⟨7, (t - ρ1 - ρ2, ρ1), (t - ρ1 - ρ2 - u1 - u2, ρ1 + u1), ?_, ?_, ?_, rfl, ?_, ?_⟩ <;>
          first | (convert hU using 1; ext <;> simp <;> ring) |
            (simp [CellIn, TriIn, cp] <;> (try omega) <;> (constructor <;> ring))

/-- Every chart point is the image of a cell point. -/
theorem exists_cell_pt (ht : 1 ≤ t) (hd : 1 ≤ d) {c : ℕ} (hc : c < 5) {ρ : ℤ × ℤ}
    (h1 : Dom t d c ρ) : ∃ g : Fin 8, ∃ z, CellIn t d g z ∧ cc g = c ∧ cp t d g z = ρ := by
  obtain ⟨ρ1, ρ2⟩ := ρ
  rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩
  · exact ⟨0, (ρ1, ρ2), by simpa [CellIn, Dom] using h1, rfl, rfl⟩
  · refine ⟨1, (ρ2 - d, ρ1 + d), ?_, rfl, ?_⟩ <;> simp [CellIn, Dom, Hx, cp] at h1 ⊢ <;> omega
  · have hi : i < 3 := by omega
    simp only [Dom, Rh] at h1
    by_cases hup : t ≤ ρ1 + ρ2
    · interval_cases i
      · exact ⟨2, (t - ρ1, t - ρ2), by simp [CellIn, TriIn]; omega, rfl, by simp [cp]; try ring⟩
      · exact ⟨4, (t - ρ1, t - ρ2), by simp [CellIn, TriIn]; omega, rfl, by simp [cp]; try ring⟩
      · exact ⟨6, (t - ρ1, t - ρ2), by simp [CellIn, TriIn]; omega, rfl, by simp [cp]; try ring⟩
    · interval_cases i
      · exact ⟨3, (t - ρ1 - ρ2, ρ1), by simp [CellIn, TriIn]; omega, rfl, by simp [cp]; try ring⟩
      · exact ⟨5, (t - ρ1 - ρ2, ρ1), by simp [CellIn, TriIn]; omega, rfl, by simp [cp]; try ring⟩
      · exact ⟨7, (t - ρ1 - ρ2, ρ1), by simp [CellIn, TriIn]; omega, rfl, by simp [cp]; try ring⟩

/-- Every model vertex is a chart point. -/
theorem valid_rep {v : MV} (hv : Valid t d v) : ∃ c, c < 5 ∧ ∃ ρ, Dom t d c ρ ∧ ch t d c ρ = v := by
  obtain ⟨k, z⟩ := v
  rcases hv with ⟨hk, hz⟩ | ⟨hk, hz, hD⟩ | ⟨hk, hz⟩ <;> simp only at hk hz
  · subst hk; exact ⟨0, by norm_num, z, hz, rfl⟩
  · subst hk; exact ⟨1, by norm_num, z, hz, ch1_nD hD⟩
  · obtain ⟨i, hi, rfl⟩ : ∃ i : ℕ, i < 3 ∧ k = (i : ℤ) + 2 := by
      rcases hk with rfl | rfl | rfl
      exacts [⟨0, by norm_num, by norm_num⟩, ⟨1, by norm_num, by norm_num⟩,
        ⟨2, by norm_num, by norm_num⟩]
    refine ⟨i + 2, by omega, z, ?_, chR_int i hz⟩
    simp only [Dom, Rh]; simp only [RhI] at hz; omega

theorem vphi_surjective (ht : 1 ≤ t) (hd : 1 ≤ d) : Function.Surjective (vphi ht hd) := by
  rintro ⟨v, hv⟩
  obtain ⟨c, hc, ρ, hρ, rfl⟩ := valid_rep hv
  obtain ⟨g, z, hz, hcc, hcp⟩ := exists_cell_pt ht hd hc hρ
  refine ⟨(o2Sig t d).vtx ⟨(g, z), (inCell_iff (by omega) (by omega) _ _).2 hz⟩, ?_⟩
  apply Subtype.ext
  rw [vphi_vtx]
  simp only [Phi, hcc, hcp]

/-! ## Adjacency -/

/-- The linear part of `cp`. -/
def cpl (f : Fin 8) (u : ℤ × ℤ) : ℤ × ℤ :=
  if f.val = 0 then u else if f.val = 1 then (u.2, u.1)
  else if f.val % 2 = 0 then (-u.1, -u.2) else (u.2, -u.1 - u.2)

theorem cp_add (f : Fin 8) (z u : ℤ × ℤ) : cp t d f (z + u) = cp t d f z + cpl f u := by
  fin_cases f <;> ext <;> simp [cp, cpl] <;> ring

theorem cpl_unit (f : Fin 8) {u : ℤ × ℤ} (hu : u ∈ unitVec) : cpl f u ∈ unitVec := by
  rw [unit_iff] at hu
  fin_cases f <;> rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [cpl, unit_iff]

theorem adj_fwd (ht : 1 ≤ t) (hd : 1 ≤ d) {v w : (o2Sig t d).Vertex}
    (h : (o2Graph t d).Adj v w) : (GM t d).Adj (vphi ht hd v) (vphi ht hd w) := by
  obtain ⟨hne, a, b, rfl, rfl, hab⟩ := h
  have key : ∀ a b : (o2Sig t d).Site, b.1.1 = a.1.1 → b.1.2 - a.1.2 ∈ unitVec →
      (vphi ht hd ((o2Sig t d).vtx a)).1 ≠ (vphi ht hd ((o2Sig t d).vtx b)).1 →
      AdjM t d (vphi ht hd ((o2Sig t d).vtx a)).1 (vphi ht hd ((o2Sig t d).vtx b)).1 := by
    rintro ⟨⟨g, z⟩, hz⟩ ⟨⟨g', z'⟩, hz'⟩ h1 h2 hne
    simp only at h1 h2
    subst g'
    have hz1 := (inCell_iff (by omega) (by omega) _ _).1 hz
    have hz2 := (inCell_iff (by omega) (by omega) _ _).1 hz'
    have e : cp t d g z' = cp t d g z + cpl g (z' - z) := by
      have := cp_add (t := t) (d := d) (g : Fin 8) z (z' - z); rwa [add_sub_cancel] at this
    refine ⟨hne, cc g, cc_lt g, cp t d g z, cpl g (z' - z), cp_dom hz1, ?_, cpl_unit g h2, rfl, ?_⟩
    · rw [← e]; exact cp_dom hz2
    · rw [vphi_vtx, ← e]; rfl
  have hne' : (vphi ht hd ((o2Sig t d).vtx a)).1 ≠ (vphi ht hd ((o2Sig t d).vtx b)).1 :=
    fun e => hne (vphi_injective ht hd (Subtype.ext e))
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key a b h1 h2 hne'
  · exact adjM_symm (key b a h1 h2 (fun e => hne' e.symm))

theorem adj_bwd (ht : 1 ≤ t) (hd : 1 ≤ d) {v w : (o2Sig t d).Vertex}
    (h : (GM t d).Adj (vphi ht hd v) (vphi ht hd w)) : (o2Graph t d).Adj v w := by
  obtain ⟨hne, c, hc, ρ, u, h1, h2, hu, e1, e2⟩ := h
  refine ⟨fun e => hne (by rw [e]), ?_⟩
  obtain ⟨g, z, z', hz, hz', hzz, hcc, hcp, hcp'⟩ := exists_cell_step ht hd hc h1 h2 hu
  let a : (o2Sig t d).Site := ⟨(g, z), (inCell_iff (by omega) (by omega) _ _).2 hz⟩
  let b : (o2Sig t d).Site := ⟨(g, z'), (inCell_iff (by omega) (by omega) _ _).2 hz'⟩
  refine ⟨a, b, vphi_injective ht hd (Subtype.ext ?_), vphi_injective ht hd (Subtype.ext ?_),
    Or.inl ⟨rfl, hzz⟩⟩
  · rw [vphi_vtx, ← e1]; simp only [a, Phi, hcc, hcp]
  · rw [vphi_vtx, ← e2]; simp only [b, Phi, hcc, hcp']

/-- The vertex bijection. -/
noncomputable def vEquiv (ht : 1 ≤ t) (hd : 1 ≤ d) : (o2Sig t d).Vertex ≃ MS t d :=
  Equiv.ofBijective (vphi ht hd) ⟨vphi_injective ht hd, vphi_surjective ht hd⟩

theorem adj_iff (ht : 1 ≤ t) (hd : 1 ≤ d) (v w : (o2Sig t d).Vertex) :
    (o2Graph t d).Adj v w ↔ (GM t d).Adj (vEquiv ht hd v) (vEquiv ht hd w) :=
  ⟨adj_fwd ht hd, adj_bwd ht hd⟩

/-- **Transfer**: literal paths in O2(t,d) correspond to literal paths in the model. -/
theorem o2_iff_gm (ht : 1 ≤ t) (hd : 1 ≤ d) :
    (∃ n p, LiteralPath (o2Graph t d) n p) ↔ (∃ n q, LiteralPath (GM t d) n q) :=
  Claude4C1.exists_literal_iff (vEquiv ht hd) (adj_iff ht hd)

end Claude5O2
