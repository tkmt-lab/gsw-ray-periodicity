import Formal.Claude7D12Eqv

/-!
# D12: `d12Graph r s` is isomorphic to the model `GM r s`

Written by a Claude worker (2026-10-22, D12 bridge session), adapting `Claude5D12Iso.lean`.

* `vphi`           : the vertex map (well defined by `samePoint_phi`);
* `vphi_bijective` : injective by `eqv_of_phi`, surjective (a seam point at arclength `l` is the
                     point `P0 l` of cell 0);
* `adj_iff`        : adjacency corresponds (the charts are the cells);
* `d12_iff_gm`     : literal paths correspond.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Claude7D12

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

theorem phi_of_eqvGen (hr : 1 ≤ r) (hs : 1 ≤ s) {a b : (d12Sig r s).Site}
    (h : Relation.EqvGen (d12Sig r s).SamePoint a b) :
    Phi r s a.1.1 a.1.2 = Phi r s b.1.1 b.1.2 := by
  induction h with
  | rel x y hxy => exact samePoint_phi hr hs x y hxy
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem phi_valid (hr : 1 ≤ r) (hs : 1 ≤ s) (a : (d12Sig r s).Site) :
    Valid r s (Phi r s a.1.1 a.1.2) :=
  ch_valid hr hs (Fin.isLt (n := 2) a.1.1) ((inCell_iff (by omega) (by omega) _ _).1 a.2)

/-- The model vertex of a site. -/
def siteM (hr : 1 ≤ r) (hs : 1 ≤ s) (a : (d12Sig r s).Site) : MS r s :=
  ⟨Phi r s a.1.1 a.1.2, phi_valid hr hs a⟩

/-- The model vertex of a vertex. -/
def vphi (hr : 1 ≤ r) (hs : 1 ≤ s) : (d12Sig r s).Vertex → MS r s :=
  Quot.lift (siteM hr hs) (fun _ _ h => Subtype.ext (phi_of_eqvGen hr hs h))

theorem vphi_vtx (hr : 1 ≤ r) (hs : 1 ≤ s) (a : (d12Sig r s).Site) :
    (vphi hr hs ((d12Sig r s).vtx a)).1 = Phi r s a.1.1 a.1.2 := rfl

theorem vphi_injective (hr : 1 ≤ r) (hs : 1 ≤ s) : Function.Injective (vphi hr hs) := by
  intro v w h
  induction v using Quot.ind
  induction w using Quot.ind
  exact Quot.sound (eqv_of_phi hr hs _ _ (congrArg Subtype.val h))

/-- Every model vertex is a chart point. -/
theorem valid_rep (hr : 1 ≤ r) (hs : 1 ≤ s) {v : MV} (hv : Valid r s v) :
    ∃ c, c < 2 ∧ ∃ ρ, Dom r s c ρ ∧ ch r s c ρ = v := by
  obtain ⟨k, z⟩ := v
  rcases hv with ⟨hk, hz⟩ | ⟨hk, hz⟩ | ⟨hk, h2, h0, h1⟩ <;> simp only at hk
  · subst hk
    refine ⟨0, by norm_num, z, ?_, ch0_I hz⟩
    simp only [Dom, H0]; simp only [I0] at hz; omega
  · subst hk
    refine ⟨1, by norm_num, z, ?_, ch1_I hz⟩
    simp only [Dom, H1]; simp only [I1] at hz; omega
  · subst hk
    obtain ⟨l, z2⟩ := z
    simp only at h2 h0 h1
    subst h2
    obtain ⟨a, b, c⟩ := P0_spec hr hs h0 h1
    exact ⟨0, by norm_num, P0 r s l, a, by rw [ch0_B b, c]⟩

theorem vphi_surjective (hr : 1 ≤ r) (hs : 1 ≤ s) : Function.Surjective (vphi hr hs) := by
  rintro ⟨v, hv⟩
  obtain ⟨c, hc, ρ, hρ, rfl⟩ := valid_rep hr hs hv
  refine ⟨(d12Sig r s).vtx ⟨((⟨c, hc⟩ : Fin 2), ρ),
    (inCell_iff (by omega) (by omega) _ _).2 hρ⟩, ?_⟩
  apply Subtype.ext
  rw [vphi_vtx]
  rfl

/-! ## Adjacency -/

theorem adj_fwd (hr : 1 ≤ r) (hs : 1 ≤ s) {v w : (d12Sig r s).Vertex}
    (h : (d12Graph r s).Adj v w) : (GM r s).Adj (vphi hr hs v) (vphi hr hs w) := by
  obtain ⟨hne, a, b, rfl, rfl, hab⟩ := h
  have key : ∀ a b : (d12Sig r s).Site, b.1.1 = a.1.1 → b.1.2 - a.1.2 ∈ unitVec →
      (vphi hr hs ((d12Sig r s).vtx a)).1 ≠ (vphi hr hs ((d12Sig r s).vtx b)).1 →
      AdjM r s (vphi hr hs ((d12Sig r s).vtx a)).1 (vphi hr hs ((d12Sig r s).vtx b)).1 := by
    rintro ⟨⟨g, z⟩, hz⟩ ⟨⟨g', z'⟩, hz'⟩ h1 h2 hne
    simp only at h1 h2
    subst g'
    have hz1 := (inCell_iff (by omega) (by omega) _ _).1 hz
    have hz2 := (inCell_iff (by omega) (by omega) _ _).1 hz'
    refine ⟨hne, g.val, Fin.isLt (n := 2) g, z, z' - z, hz1, by simpa using hz2, h2, rfl, ?_⟩
    rw [vphi_vtx]
    simp [Phi]
  have hne' : (vphi hr hs ((d12Sig r s).vtx a)).1 ≠ (vphi hr hs ((d12Sig r s).vtx b)).1 :=
    fun e => hne (vphi_injective hr hs (Subtype.ext e))
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key a b h1 h2 hne'
  · exact adjM_symm (key b a h1 h2 (fun e => hne' e.symm))

theorem adj_bwd (hr : 1 ≤ r) (hs : 1 ≤ s) {v w : (d12Sig r s).Vertex}
    (h : (GM r s).Adj (vphi hr hs v) (vphi hr hs w)) : (d12Graph r s).Adj v w := by
  obtain ⟨hne, c, hc, ρ, u, h1, h2, hu, e1, e2⟩ := h
  refine ⟨fun e => hne (by rw [e]), ?_⟩
  let a : (d12Sig r s).Site := ⟨((⟨c, hc⟩ : Fin 2), ρ), (inCell_iff (by omega) (by omega) _ _).2 h1⟩
  let b : (d12Sig r s).Site :=
    ⟨((⟨c, hc⟩ : Fin 2), ρ + u), (inCell_iff (by omega) (by omega) _ _).2 h2⟩
  refine ⟨a, b, vphi_injective hr hs (Subtype.ext ?_), vphi_injective hr hs (Subtype.ext ?_),
    Or.inl ⟨rfl, by simpa [a, b] using hu⟩⟩
  · rw [vphi_vtx, ← e1]; rfl
  · rw [vphi_vtx, ← e2]; rfl

/-- The vertex bijection. -/
noncomputable def vEquiv (hr : 1 ≤ r) (hs : 1 ≤ s) : (d12Sig r s).Vertex ≃ MS r s :=
  Equiv.ofBijective (vphi hr hs) ⟨vphi_injective hr hs, vphi_surjective hr hs⟩

theorem adj_iff (hr : 1 ≤ r) (hs : 1 ≤ s) (v w : (d12Sig r s).Vertex) :
    (d12Graph r s).Adj v w ↔ (GM r s).Adj (vEquiv hr hs v) (vEquiv hr hs w) :=
  ⟨adj_fwd hr hs, adj_bwd hr hs⟩

/-- **Transfer**: literal paths in D12(r,s) correspond to literal paths in the model. -/
theorem d12_iff_gm (hr : 1 ≤ r) (hs : 1 ≤ s) :
    (∃ n p, LiteralPath (d12Graph r s) n p) ↔ (∃ n q, LiteralPath (GM r s) n q) :=
  Claude4C1.exists_literal_iff (vEquiv hr hs) (adj_iff hr hs)

end Claude7D12
