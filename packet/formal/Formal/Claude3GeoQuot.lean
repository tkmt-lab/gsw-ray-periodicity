import Formal.Claude3GeoBasic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Card

/-!
# Theorem 1a, geometric foundation (4): exhausting the quotient identifications

Written by a Claude worker (2026-10-20, Theorem 1a geometric session).

The vertex relation of the spec is the equivalence *generated* by the gluing records, so a priori
two sites may be identified through arbitrarily long chains of records. Chart-embeddedness
(part of `Valid`) bounds this:

* `site_eq_of_vtx_eq` : a vertex class contains at most one site of each chart;
* `vtx_eq_iff_stepN`  : two sites are identified iff they are joined by a chain of fewer than
                        `S.C` record steps (each step a record applied forwards or backwards);
* `graph_adj_iff`     : the symmetric normal form of adjacency: `v ≠ w` and some representatives
                        of `v, w` in one common chart differ by a unit vector.

Hence each identification, and each adjacency, is a fixed finite disjunction (over words of
fewer than `C` records with orientations) of conjunctions of the chart inequalities of the
intermediate sites, all of which are images of the first site under fixed rotations plus
integer-affine translations.
-/

namespace ClaudeChallenge2.Geo

open ClaudeChallenge2

variable {S : Sig} {t : ℕ}

/-- Chart-embeddedness, the second conjunct of `Valid`. -/
def Embedded (S : Sig) (t : ℕ) : Prop :=
  ∀ f : Fin S.C, ∀ z z' : ℤ × ℤ, ∀ (h : (S.chart f).Mem t z) (h' : (S.chart f).Mem t z'),
    vtx (S := S) (t := t) ⟨(f, z), h⟩ = vtx ⟨(f, z'), h'⟩ → z = z'

theorem valid_embedded (hV : Valid S t) : Embedded S t := hV.2.1

/-- A vertex class contains at most one site of each chart. -/
theorem site_eq_of_vtx_eq (hE : Embedded S t) {s s' : Site S t} (hf : s.1.1 = s'.1.1)
    (e : vtx s = vtx s') : s = s' := by
  obtain ⟨⟨f, z⟩, h⟩ := s
  obtain ⟨⟨f', z'⟩, h'⟩ := s'
  simp only at hf
  subst hf
  obtain rfl := hE f z z' h h' e
  rfl

/-- One record step, forwards or backwards. -/
def Step (S : Sig) (t : ℕ) (s s' : Site S t) : Prop := SamePoint S t s s' ∨ SamePoint S t s' s

/-- A chain of exactly `n` record steps. -/
def StepN (S : Sig) (t : ℕ) : ℕ → Site S t → Site S t → Prop
  | 0, s, s' => s = s'
  | n + 1, s, s'' => ∃ s', Step S t s s' ∧ StepN S t n s' s''

theorem vtx_eq_of_step {s s' : Site S t} (h : Step S t s s') : vtx s = vtx s' := by
  rcases h with h | h
  · exact Quot.sound (Relation.EqvGen.rel _ _ h)
  · exact (Quot.sound (Relation.EqvGen.rel _ _ h)).symm

theorem vtx_eq_of_stepN : ∀ {n : ℕ} {s s' : Site S t}, StepN S t n s s' → vtx s = vtx s'
  | 0, _, _, h => by rw [show _ = _ from h]
  | _ + 1, _, _, ⟨_, h1, h2⟩ => (vtx_eq_of_step h1).trans (vtx_eq_of_stepN h2)

/-- The graph of record steps on sites. -/
def siteGraph (S : Sig) (t : ℕ) : SimpleGraph (Site S t) := SimpleGraph.fromRel (SamePoint S t)

theorem reachable_of_eqvGen {s s' : Site S t} (h : Relation.EqvGen (SamePoint S t) s s') :
    (siteGraph S t).Reachable s s' := by
  induction h with
  | rel a b h =>
    by_cases hab : a = b
    · subst hab; rfl
    · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hab, Or.inl h⟩)
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

theorem reachable_of_vtx_eq {s s' : Site S t} (e : vtx s = vtx s') :
    (siteGraph S t).Reachable s s' := by
  have h := Quot.eq.1 e
  rw [Equivalence.eqvGen_eq (Relation.EqvGen.is_equivalence _)] at h
  exact reachable_of_eqvGen h

theorem stepN_of_walk : ∀ {s s' : Site S t} (w : (siteGraph S t).Walk s s'),
    StepN S t w.length s s'
  | _, _, .nil => rfl
  | _, _, .cons h w => ⟨_, ((SimpleGraph.fromRel_adj _ _ _).1 h).2, stepN_of_walk w⟩

theorem walk_support_vtx : ∀ {s s' : Site S t} (w : (siteGraph S t).Walk s s'),
    ∀ x ∈ w.support, vtx x = vtx s
  | _, _, .nil, x, hx => by
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
    rw [hx]
  | _, _, .cons h w, x, hx => by
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rfl
    · exact (walk_support_vtx w x hx).trans
        (vtx_eq_of_step ((SimpleGraph.fromRel_adj _ _ _).1 h).2).symm

/-- **Quotient identifications are exhausted by short chains.** Under chart-embeddedness, two
sites have the same vertex iff they are joined by a chain of fewer than `S.C` record steps. -/
theorem vtx_eq_iff_stepN (hE : Embedded S t) (s s' : Site S t) :
    vtx s = vtx s' ↔ ∃ n, n < S.C ∧ StepN S t n s s' := by
  constructor
  · intro e
    classical
    obtain ⟨w⟩ := reachable_of_vtx_eq e
    have hp : w.bypass.IsPath := w.bypass_isPath
    refine ⟨w.bypass.length, ?_, stepN_of_walk _⟩
    have hsup := walk_support_vtx w.bypass
    have hnd : (w.bypass.support.map (fun x : Site S t => x.1.1)).Nodup :=
      hp.support_nodup.map_on (fun x hx y hy hxy =>
        site_eq_of_vtx_eq hE hxy ((hsup x hx).trans (hsup y hy).symm))
    have hle := hnd.length_le_card
    rw [List.length_map, SimpleGraph.Walk.length_support, Fintype.card_fin] at hle
    omega
  · rintro ⟨n, -, h⟩
    exact vtx_eq_of_stepN h

/-! ## Normal form of adjacency -/

/-- Symmetric normal form of adjacency in the surface graph. -/
theorem graph_adj_iff (v w : Vertex S t) :
    (graph S t).Adj v w ↔ v ≠ w ∧ ∃ s s' : Site S t, vtx s = v ∧ vtx s' = w ∧
      s.1.1 = s'.1.1 ∧ s'.1.2 - s.1.2 ∈ unitVec := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    obtain ⟨s, s', hf, hu, (⟨e, e'⟩ | ⟨e, e'⟩)⟩ := exists_unit_of_adj h
    · exact ⟨s, s', e, e', hf, hu⟩
    · exact ⟨s', s, e', e, hf.symm, sub_mem_unitVec_comm hu⟩
  · rintro ⟨hne, s, s', e, e', hf, hu⟩
    exact ⟨hne, Or.inl ⟨s, s', e, e', hf, _, hu, by abel⟩⟩

end ClaudeChallenge2.Geo
