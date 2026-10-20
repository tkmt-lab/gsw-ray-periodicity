import Formal.GCChallengeGraphIso
import Formal.GCPrimitiveDecision

namespace R002.GCChallengeBridge
open Icosahedron GCPrimitive GCPrimitiveSurface
variable {k l : ℤ}

theorem iso_degree {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (E : G ≃g H) (v : V) : ClaudeChallenge.deg H (E v)=ClaudeChallenge.deg G v := by
  change (H.neighborSet (E v)).ncard=(G.neighborSet v).ncard
  rw [← E.image_neighborSet,Set.ncard_image_of_injective _ E.injective]

theorem iso_literal_path {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (E : G ≃g H) (n : ℕ) (p : ℕ → V) :
    ClaudeChallenge.LiteralPath H n (E ∘ p) ↔ ClaudeChallenge.LiteralPath G n p := by
  simp only [ClaudeChallenge.LiteralPath,Function.comp_apply,E.injective.eq_iff,
    E.map_adj_iff,iso_degree]

theorem challenge_degree (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (v : GCPrimitiveSurface.Vertex k l) :
    ClaudeChallenge.deg (ClaudeChallenge.gcGraph k l) (toChallenge (by omega) hl v)=
      match toCanonical v with | .inl _ => 5 | .inr _ => 6 :=
  (iso_degree (challengeGraphIso hkl hl hprim) v).trans (primitive_challenge_degree hkl hl hprim v)

theorem challenge_degrees_five_six (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (v : ClaudeChallenge.Vertex k l) :
    ClaudeChallenge.deg (ClaudeChallenge.gcGraph k l) v=5 ∨
      ClaudeChallenge.deg (ClaudeChallenge.gcGraph k l) v=6 := by
  obtain ⟨w,rfl⟩ := toChallenge_surjective (by omega) hl hprim v
  rw [challenge_degree hkl hl hprim]
  cases toCanonical w <;> simp

/-- The path's edge count in the research formulation becomes its vertex count minus one. -/
theorem challenge_literal_path_iff (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (p : ℕ → GCPrimitiveSurface.Vertex k l) (n : ℕ) :
    (∃ t : R002.OrderedTriangle (graph k l),
      R002.LiteralPathFrom (graph k l) (fun v => ClaudeChallenge.deg (graph k l) v=5) t p n) ↔
      ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) (n+1)
        (toChallenge (by omega) hl ∘ p) :=
  (primitive_literal_path_iff hkl hl hprim p n).trans
    (iso_literal_path (challengeGraphIso hkl hl hprim) (n+1) p).symm

/-- Exact all-path existence equivalence; neither side has been classified arithmetically. -/
theorem challenge_has_path_iff (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) :
    (∃ n p, ∃ t : R002.OrderedTriangle (graph k l),
      R002.LiteralPathFrom (graph k l) (fun v => ClaudeChallenge.deg (graph k l) v=5) t p n) ↔
    (∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) n p) := by
  constructor
  · rintro ⟨n,p,hp⟩
    exact ⟨n+1,toChallenge (by omega) hl ∘ p,(challenge_literal_path_iff hkl hl hprim p n).mp hp⟩
  · rintro ⟨n,q,hq⟩
    let E := challengeGraphIso hkl hl hprim
    have hp : ClaudeChallenge.LiteralPath (graph k l) n (E.symm ∘ q) :=
      (iso_literal_path E.symm n q).mpr hq
    have hn : n-1+1=n := by have h := hq.1; omega
    refine ⟨n-1,E.symm ∘ q,(primitive_literal_path_iff hkl hl hprim _ _).mpr ?_⟩
    simpa only [hn] using hp

/-- A future classification of the research paths transfers to the independent statement.
This theorem does not supply the classification premise. -/
theorem primitive_comparator (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) (P : Prop)
    (h : (∃ n p, ∃ t : R002.OrderedTriangle (graph k l),
      R002.LiteralPathFrom (graph k l) (fun v => ClaudeChallenge.deg (graph k l) v=5) t p n) ↔ P) :
    (∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) n p) ↔ P :=
  (challenge_has_path_iff hkl hl hprim).symm.trans h

theorem iso_two_common_neighbors {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (E : G ≃g H) (hG : R002.TwoCommonNeighbors G) : R002.TwoCommonNeighbors H := by
  intro b c hbc
  obtain ⟨b,rfl⟩ := E.surjective b
  obtain ⟨c,rfl⟩ := E.surjective c
  obtain ⟨x,y,hxy,h⟩ := hG b c (E.map_adj_iff.mp hbc)
  refine ⟨E x,E y,fun he => hxy (E.injective he),?_⟩
  intro v
  obtain ⟨v,rfl⟩ := E.surjective v
  simpa only [E.map_adj_iff,E.injective.eq_iff] using h v

theorem challenge_two_common_neighbors (hkl : l<k) (hl : 0<l) (hprim : Primitive k l) :
    R002.TwoCommonNeighbors (ClaudeChallenge.gcGraph k l) :=
  iso_two_common_neighbors (challengeGraphIso hkl hl hprim) (two_common_neighbors hkl hl hprim)

noncomputable def challengeFintype (hk : 0<k) (hl : 0<l) (hprim : Primitive k l) :
    Fintype (ClaudeChallenge.Vertex k l) := by
  letI := vertexFintype hk hl
  exact Fintype.ofEquiv (GCPrimitiveSurface.Vertex k l) (challengeVertexEquiv hk hl hprim)

/-- The finite first-repeat decision also applies on the independent quotient itself. -/
theorem challenge_finite_decision (hkl : l<k) (hl : 0<l) (hprim : Primitive k l)
    (t : R002.OrderedTriangle (ClaudeChallenge.gcGraph k l))
    (hc : ClaudeChallenge.deg (ClaudeChallenge.gcGraph k l) t.a=5)
    (hb : ClaudeChallenge.deg (ClaudeChallenge.gcGraph k l) t.b=6) :
    let G := ClaudeChallenge.gcGraph k l
    let hG := challenge_two_common_neighbors hkl hl hprim
    let cone := fun v => ClaudeChallenge.deg G v=5
    ∃ r≤Nat.card (ClaudeChallenge.Vertex k l), R002.FirstRepeat (R002.forcedWalk G hG t) r ∧
      ((∃ n p, R002.LiteralPathFrom G cone t p n) ↔
        ∃ e<r, R002.LegalConeEndpoint cone (R002.forcedWalk G hG t) e) := by
  letI := challengeFintype (show 0<k by omega) hl hprim
  have hb' : ¬ClaudeChallenge.deg (ClaudeChallenge.gcGraph k l) t.b=5 := by omega
  simpa only [Nat.card_eq_fintype_card] using
    R002.finite_literal_path_decision (ClaudeChallenge.gcGraph k l)
      (challenge_two_common_neighbors hkl hl hprim)
      (fun v => ClaudeChallenge.deg (ClaudeChallenge.gcGraph k l) v=5) t hc hb'

end R002.GCChallengeBridge
