import Formal.ClaudeChallengeSpec
import Formal.GCPrimitiveDegree
import Formal.FiniteLiteralPath
import Mathlib.Algebra.Group.Nat.Even

namespace R002.GCChallengeBridge

/-- The edge-count indexing and cone predicate agree exactly with the challenge's
vertex-count indexing on graphs whose actual neighbor cardinalities are five or six. -/
theorem literal_path_iff {V : Type} (G : SimpleGraph V)
    (hdeg : ∀ v, ClaudeChallenge.deg G v=5 ∨ ClaudeChallenge.deg G v=6)
    (p : ℕ → V) (n : ℕ) :
    (∃ t : R002.OrderedTriangle G,
      R002.LiteralPathFrom G (fun v => ClaudeChallenge.deg G v=5) t p n) ↔
      ClaudeChallenge.LiteralPath G (n+1) p := by
  constructor
  · rintro ⟨t,hp⟩
    obtain ⟨hmin,hodd,hend,hprev⟩ := hp.endpoint
    have hsecond : ClaudeChallenge.deg G (p 1)=6 := (hdeg _).resolve_left hp.secondNotCone
    have hpenult : ClaudeChallenge.deg G (p (n-1))=6 := (hdeg _).resolve_left hprev
    have hidx : n+1-2=n-1 := by omega
    refine ⟨by omega,Nat.even_iff.mpr (by omega),?_,?_,?_,hp.startCone,?_,hsecond,?_⟩
    · intro i j hi hj he
      exact hp.finitePath.injective i (by omega) j (by omega) he
    · intro i hi
      exact hp.finitePath.adjacent i (by omega)
    · intro i hi
      exact hp.finitePath.skipAdjacent i (by omega)
    · simpa using hend
    · simpa only [hidx] using hpenult
  · rintro ⟨hmin,heven,hinj,hadj,hskip,hstart,hend,hsecond,hpenult⟩
    have hodd : n%2=1 := by have he := Nat.even_iff.mp heven; omega
    have hn : 3≤n := by omega
    have hidx : n+1-2=n-1 := by omega
    rw [hidx] at hpenult
    have hend' : ClaudeChallenge.deg G (p n)=5 := by simpa using hend
    let t : R002.OrderedTriangle G := ⟨p 0,p 1,p 2,
      hadj 0 (by omega),hadj 1 (by omega),(hskip 0 (by omega)).symm⟩
    refine ⟨t,{
      finitePath := ⟨?_,?_,?_⟩
      initial0 := rfl
      initial1 := rfl
      initial2 := rfl
      startCone := hstart
      secondNotCone := ?_
      endpoint := ⟨hn,hodd,hend',?_⟩ }⟩
    · intro i hi j hj he
      exact hinj i j (by omega) (by omega) he
    · intro i hi
      exact hadj i (by omega)
    · intro i hi
      exact hskip i (by omega)
    · omega
    · omega

theorem primitive_challenge_degree {k l : ℤ} (hkl : l<k) (hl : 0<l)
    (hprim : GCPrimitive.Primitive k l) (v : GCPrimitiveSurface.Vertex k l) :
    ClaudeChallenge.deg (GCPrimitiveSurface.graph k l) v=
      match GCPrimitiveSurface.toCanonical v with | .inl _ => 5 | .inr _ => 6 :=
  GCPrimitiveSurface.all_neighbor_card hkl hl hprim v

theorem primitive_literal_path_iff {k l : ℤ} (hkl : l<k) (hl : 0<l)
    (hprim : GCPrimitive.Primitive k l) (p : ℕ → GCPrimitiveSurface.Vertex k l) (n : ℕ) :
    (∃ t : R002.OrderedTriangle (GCPrimitiveSurface.graph k l),
      R002.LiteralPathFrom (GCPrimitiveSurface.graph k l)
        (fun v => ClaudeChallenge.deg (GCPrimitiveSurface.graph k l) v=5) t p n) ↔
      ClaudeChallenge.LiteralPath (GCPrimitiveSurface.graph k l) (n+1) p := by
  apply literal_path_iff
  intro v
  rw [primitive_challenge_degree hkl hl hprim]
  cases GCPrimitiveSurface.toCanonical v <;> simp

end R002.GCChallengeBridge
