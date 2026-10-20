import Formal.GCNegSources

namespace R002.GCNeg
open Icosahedron GCPrimitive GCSector

theorem same_symm (S : Atlas) (p q : Lattice) (h : Same S p q) : Same S q p := by
  intro hq hqn hp hpn; exact (h hp hpn hq hqn).symm

theorem plus_same (P : TailParameters) (hp : Primitive (plusK P) P.l)
    (xi : ℤ) (hx0 : 0≤xi) (hx1 : xi≤1) :
    Same (plusAtlas P hp) (plusJ P-1,xi) (plusG P (plusJ P-1,xi)) := by
  apply same_symm
  rcases plus_source_tile P hp xi hx0 hx1 with ht|ht
  · have hu : Interior (plusK P) P.l
        (tileLocal (plusK P) P.l ⟨2*P.a+3,-P.a-2,false⟩ (plusG P (plusJ P-1,xi))) := by
      rwa [plus_local0]
    apply same_of_charts (plusAtlas P hp) _ _ _ _ hu ht
    · change (plusDart P _).1=(plusDart P _).1
      rw [plus_cap1,plus_source_dart0]; rfl
    · change unframe (plusK P) P.l (plusDart P _).2 _=unframe (plusK P) P.l (plusDart P _).2 _
      rw [plus_cap1,plus_source_dart0]
      exact psi_position _ _ _ 10 0 _ _ (by simpa [unframe] using plus_local0 P (plusJ P-1,xi))
  · have hu : Interior (plusK P) P.l
        (tileLocal (plusK P) P.l ⟨2*P.a+3,-P.a-1,true⟩ (plusG P (plusJ P-1,xi))) := by
      apply (interior_unframe (plusK P) P.l 2 _).mp
      rwa [plus_local1]
    apply same_of_charts (plusAtlas P hp) _ _ _ _ hu ht
    · change (plusDart P _).1=(plusDart P _).1
      rw [plus_cap0,plus_source_dart1]; rfl
    · change unframe (plusK P) P.l (plusDart P _).2 _=unframe (plusK P) P.l (plusDart P _).2 _
      rw [plus_cap0,plus_source_dart1]
      exact psi_position _ _ _ 6 2 _ _ (plus_local1 P (plusJ P-1,xi))

theorem minus_same (P : TailParameters) (ha2 : 2≤P.a) (hp : Primitive (minusK P) P.l)
    (eta : ℤ) (he0 : 0≤eta) (he1 : eta≤1) :
    Same (minusAtlas P ha2 hp) (minusJ P-1+eta,-eta) (minusH P (minusJ P-1+eta,-eta)) := by
  apply same_symm
  have ht := (minus_certificates P ha2 eta he0 he1).2.2
  have hu : Interior (minusK P) P.l
      (tileLocal (minusK P) P.l ⟨2*P.a+1,-P.a-2,false⟩ (minusH P (minusJ P-1+eta,-eta))) := by
    apply (interior_unframe (minusK P) P.l 1 _).mp
    rwa [minus_local]
  apply same_of_charts (minusAtlas P ha2 hp) _ _ _ _ hu ht
  · change (minusDart P _).1=(minusDart P _).1
    rw [minus_cap1 P ha2,minus_source_dart P ha2]; rfl
  · change unframe (minusK P) P.l (minusDart P _).2 _=unframe (minusK P) P.l (minusDart P _).2 _
    rw [minus_cap1 P ha2,minus_source_dart P ha2]
    exact chi_position _ _ _ 11 1 _ _ (minus_local P (minusJ P-1+eta,-eta))

theorem plus_no_challenge_path (P : TailParameters) (hp : Primitive (plusK P) P.l) :
    ¬∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph (plusK P) P.l) n p := by
  apply no_G_path (plusAtlas P hp) (plusJ P) (plusG P)
  · have h := plus_certificates P 0 (by omega) (by omega)
    change 1<plusJ P ∧ plusJ P<plusA P
    constructor <;> linarith [h.1,h.2.1]
  · exact plus_upper_collision P
  · exact plus_lower_collision P
  · exact plus_same P hp

theorem minus_no_challenge_path (P : TailParameters) (ha2 : 2≤P.a) (hp : Primitive (minusK P) P.l) :
    ¬∃ n p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph (minusK P) P.l) n p := by
  apply no_H_path (minusAtlas P ha2 hp) (minusJ P) (minusH P)
  · have h := minus_certificates P ha2 0 (by omega) (by omega)
    change 1<minusJ P ∧ minusJ P<minusA P
    constructor <;> linarith [h.1,h.2.1]
  · exact minus_upper_collision P
  · exact minus_lower_collision P
  · exact minus_same P ha2 hp

end R002.GCNeg
