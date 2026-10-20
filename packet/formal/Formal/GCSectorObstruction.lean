import Formal.GCSectorZigzag

/-! A finite forced prefix need not be injective: a repetition itself obstructs a literal path. -/
namespace R002.GCSector

structure ForcedPrefix {V : Type} (G : SimpleGraph V) (q : ℕ → V) (N : ℕ) : Prop where
  adjacent : ∀ i, i+1≤N → G.Adj (q i) (q (i+1))
  skip : ∀ i, i+2≤N → G.Adj (q i) (q (i+2))
  noBacktrack : ∀ i, i+3≤N → q (i+3)≠q i

theorem literal_eq_prefix {V : Type} (G : SimpleGraph V) (hG : TwoCommonNeighbors G)
    (q : ℕ → V) (N : ℕ) (hq : ForcedPrefix G q N)
    (p : ℕ → V) (n : ℕ) (hp : ClaudeChallenge.LiteralPath G n p)
    (h0 : p 0=q 0) (h1 : p 1=q 1) (h2 : p 2=q 2) :
    ∀ i, i≤N → i<n → p i=q i := by
  obtain ⟨hn,hev,hinj,hadj,hskip,hdeg⟩ := hp
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hiN hin
    by_cases hi0 : i=0
    · subst i; exact h0
    by_cases hi1 : i=1
    · subst i; exact h1
    by_cases hi2 : i=2
    · subst i; exact h2
    obtain ⟨j,rfl⟩ : ∃ j, i=j+3 := ⟨i-3,by omega⟩
    have e0 := ih j (by omega) (by omega) (by omega)
    have e1 := ih (j+1) (by omega) (by omega) (by omega)
    have e2 := ih (j+2) (by omega) (by omega) (by omega)
    let t : OrderedTriangle G := ⟨p j,p (j+1),p (j+2),
      hadj j (by omega),hadj (j+1) (by omega),(hskip j (by omega)).symm⟩
    have hp' : OtherCommon G t.a t.b t.c (p (j+3)) := by
      refine ⟨⟨hskip (j+1) (by omega),hadj (j+2) (by omega)⟩,?_⟩
      intro he
      have := hinj (j+3) j hin (by omega) he
      omega
    have hq' : OtherCommon G t.a t.b t.c (q (j+3)) := by
      change (G.Adj (p (j+1)) (q (j+3)) ∧ G.Adj (p (j+2)) (q (j+3))) ∧ q (j+3)≠p j
      rw [e0,e1,e2]
      exact ⟨⟨hq.skip (j+1) (by omega),hq.adjacent (j+2) (by omega)⟩,hq.noBacktrack j hiN⟩
    obtain ⟨d,_,hd⟩ := unique_other_common G hG t
    exact (hd _ hp').trans (hd _ hq').symm

/-- No endpoint is possible before the displayed repeat, and after it injectivity fails. -/
theorem repetition_obstructs {V : Type} (G : SimpleGraph V) (hG : TwoCommonNeighbors G)
    (q : ℕ → V) (N e : ℕ) (hq : ForcedPrefix G q N)
    (hdeg : ∀ i, 0 < i → i ≤ N → ClaudeChallenge.deg G (q i)=6)
    (he : e<N) (hrep : q e=q N) :
    ¬∃ n p, ClaudeChallenge.LiteralPath G n p ∧ p 0=q 0 ∧ p 1=q 1 ∧ p 2=q 2 := by
  rintro ⟨n,p,hp,h0,h1,h2⟩
  have hmatch := literal_eq_prefix G hG q N hq p n hp h0 h1 h2
  have hn := hp.1
  by_cases hend : n-1≤N
  · have h6 := hdeg (n-1) (by omega) hend
    rw [← hmatch (n-1) hend (by omega)] at h6
    have h5 := hp.2.2.2.2.2.2.1
    omega
  · have hpn : N<n := by omega
    have hpe : e<n := by omega
    have heq : p e=p N := (hmatch e (by omega) hpe).trans (hrep.trans (hmatch N le_rfl hpn).symm)
    have := hp.2.2.1 e N hpe hpn heq
    omega

end R002.GCSector
