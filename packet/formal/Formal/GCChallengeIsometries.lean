import Formal.GCChallengeQuotient

namespace R002.GCChallengeBridge
open Icosahedron GCPrimitive GCPrimitiveSurface
variable {k l : ℤ}

theorem rotN_reduced (n : ℕ) : ∃ i : Fin 6, ∀ p, ClaudeChallenge.rotN n p=ClaudeChallenge.rotN i.val p := by
  induction n with
  | zero => exact ⟨0,fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨i,hi⟩ := ih
    refine ⟨i+1,?_⟩
    intro p
    rw [ClaudeChallenge.rotN,hi]
    fin_cases i <;> ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot] <;> ring

/-- Two distinct points determine a rotation/translation among the six lattice rotations. -/
theorem affine_unique (j j' : ℕ) (t t' p q : Lattice) (hpq : p≠q)
    (hp : ClaudeChallenge.rotN j p+t=ClaudeChallenge.rotN j' p+t')
    (hq : ClaudeChallenge.rotN j q+t=ClaudeChallenge.rotN j' q+t') :
    ∀ z, ClaudeChallenge.rotN j z+t=ClaudeChallenge.rotN j' z+t' := by
  obtain ⟨i,hi⟩ := rotN_reduced j
  obtain ⟨i',hi'⟩ := rotN_reduced j'
  simp only [hi,hi'] at hp hq ⊢
  have hpx := congrArg Prod.fst hp
  have hpy := congrArg Prod.snd hp
  have hqx := congrArg Prod.fst hq
  have hqy := congrArg Prod.snd hq
  have hn : p.1≠q.1 ∨ p.2≠q.2 := by
    by_cases h : p.1=q.1
    · exact Or.inr (fun h2 => hpq (Prod.ext h h2))
    · exact Or.inl h
  intro z
  fin_cases i <;> fin_cases i' <;>
    ext <;> simp [ClaudeChallenge.rotN,ClaudeChallenge.rot] at hpx hpy hqx hqy ⊢ <;> omega

theorem cornerMap_bijective : ∀ f, Function.Bijective (cornerMap f) := by decide +kernel

theorem pair_oriented : ∀ i j : Corner, i≠j → j=i+1 ∨ i=j+1 := by decide +kernel

theorem two_labels_mate : ∀ (f g : Face) (e a b : Corner), f≠g →
    faceVertex f e=faceVertex g a → faceVertex f (e+1)=faceVertex g b →
    g=(mate (f,e)).1 ∧ a=(mate (f,e)).2+1 ∧ b=(mate (f,e)).2 := by
  decide +kernel

theorem frame_posMap (f : Face) (e : Corner) (p : Lattice) :
    frame k l (cornerMap f e) (posMap k l f p)=frame k l e p := by
  by_cases hf : f=4
  · fin_cases e <;> ext <;> simp [frame,posMap,cornerMap,hf,GCPrimitive.turn] <;> ring
  · simp [posMap,cornerMap,hf]

theorem unfold_posMap (f g : Face) (e m : Corner) (p : Lattice) :
    unframe k l (cornerMap g m) (opposite k l (frame k l (cornerMap f e) (posMap k l f p)))=
      posMap k l g (unframe k l m (opposite k l (frame k l e p))) := by
  apply frame_injective k l (cornerMap g m)
  rw [frame_unframe,frame_posMap,frame_posMap,frame_unframe]

end R002.GCChallengeBridge
