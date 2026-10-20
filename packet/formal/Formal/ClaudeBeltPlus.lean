import Formal.ClaudeBeltPath

/-!
# Belt case of A3, part 5: `k = q l + 1`

Written by a Claude worker (2026-10-19). Mirror image of section 2 of the verifier's
belt proof. With `A=(q+1)k+l`, the zigzag `(0,t),(1,t)`, `0≤t≤A-1`, runs from
`U_0=(0,0)` to `L_q=z+qw=(1,A-1)` strictly inside the band.
-/

namespace ClaudeBelt
open R002 R002.Icosahedron R002.GCPrimitive R002.GCPrimitiveSurface R002.GCChallengeBridge

variable {k l : ℤ}

theorem band_of_alpha (R : Reg) (x : Lattice) (h : InR k l R x) (h0 : 0<a k l x)
    (h1 : a k l x<norm k l) : IsBand R := by
  rcases R with ⟨_|_|_|_,i⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · have := ((in_top i x).mp h).2.2; linarith
  · have := ((in_bot i x).mp h).2.2; linarith

theorem r5_zero : r5 0=0 := by decide
theorem r5_neg_one : r5 (-1)=4 := by decide

theorem start_end_labels : ∀ r : Fin 5,
    ClaudeChallenge.face (kindFace .low 0) 0≠ClaudeChallenge.face (kindFace .up r) 2 := by decide

/-- The zigzag on the lines `x=0` and `x=1`. -/
def zigP (n : ℕ) : Lattice := (((n%2 : ℕ) : ℤ),((n/2 : ℕ) : ℤ))

theorem zigP_even (t : ℕ) : zigP (2*t)=(0,(t:ℤ)) := by
  ext <;> simp [zigP]

theorem zigP_odd (t : ℕ) : zigP (2*t+1)=(1,(t:ℤ)) := by
  ext <;> simp [zigP] <;> omega

theorem zigP_unit (n m : ℕ) (h1 : n<m) (h2 : m≤n+2) : GCPrimitive.Unit (zigP n) (zigP m) := by
  rcases (show m=n+1 ∨ m=n+2 by omega) with rfl | rfl
  · rcases Nat.even_or_odd' n with ⟨t,rfl|rfl⟩
    · refine ⟨0,?_⟩
      rw [zigP_even,zigP_odd]; ext <;> simp [direction]
    · refine ⟨2,?_⟩
      rw [zigP_odd,show 2*t+1+1=2*(t+1) by ring,zigP_even]; ext <;> simp [direction]
  · refine ⟨1,?_⟩
    ext <;> simp [zigP,direction] <;> omega

theorem plus_path (hl : 0<l) (q : ℤ) (hq : 1≤q) (hk : k=q*l+1) (hprim : Primitive k l) :
    ∃ N p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) N p := by
  have hkl : l<k := by nlinarith
  have hk0 : 0<k := by omega
  set A : ℤ := (q+1)*k+l with hA
  have hA2 : 2≤A := by nlinarith
  obtain ⟨M,hM⟩ : ∃ M : ℕ, (M:ℤ)=A := ⟨A.toNat,Int.toNat_of_nonneg (by omega)⟩
  have hTdef : norm k l=k*k+k*l+l*l := rfl
  have I1 : l*(A-1)=norm k l-k-l := by rw [hTdef,hA,hk]; ring
  have I2 : k*(A-1)=q*norm k l+l := by rw [hTdef,hA,hk]; ring
  have hTkl : k+l<norm k l := by rw [hTdef]; nlinarith
  have halpha : ∀ n, 0<n → n<2*M-1 → 0<a k l (zigP n) ∧ a k l (zigP n)<norm k l := by
    intro n h0 h1
    rcases Nat.even_or_odd' n with ⟨t,rfl|rfl⟩
    · rw [zigP_even]; simp only [a]
      have ht1 : (1:ℤ)≤t := by omega
      have ht2 : (t:ℤ)≤A-1 := by omega
      constructor <;> nlinarith
    · rw [zigP_odd]; simp only [a]
      have ht2 : (t:ℤ)≤A-2 := by omega
      have ht0 : (0:ℤ)≤t := by omega
      constructor <;> nlinarith
  refine ⟨2*M,_,literal_of_plane hkl hl hprim (2*M) zigP (Reg.face ⟨.low,0⟩) 0
    (Reg.face ⟨.up,q-1⟩) 2 (by omega) ⟨M,by ring⟩ ?_ ?_ (fun n m h1 h2 _ => zigP_unit n m h1 h2)
    ?_ ?_ ?_ ?_ ?_⟩
  · intro n h0 h1
    obtain ⟨h0',h1'⟩ := halpha n h0 h1
    obtain ⟨R,-,hR⟩ := band_exists hk0 hl hprim _ h0' h1'
    exact ⟨R,hR⟩
  · intro n m R R' h0 hnm _ hmN hR _
    obtain ⟨h0',h1'⟩ := halpha n h0 (by omega)
    exact Or.inl (band_of_alpha R _ hR h0' h1')
  · intro n m _ _
    simp only [zigP]; omega
  · intro n m _ _ h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [zigP] at h1 h2; omega
  · intro n h0 h2
    rcases (show n=1 ∨ n=2 by omega) with rfl | rfl
    · refine ⟨⟨.up,-1⟩,0,?_,?_,?_⟩
      · rw [show (1:ℕ)=2*0+1 by rfl,zigP_odd,in_up]
        simp only [a,b]; push_cast; refine ⟨?_,?_,?_⟩ <;> nlinarith
      · simp [chart,zigP,ClaudeChallenge.rot,ClaudeChallenge.corner]
      · show ClaudeChallenge.face (kindFace .up (r5 (-1))) 0=ClaudeChallenge.face (kindFace .low (r5 0)) 0
        rw [r5_neg_one,r5_zero]; decide
    · refine ⟨⟨.low,0⟩,0,?_,?_,rfl⟩
      · rw [show (2:ℕ)=2*1 by rfl,zigP_even,in_low]
        simp only [a,b]; push_cast; refine ⟨?_,?_,?_⟩ <;> nlinarith
      · simp [chart,zigP,ClaudeChallenge.corner]
  · intro n h1 h2
    have hend : zigP (2*M-1)=(1,A-1) := by
      rw [show 2*M-1=2*(M-1)+1 by omega,zigP_odd]; ext <;> simp <;> omega
    rw [hend]
    rcases (show n=2*(M-2)+1 ∨ n=2*(M-1) by omega) with rfl | rfl
    · refine ⟨⟨.up,q-1⟩,2,?_,?_,rfl⟩
      · rw [zigP_odd,in_up]
        have ht : ((M-2 : ℕ) : ℤ)=A-2 := by omega
        rw [ht]; simp only [a,b]
        refine ⟨?_,?_,?_⟩ <;> nlinarith
      · simp only [chart,ClaudeChallenge.rot,ClaudeChallenge.corner]
        ext <;> simp <;> linarith
    · refine ⟨⟨.low,q⟩,1,?_,?_,?_⟩
      · rw [zigP_even,in_low]
        have ht : ((M-1 : ℕ) : ℤ)=A-1 := by omega
        rw [ht]; simp only [a,b]
        refine ⟨?_,?_,?_⟩ <;> nlinarith
      · simp only [chart,ClaudeChallenge.corner]
        ext <;> simp <;> linarith
      · show ClaudeChallenge.face (kindFace .low (r5 q)) 1=
          ClaudeChallenge.face (kindFace .up (r5 (q-1))) 2
        rw [r5_sub_one q]; exact ((labels_a (r5 (q-1))).2.2.2).symm
  · show ClaudeChallenge.face (kindFace .low (r5 0)) 0≠ClaudeChallenge.face (kindFace .up (r5 (q-1))) 2
    rw [r5_zero]; exact start_end_labels _

end ClaudeBelt
