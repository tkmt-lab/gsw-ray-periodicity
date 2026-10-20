import Formal.ClaudeBeltPlus

/-!
# Belt case of A3, part 6: `k = q l - 1`, `l ≥ 2`

Written by a Claude worker (2026-10-19). Mirror image of section 3 of the verifier's
belt proof. With `A=(q+1)k+l`, the zigzag `(0,t),(-1,t+1)`, `0≤t≤A`, runs from
`U_0=(0,0)` to `L_q=z+qw=(-1,A+1)`. Its first odd points lie in the top cap face
attached to `low 0`, its last even points in the bottom cap face attached to `up (q-1)`,
all other interior points strictly inside the band.
-/

namespace ClaudeBelt
open R002 R002.Icosahedron R002.GCPrimitive R002.GCPrimitiveSurface R002.GCChallengeBridge

variable {k l : ℤ}

/-- The zigzag on the lines `x=0` and `x=-1`. -/
def zigM (n : ℕ) : Lattice := (-((n%2 : ℕ) : ℤ),((n/2+n%2 : ℕ) : ℤ))

theorem zigM_even (t : ℕ) : zigM (2*t)=(0,(t:ℤ)) := by
  ext <;> simp [zigM]

theorem zigM_odd (t : ℕ) : zigM (2*t+1)=(-1,(t:ℤ)+1) := by
  ext <;> simp [zigM] <;> omega

theorem zigM_unit (n m : ℕ) (h1 : n<m) (h2 : m≤n+2) : GCPrimitive.Unit (zigM n) (zigM m) := by
  rcases (show m=n+1 ∨ m=n+2 by omega) with rfl | rfl
  · rcases Nat.even_or_odd' n with ⟨t,rfl|rfl⟩
    · refine ⟨2,?_⟩
      rw [zigM_even,zigM_odd]; ext <;> simp [direction]
    · refine ⟨0,?_⟩
      rw [zigM_odd,show 2*t+1+1=2*(t+1) by ring,zigM_even]; ext <;> simp [direction]
  · refine ⟨1,?_⟩
    ext <;> simp [zigM,direction] <;> omega

set_option maxHeartbeats 1000000 in
theorem minus_path (hl : 2≤l) (q : ℤ) (hk : k=q*l-1) (hkl : l<k) (hprim : Primitive k l) :
    ∃ N p, ClaudeChallenge.LiteralPath (ClaudeChallenge.gcGraph k l) N p := by
  have hl0 : 0<l := by omega
  have hk0 : 0<k := by omega
  have hq : 2≤q := by
    by_contra h; push Not at h
    have : q*l≤1*l := mul_le_mul_of_nonneg_right (by omega) (by omega)
    omega
  set A : ℤ := (q+1)*k+l with hA
  have hA2 : 2≤A := by nlinarith
  obtain ⟨M,hM⟩ : ∃ M : ℕ, (M:ℤ)=A := ⟨A.toNat,Int.toNat_of_nonneg (by omega)⟩
  have hTdef : norm k l=k*k+k*l+l*l := rfl
  have J1 : l*A=norm k l+k := by rw [hTdef,hA,hk]; ring
  have J2 : k*A=q*norm k l-k-l := by rw [hTdef,hA,hk]; ring
  have J3 : norm k l=l*((k-1)*q+k+l)+1 := by rw [hTdef,hk]; ring
  have J5 : q*l=k+1 := by omega
  have hTkl : k+l+1<norm k l := by rw [hTdef]; nlinarith
  have hTlq : l+k*q<norm k l := by
    have h1 : l*(l+k*q)=l*l+k*(k+1) := by rw [← J5]; ring
    have h2 : l*l+k*(k+1)<l*norm k l := by rw [hTdef]; nlinarith
    exact lt_of_mul_lt_mul_left (h1 ▸ h2) hl0.le
  have hTne : ∀ t : ℤ, l*t≠norm k l := by
    intro t ht
    rw [J3] at ht
    have : l*(t-((k-1)*q+k+l))=1 := by linarith
    rcases lt_trichotomy (t-((k-1)*q+k+l)) 0 with h | h | h
    · nlinarith
    · rw [h] at this; omega
    · nlinarith
  -- classification of the interior points
  have hclass : ∀ n, 0<n → n<2*M+1 →
      (0<a k l (zigM n) ∧ a k l (zigM n)<norm k l) ∨
      (InR k l ⟨.top,0⟩ (zigM n) ∧ (n:ℤ)≤2*q-1) ∨
      (InR k l ⟨.bot,q-1⟩ (zigM n) ∧ 2*q+2≤(n:ℤ)) := by
    intro n h0 h1
    rcases Nat.even_or_odd' n with ⟨t,rfl|rfl⟩
    · rw [zigM_even]
      have ht1 : (1:ℤ)≤t := by omega
      have ht2 : (t:ℤ)≤A := by omega
      by_cases hlt : l*t<norm k l
      · left; simp only [a]; constructor <;> nlinarith
      · have hgt : norm k l<l*t := lt_of_le_of_ne (not_lt.mp hlt) (fun h => hTne t h.symm)
        right; right
        constructor
        · rw [in_bot]; simp only [a,b]
          refine ⟨?_,?_,?_⟩
          · have h1 : l*((q-1)*norm k l)<l*(k*t) := by
              have e1 : l*((q-1)*norm k l)=(k+1-l)*norm k l := by rw [← J5]; ring
              rw [e1]; nlinarith
            have := lt_of_mul_lt_mul_left h1 hl0.le
            linarith
          · have : (k+l)*t≤(k+l)*A := mul_le_mul_of_nonneg_left ht2 (by omega)
            nlinarith
          · linarith
        · have : l*(q+1)<l*t := by nlinarith
          have := lt_of_mul_lt_mul_left this hl0.le
          push_cast; omega
    · rw [zigM_odd]
      have ht2 : (t:ℤ)≤A-1 := by omega
      have ht0 : (0:ℤ)≤t := by omega
      by_cases htq : (t:ℤ)≤q-1
      · right; left
        constructor
        · rw [in_top]; simp only [a,b]
          refine ⟨?_,?_,?_⟩
          · have : k*(t+1)≤k*q := mul_le_mul_of_nonneg_left (by omega) hk0.le
            nlinarith
          · nlinarith
          · have : l*t≤l*(q-1) := mul_le_mul_of_nonneg_left htq hl0.le
            nlinarith
        · push_cast; omega
      · left; simp only [a]
        have : l*q≤l*t := mul_le_mul_of_nonneg_left (by omega) hl0.le
        have : l*t≤l*(A-1) := mul_le_mul_of_nonneg_left ht2 hl0.le
        constructor <;> nlinarith
  have hregion : ∀ n, 0<n → n<2*M+1 → ∃ R, InR k l R (zigM n) := by
    intro n h0 h1
    rcases hclass n h0 h1 with ⟨h0',h1'⟩ | ⟨h,_⟩ | ⟨h,_⟩
    · obtain ⟨R,-,hR⟩ := band_exists hk0 hl0 hprim _ h0' h1'
      exact ⟨R,hR⟩
    · exact ⟨_,h⟩
    · exact ⟨_,h⟩
  refine ⟨2*M+2,_,literal_of_plane hkl hl0 hprim (2*M+2) zigM (Reg.face ⟨.low,0⟩) 0
    (Reg.face ⟨.up,q-1⟩) 2 (by omega) ⟨M+1,by ring⟩ ?_ ?_ (fun n m h1 h2 _ => zigM_unit n m h1 h2)
    ?_ ?_ ?_ ?_ ?_⟩
  · intro n h0 h1
    exact hregion n h0 (by omega)
  · intro n m R R' h0 hnm hmn hmN hR hR'
    rcases hclass n h0 (by omega) with ⟨a0,a1⟩ | ⟨tn,hn⟩ | ⟨bn,hn⟩
    · exact Or.inl (band_of_alpha R _ hR a0 a1)
    all_goals rcases hclass m (by omega) (by omega) with ⟨a0,a1⟩ | ⟨tm,hm⟩ | ⟨bm,hm⟩
    · exact Or.inr (Or.inl (band_of_alpha R' _ hR' a0 a1))
    · right; right
      rw [region_unique hk0 hl0 R _ _ hR tn,region_unique hk0 hl0 R' _ _ hR' tm]
    · exfalso; omega
    · exact Or.inr (Or.inl (band_of_alpha R' _ hR' a0 a1))
    · exfalso; omega
    · right; right
      rw [region_unique hk0 hl0 R _ _ hR bn,region_unique hk0 hl0 R' _ _ hR' bm]
  · intro n m _ _
    simp only [zigM]; omega
  · intro n m _ _ h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [zigM] at h1 h2; omega
  · intro n h0 h2
    rcases (show n=1 ∨ n=2 by omega) with rfl | rfl
    · refine ⟨⟨.top,0⟩,1,?_,?_,?_⟩
      · rw [show (1:ℕ)=2*0+1 by rfl,zigM_odd,in_top]
        simp only [a,b]; push_cast; refine ⟨?_,?_,?_⟩ <;> nlinarith
      · simp [chart,zigM,ClaudeChallenge.rot,ClaudeChallenge.corner]
      · show ClaudeChallenge.face (kindFace .top (r5 0)) 1=ClaudeChallenge.face (kindFace .low (r5 0)) 0
        exact (labels_c (r5 0)).2.2.1
    · refine ⟨⟨.low,0⟩,0,?_,?_,rfl⟩
      · rw [show (2:ℕ)=2*1 by rfl,zigM_even,in_low]
        simp only [a,b]; push_cast; refine ⟨?_,?_,?_⟩ <;> nlinarith
      · simp [chart,zigM,ClaudeChallenge.corner]
  · intro n h1 h2
    have hend : zigM (2*M+2-1)=(-1,A+1) := by
      rw [show 2*M+2-1=2*M+1 by omega,zigM_odd]; ext <;> simp <;> omega
    rw [hend]
    rcases (show n=2*(M-1)+1 ∨ n=2*M by omega) with rfl | rfl
    · refine ⟨⟨.up,q-1⟩,2,?_,?_,rfl⟩
      · rw [zigM_odd,in_up]
        have ht : ((M-1 : ℕ) : ℤ)+1=A := by omega
        rw [ht]; simp only [a,b]
        refine ⟨?_,?_,?_⟩ <;> nlinarith
      · simp only [chart,ClaudeChallenge.rot,ClaudeChallenge.corner]
        ext <;> simp <;> linarith
    · refine ⟨⟨.bot,q-1⟩,1,?_,?_,?_⟩
      · rw [zigM_even,in_bot,hM]; simp only [a,b]
        refine ⟨?_,?_,?_⟩ <;> nlinarith
      · simp only [chart,ClaudeChallenge.rot,ClaudeChallenge.corner]
        ext <;> simp <;> linarith
      · exact (labels_e (r5 (q-1))).2.2.1
  · show ClaudeChallenge.face (kindFace .low (r5 0)) 0≠ClaudeChallenge.face (kindFace .up (r5 (q-1))) 2
    rw [r5_zero]; exact start_end_labels _

end ClaudeBelt
