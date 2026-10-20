import Formal.GCPrimitiveBoundary

/-! Coordinate recovery and finite search bounds for the local parent triangle. -/
namespace R002.GCPrimitive

theorem recover_coordinates (k l : ℤ) (p : Lattice) :
    norm k l*p.1=k*a k l p-l*b k l p ∧
    norm k l*p.2=l*a k l p+(k+l)*b k l p := by
  dsimp [norm,a,b]
  constructor <;> ring

theorem slices_injective (k l : ℤ) (hk : 0<k) (hl : 0≤l) :
    Function.Injective (fun p : Lattice => (a k l p,b k l p)) := by
  intro p q h
  have ha := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  change a k l p=a k l q at ha
  change b k l p=b k l q at hb
  have hn := ne_of_gt (norm_pos k l hk hl)
  apply Prod.ext
  · apply mul_left_cancel₀ hn
    rw [(recover_coordinates k l p).1,(recover_coordinates k l q).1,ha,hb]
  · apply mul_left_cancel₀ hn
    rw [(recover_coordinates k l p).2,(recover_coordinates k l q).2,ha,hb]

theorem closed_bounds (k l : ℤ) (hk : 0<k) (hl : 0≤l) (p : Lattice)
    (hp : Closed k l p) : -l≤p.1 ∧ p.1≤k ∧ 0≤p.2 ∧ p.2≤k+l := by
  have hT := norm_pos k l hk hl
  have hkl : 0≤k+l := by omega
  have hx0 : norm k l*(p.1+l)=(k+l)*a k l p+l*c k l p := by
    dsimp [a,b,c,norm]; ring
  have hx1 : norm k l*(k-p.1)=k*c k l p+(k+l)*b k l p := by
    dsimp [a,b,c,norm]; ring
  have hy0 := (recover_coordinates k l p).2
  have hy1 : norm k l*(k+l-p.2)=(k+l)*c k l p+k*a k l p := by
    dsimp [a,b,c,norm]; ring
  have h0 := add_nonneg (mul_nonneg hkl hp.1) (mul_nonneg hl hp.2.2)
  have h1 := add_nonneg (mul_nonneg hk.le hp.2.2) (mul_nonneg hkl hp.2.1)
  have h2 := add_nonneg (mul_nonneg hl hp.1) (mul_nonneg hkl hp.2.1)
  have h3 := add_nonneg (mul_nonneg hkl hp.2.2) (mul_nonneg hk.le hp.1)
  rw [← hx0] at h0
  rw [← hx1] at h1
  rw [← hy0] at h2
  rw [← hy1] at h3
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

theorem interior_closed (k l : ℤ) (p : Lattice) (hp : Interior k l p) :
    Closed k l p := ⟨hp.1.le,hp.2.1.le,hp.2.2.le⟩

theorem interior_bounds (k l : ℤ) (hk : 0<k) (hl : 0≤l) (p : Lattice)
    (hp : Interior k l p) : -l≤p.1 ∧ p.1≤k ∧ 0≤p.2 ∧ p.2≤k+l :=
  closed_bounds k l hk hl p (interior_closed k l p hp)

end R002.GCPrimitive
