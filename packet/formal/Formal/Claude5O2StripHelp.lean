import Formal.Claude5O2Kill

/-!
# O2 model: helper lemmas for the generated strip files

Written by a Claude worker (2026-10-20, O2 bridge session).
-/

set_option linter.unusedVariables false

/-- Equality of explicit lattice points (linear arithmetic). -/
macro "peq" : tactic => `(tactic| (first | rfl | (simp only [Claude5O2.sp, Prod.mk.injEq, Prod.ext_iff, true_and, and_true] <;> omega)))

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

variable {t d : ℤ}

theorem pt_0 (b : Blk) : b.pt t d 0 = ch t d b.c (b.A.1, b.A.2) := by simp [Blk.pt, Blk.pos]

theorem pt_1 (b : Blk) : b.pt t d 1 = ch t d b.c (b.A.1 + b.E.1, b.A.2 + b.E.2) := by
  simp [Blk.pt, Blk.pos]

theorem pt_2 (b : Blk) : b.pt t d 2 = ch t d b.c (b.A.1 + b.D.1, b.A.2 + b.D.2) := by
  simp [Blk.pt, Blk.pos]

theorem pt_e (b : Blk) :
    b.pt t d (2 * b.L) = ch t d b.c (b.A.1 + (b.L : ℤ) * b.D.1, b.A.2 + (b.L : ℤ) * b.D.2) := by
  simp only [Blk.pt]; rw [pos_even]

theorem pt_e1 (b : Blk) (h : 1 ≤ b.L) : b.pt t d (2 * b.L - 1) =
    ch t d b.c (b.A.1 + ((b.L : ℤ) - 1) * b.D.1 + b.E.1, b.A.2 + ((b.L : ℤ) - 1) * b.D.2 + b.E.2) := by
  simp only [Blk.pt]
  rw [show 2 * b.L - 1 = 2 * (b.L - 1) + 1 by omega, pos_odd]
  push_cast [h]; rfl

theorem pt_e2 (b : Blk) (h : 1 ≤ b.L) : b.pt t d (2 * b.L - 2) =
    ch t d b.c (b.A.1 + ((b.L : ℤ) - 1) * b.D.1, b.A.2 + ((b.L : ℤ) - 1) * b.D.2) := by
  simp only [Blk.pt]
  rw [show 2 * b.L - 2 = 2 * (b.L - 1) by omega, pos_even]
  push_cast [h]; rfl

theorem pt_odd' (b : Blk) (i : ℕ) : b.pt t d (2 * i + 1) =
    ch t d b.c (b.A.1 + (i : ℤ) * b.D.1 + b.E.1, b.A.2 + (i : ℤ) * b.D.2 + b.E.2) := by
  simp only [Blk.pt]; rw [pos_odd]

theorem adj_ch (ht : 1 ≤ t) {c : ℕ} (hc : c < 5) {P Q : ℤ × ℤ} (hP : Dom t d c P)
    (hQ : Dom t d c Q) (hu : Q - P ∈ unitVec) : AdjM t d (ch t d c P) (ch t d c Q) := by
  have := adj_of_unit ht hc hP (by simpa using hQ) hu (v := ch t d c P) rfl
  simpa using this

theorem tr_ch (ht : 1 ≤ t) (hd : 1 ≤ d) {c c' : ℕ} (hc' : c' < 5) {p p' : ℤ × ℤ}
    (h : Tr t d c c' p p') : ch t d c p = ch t d c' p' := by
  rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩ <;>
    rcases c_cases (c := c') with rfl | rfl | ⟨j, rfl⟩ <;> simp only [Tr] at h
  · obtain ⟨rfl, hD⟩ := h; rw [ch1_onD hD]; rfl
  · obtain ⟨l, h0, h1, rfl, rfl⟩ := h
    have hj : j < 3 := by omega
    by_cases hl : l ≤ t
    · rw [show ((max (l - t) 0, min l t) : ℤ × ℤ) = (0, l) by ext <;> simp <;> omega,
        chR_AB ht j rfl]
    · rw [show ((max (l - t) 0, min l t) : ℤ × ℤ) = (l - t, t) by ext <;> simp <;> omega,
        chR_BC ht j rfl (by simp; omega)]
      simp
  · obtain ⟨l, h0, h1, rfl, rfl⟩ := h
    have hj : j < 3 := by omega
    by_cases hl : l ≤ t
    · rw [show ((min l t, max (l - t) 0) : ℤ × ℤ) = (l, 0) by ext <;> simp <;> omega,
        chR_AD ht hd hj rfl (by simp; omega) (by simp; omega)]
    · rw [show ((min l t, max (l - t) 0) : ℤ × ℤ) = (t, l - t) by ext <;> simp <;> omega,
        chR_DC ht hd hj rfl (by simp; omega) (by simp; omega)]
      simp

theorem ne_RR (ht : 1 ≤ t) (hd : 1 ≤ d) {i j : ℕ} (hi : i < 3) (hj : j < 3) (hij : i ≠ j)
    {ρ ρ' : ℤ × ℤ} (h1 : Dom t d (i + 2) ρ) (h2 : Dom t d (j + 2) ρ') :
    ch t d (i + 2) ρ ≠ ch t d (j + 2) ρ' := by
  intro e
  rcases ch_eq ht hd (by omega) (by omega) h1 h2 e with ⟨hc, -⟩ | h' | h'
  · omega
  · simp [Tr] at h'
  · simp [Tr] at h'

theorem adj_via (ht : 1 ≤ t) {c : ℕ} (hc : c < 5) {P Q : ℤ × ℤ} {v w : MV} (hP : Dom t d c P)
    (hQ : Dom t d c Q) (hu : Q - P ∈ unitVec) (e1 : v = ch t d c P) (e2 : w = ch t d c Q) :
    AdjM t d v w := by
  rw [e1, e2]; exact adj_ch ht hc hP hQ hu

theorem tr01 {z z' : ℤ × ℤ} (h1 : z' = z) (h2 : OnD t d z) : Tr t d 0 1 z z' := by
  simp only [Tr]; exact ⟨h1, h2⟩

theorem tr0R {j : ℕ} {z z' : ℤ × ℤ} (l : ℤ) (h0 : 0 ≤ l) (h1 : l ≤ 2 * t) (h2 : z = sp t d j l)
    (h3 : z' = (max (l - t) 0, min l t)) : Tr t d 0 (j + 2) z z' := by
  simp only [Tr]; exact ⟨l, h0, h1, h2, h3⟩

theorem tr1R {j : ℕ} {z z' : ℤ × ℤ} (l : ℤ) (h0 : 0 ≤ l) (h1 : l ≤ 2 * t) (h2 : z = sp t d j l)
    (h3 : z' = (min l t, max (l - t) 0)) : Tr t d 1 (j + 2) z z' := by
  simp only [Tr]; exact ⟨l, h0, h1, h2, h3⟩

end Claude5O2

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

variable {t d : ℤ}

theorem one_le_of_two {t : ℕ} (h : 2 ≤ t) : (1 : ℤ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)

theorem two_le_of_two {t : ℕ} (h : 2 ≤ t) : (2 : ℤ) ≤ t := by exact_mod_cast h

theorem kill_at_fwd (ht : 2 ≤ t) (hd : 2 ≤ d) {ls : List Blk} {N : ℕ} (hch : Chain t d ls)
    (hW : IsCStrip t d (fun k => wk t d ls (k % N)) N) (j : ℕ) (hj : j < ls.length)
    (hL : 1 ≤ (ls.get ⟨j, hj⟩).L) (hlt : tot (ls.take j) + 2 < N) {n : ℕ} {p : ℕ → MS t d}
    (hp : LiteralPath (GM t d) n p) (h0 : (p 0).1 = (ls.get ⟨j, hj⟩).pt t d 0)
    (h1 : (p 1).1 = (ls.get ⟨j, hj⟩).pt t d 1) (h2 : (p 2).1 = (ls.get ⟨j, hj⟩).pt t d 2) :
    False := by
  refine kill_fwd ht hd hW (s := tot (ls.take j)) (tot_even _) hp ?_ ?_ ?_ <;> beta_reduce
  · rw [h0, Nat.mod_eq_of_lt (by omega)]
    have := wk_at ls hch j hj 0 (by omega); rw [Nat.add_zero] at this; rw [this]
  · rw [h1, Nat.mod_eq_of_lt (by omega), wk_at ls hch j hj 1 (by omega)]
  · rw [h2, Nat.mod_eq_of_lt (by omega), wk_at ls hch j hj 2 (by omega)]

theorem kill_at_bwd (ht : 2 ≤ t) (hd : 2 ≤ d) {ls : List Blk} {N : ℕ} (hch : Chain t d ls)
    (hW : IsCStrip t d (fun k => wk t d ls (k % N)) N) (j jp δ : ℕ) (hj : j < ls.length)
    (hjp : jp < ls.length) (hlt : tot (ls.take j) < N) (hLp : 1 ≤ (ls.get ⟨jp, hjp⟩).L)
    (hle : tot (ls.take jp) + 2 * (ls.get ⟨jp, hjp⟩).L ≤ N)
    (hidx : tot (ls.take j) + N = tot (ls.take jp) + 2 * (ls.get ⟨jp, hjp⟩).L + N * δ)
    {n : ℕ} {p : ℕ → MS t d} (hp : LiteralPath (GM t d) n p)
    (h0 : (p 0).1 = (ls.get ⟨j, hj⟩).pt t d 0)
    (h1 : (p 1).1 = (ls.get ⟨jp, hjp⟩).pt t d (2 * (ls.get ⟨jp, hjp⟩).L - 1))
    (h2 : (p 2).1 = (ls.get ⟨jp, hjp⟩).pt t d (2 * (ls.get ⟨jp, hjp⟩).L - 2)) : False := by
  refine kill_bwd ht hd hW (s := tot (ls.take j)) (tot_even _) hp ?_ ?_ ?_ <;> beta_reduce
  · rw [h0, Nat.mod_eq_of_lt (by omega)]
    have := wk_at ls hch j hj 0 (by omega); rw [Nat.add_zero] at this; rw [this]
  · rw [h1, show tot (ls.take j) + N - 1 =
      tot (ls.take jp) + (2 * (ls.get ⟨jp, hjp⟩).L - 1) + N * δ by omega]
    have := hW.2.2.1
    rw [show (tot (ls.take jp) + (2 * (ls.get ⟨jp, hjp⟩).L - 1) + N * δ) % N =
      (tot (ls.take jp) + (2 * (ls.get ⟨jp, hjp⟩).L - 1)) % N by
        rw [Nat.add_mul_mod_self_left], Nat.mod_eq_of_lt (by omega), wk_at ls hch jp hjp _ (by omega)]
  · rw [h2, show tot (ls.take j) + N - 2 =
      tot (ls.take jp) + (2 * (ls.get ⟨jp, hjp⟩).L - 2) + N * δ by omega]
    rw [show (tot (ls.take jp) + (2 * (ls.get ⟨jp, hjp⟩).L - 2) + N * δ) % N =
      (tot (ls.take jp) + (2 * (ls.get ⟨jp, hjp⟩).L - 2)) % N by
        rw [Nat.add_mul_mod_self_left], Nat.mod_eq_of_lt (by omega), wk_at ls hch jp hjp _ (by omega)]

end Claude5O2
