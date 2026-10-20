import Formal.Claude5D14Kill

/-!
# D14 model: helper lemmas for the generated strip files

Written by a Claude worker (2026-10-20, D14 bridge session), adapting `Claude5O2StripHelp.lean`.
-/

set_option linter.unusedVariables false

/-- Equality of explicit lattice points (linear arithmetic). -/
macro "peq" : tactic => `(tactic| (first | rfl | (simp only [Prod.mk.injEq, Prod.ext_iff, true_and, and_true] <;> omega)))

namespace Claude5D14

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

theorem pt_0 (b : Blk) : b.pt r s 0 = ch r s b.c (b.A.1, b.A.2) := by simp [Blk.pt, Blk.pos]

theorem pt_1 (b : Blk) : b.pt r s 1 = ch r s b.c (b.A.1 + b.E.1, b.A.2 + b.E.2) := by
  simp [Blk.pt, Blk.pos]

theorem pt_2 (b : Blk) : b.pt r s 2 = ch r s b.c (b.A.1 + b.D.1, b.A.2 + b.D.2) := by
  simp [Blk.pt, Blk.pos]

theorem pt_e (b : Blk) :
    b.pt r s (2 * b.L) = ch r s b.c (b.A.1 + (b.L : ℤ) * b.D.1, b.A.2 + (b.L : ℤ) * b.D.2) := by
  simp only [Blk.pt]; rw [pos_even]

theorem pt_e1 (b : Blk) (h : 1 ≤ b.L) : b.pt r s (2 * b.L - 1) =
    ch r s b.c (b.A.1 + ((b.L : ℤ) - 1) * b.D.1 + b.E.1, b.A.2 + ((b.L : ℤ) - 1) * b.D.2 + b.E.2) := by
  simp only [Blk.pt]
  rw [show 2 * b.L - 1 = 2 * (b.L - 1) + 1 by omega, pos_odd]
  push_cast [h]; rfl

theorem pt_e2 (b : Blk) (h : 1 ≤ b.L) : b.pt r s (2 * b.L - 2) =
    ch r s b.c (b.A.1 + ((b.L : ℤ) - 1) * b.D.1, b.A.2 + ((b.L : ℤ) - 1) * b.D.2) := by
  simp only [Blk.pt]
  rw [show 2 * b.L - 2 = 2 * (b.L - 1) by omega, pos_even]
  push_cast [h]; rfl

theorem pt_odd' (b : Blk) (i : ℕ) : b.pt r s (2 * i + 1) =
    ch r s b.c (b.A.1 + (i : ℤ) * b.D.1 + b.E.1, b.A.2 + (i : ℤ) * b.D.2 + b.E.2) := by
  simp only [Blk.pt]; rw [pos_odd]

theorem adj_ch (hr : 1 ≤ r) (hs : 1 ≤ s) {c : ℕ} (hc : c < 2) {P Q : ℤ × ℤ}
    (hP : Dom r s c P) (hQ : Dom r s c Q) (hu : Q - P ∈ unitVec) :
    AdjM r s (ch r s c P) (ch r s c Q) := by
  have := adj_of_unit hr hs hc hP (by simpa using hQ) hu (v := ch r s c P) rfl
  simpa using this

theorem one_le_of_two {n : ℕ} (h : 2 ≤ n) : (1 : ℤ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)

theorem two_le_of_two {n : ℕ} (h : 2 ≤ n) : (2 : ℤ) ≤ n := by exact_mod_cast h

theorem kill_at_fwd (hr : 2 ≤ r) (hs : 2 ≤ s) {ls : List Blk} {N : ℕ} (hch : Chain r s ls)
    (hW : IsCStrip r s (fun k => wk r s ls (k % N)) N) (j : ℕ) (hj : j < ls.length)
    (hL : 1 ≤ (ls.get ⟨j, hj⟩).L) (hlt : tot (ls.take j) + 2 < N) {n : ℕ} {p : ℕ → MS r s}
    (hp : LiteralPath (GM r s) n p) (h0 : (p 0).1 = (ls.get ⟨j, hj⟩).pt r s 0)
    (h1 : (p 1).1 = (ls.get ⟨j, hj⟩).pt r s 1) (h2 : (p 2).1 = (ls.get ⟨j, hj⟩).pt r s 2) :
    False := by
  refine kill_fwd hr hs hW (s0 := tot (ls.take j)) (tot_even _) hp ?_ ?_ ?_ <;> beta_reduce
  · rw [h0, Nat.mod_eq_of_lt (by omega)]
    have := wk_at ls hch j hj 0 (by omega); rw [Nat.add_zero] at this; rw [this]
  · rw [h1, Nat.mod_eq_of_lt (by omega), wk_at ls hch j hj 1 (by omega)]
  · rw [h2, Nat.mod_eq_of_lt (by omega), wk_at ls hch j hj 2 (by omega)]

theorem kill_at_bwd (hr : 2 ≤ r) (hs : 2 ≤ s) {ls : List Blk} {N : ℕ} (hch : Chain r s ls)
    (hW : IsCStrip r s (fun k => wk r s ls (k % N)) N) (j jp δ : ℕ) (hj : j < ls.length)
    (hjp : jp < ls.length) (hlt : tot (ls.take j) < N) (hLp : 1 ≤ (ls.get ⟨jp, hjp⟩).L)
    (hle : tot (ls.take jp) + 2 * (ls.get ⟨jp, hjp⟩).L ≤ N)
    (hidx : tot (ls.take j) + N = tot (ls.take jp) + 2 * (ls.get ⟨jp, hjp⟩).L + N * δ)
    {n : ℕ} {p : ℕ → MS r s} (hp : LiteralPath (GM r s) n p)
    (h0 : (p 0).1 = (ls.get ⟨j, hj⟩).pt r s 0)
    (h1 : (p 1).1 = (ls.get ⟨jp, hjp⟩).pt r s (2 * (ls.get ⟨jp, hjp⟩).L - 1))
    (h2 : (p 2).1 = (ls.get ⟨jp, hjp⟩).pt r s (2 * (ls.get ⟨jp, hjp⟩).L - 2)) : False := by
  refine kill_bwd hr hs hW (s0 := tot (ls.take j)) (tot_even _) hp ?_ ?_ ?_ <;> beta_reduce
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

end Claude5D14
