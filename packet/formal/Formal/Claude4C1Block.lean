import Formal.Claude4C1Strip
import Mathlib.Tactic.Ring

/-!
# Blocks of a strip: checks that reduce to linear arithmetic

Written by a Claude worker (2026-10-20, C1 bridge session).

* `RootIn v d`  : `v = e_i - e_j` with `d ∉ {i, j}` (decidable for explicit `v`);
* `blkOK_of`    : a block whose steps `E`, `D - E`, `D` are roots avoiding a face coordinate `d`
                  with `A_d ∈ {0, r+s}`, and whose points lie on the surface, is a strip;
* `adjR_of_root`: adjacency from an explicit root and face;
* `OddOK`, `oddOK_of_chain` : the odd-indexed points of a chain are not corners (or follow a
                  corner) if this holds block by block;
* `cornerP_iff` : the corner condition in coordinates.
-/

namespace Claude4C1

open ClaudeChallenge Claude2Aligned

variable {r s : ℤ}

/-- `v` is a root `e_i - e_j` with `d ∉ {i, j}`. -/
def RootIn (v : Fin 4 → ℤ) (d : Fin 4) : Prop :=
  ∃ i j : Fin 4, i ≠ j ∧ d ≠ i ∧ d ≠ j ∧ ∀ t, v t = rt i j t

instance (v : Fin 4 → ℤ) (d : Fin 4) : Decidable (RootIn v d) := by unfold RootIn; infer_instance

theorem RootIn.zero {v : Fin 4 → ℤ} {d : Fin 4} (h : RootIn v d) : v d = 0 := by
  obtain ⟨i, j, -, hi, hj, hv⟩ := h
  rw [hv, rt_ne hi hj]

theorem adjR_of_root {x y v : Fin 4 → ℤ} {d : Fin 4} (hv : RootIn v d)
    (hd : x d = 0 ∨ x d = r + s) (hy : ∀ t, y t = x t + v t) : AdjR r s x y := by
  obtain ⟨i, j, hij, hi, hj, hvt⟩ := hv
  exact ⟨i, j, hij, funext fun t => by rw [hy, hvt]; rfl, d, hi, hj, hd⟩

theorem pt_apply (b : Blk) (m : ℕ) (t : Fin 4) :
    b.pt m t = b.A t + ((m / 2 : ℕ) : ℤ) * b.D t + ((m % 2 : ℕ) : ℤ) * b.E t := by
  simp [Blk.pt]

theorem blkOK_of (b : Blk) (d : Fin 4) (hfd : b.A d = 0 ∨ b.A d = r + s) (hD : RootIn b.D d)
    (hE : RootIn b.E d) (hDE : RootIn (b.D - b.E) d) (hne1 : ∃ t, b.D t + b.E t ≠ 0)
    (hne2 : ∃ t, 2 * b.D t - b.E t ≠ 0) (hpts : ∀ m, m ≤ 2 * b.L → InS r s (b.pt m)) :
    StripOK r s b.pt (2 * b.L) := by
  have hDd := hD.zero
  have hEd := hE.zero
  have hface : ∀ m, b.pt m d = 0 ∨ b.pt m d = r + s := by
    intro m; rw [pt_apply, hDd, hEd]; simpa using hfd
  refine ⟨hpts, fun m _ => ?_, fun m _ => ?_, fun m _ => ?_⟩
  · rcases Nat.mod_two_eq_zero_or_one m with h | h
    · refine adjR_of_root hE (hface m) fun t => ?_
      rw [pt_apply, pt_apply, show (m + 1) / 2 = m / 2 by omega, show (m + 1) % 2 = 1 by omega, h]
      push_cast; ring
    · refine adjR_of_root hDE (hface m) fun t => ?_
      rw [pt_apply, pt_apply, show (m + 1) / 2 = m / 2 + 1 by omega,
        show (m + 1) % 2 = 0 by omega, h]
      simp only [Pi.sub_apply]; push_cast; ring
  · refine adjR_of_root hD (hface m) fun t => ?_
    rw [pt_apply, pt_apply, show (m + 2) / 2 = m / 2 + 1 by omega,
      show (m + 2) % 2 = m % 2 by omega]
    push_cast; ring
  · intro h
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm
    · obtain ⟨t, ht⟩ := hne1
      have := congrFun h t
      rw [pt_apply, pt_apply, show (m + 3) / 2 = m / 2 + 1 by omega,
        show (m + 3) % 2 = 1 by omega, hm] at this
      push_cast at this; apply ht; linarith
    · obtain ⟨t, ht⟩ := hne2
      have := congrFun h t
      rw [pt_apply, pt_apply, show (m + 3) / 2 = m / 2 + 2 by omega,
        show (m + 3) % 2 = 0 by omega, hm] at this
      push_cast at this; apply ht; linarith

theorem cornerP_iff {x : Fin 4 → ℤ} : CornerP r s x ↔
    (x 0 = r + s ∨ x 1 = r + s ∨ x 2 = r + s ∨ x 3 = r + s) ∧
      ((x 0 = 0 ∧ x 1 = 0) ∨ (x 0 = 0 ∧ x 2 = 0) ∨ (x 0 = 0 ∧ x 3 = 0) ∨ (x 1 = 0 ∧ x 2 = 0) ∨
        (x 1 = 0 ∧ x 3 = 0) ∨ (x 2 = 0 ∧ x 3 = 0)) := by
  constructor
  · rintro ⟨⟨a, ha⟩, b, c, hbc, hb, hc⟩
    refine ⟨by fin_cases a <;> simp_all, ?_⟩
    fin_cases b <;> fin_cases c <;> simp_all
  · rintro ⟨ha, hz⟩
    refine ⟨?_, ?_⟩
    · rcases ha with h | h | h | h
      exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]
    · rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      exacts [⟨0, 1, by decide, h1, h2⟩, ⟨0, 2, by decide, h1, h2⟩, ⟨0, 3, by decide, h1, h2⟩,
        ⟨1, 2, by decide, h1, h2⟩, ⟨1, 3, by decide, h1, h2⟩, ⟨2, 3, by decide, h1, h2⟩]

/-- Odd-indexed points of a block are not corners, or follow a corner. -/
def OddOK (r s : ℤ) (W : ℕ → Fin 4 → ℤ) (N : ℕ) : Prop :=
  ∀ k, k < N → k % 2 = 1 → ¬ CornerP r s (W k) ∨ CornerP r s (W (k - 1))

/-- Chains whose blocks are `OddOK`. -/
def ChainOdd (r s : ℤ) : List Blk → Prop
  | [] => True
  | b :: bs => OddOK r s b.pt (2 * b.L) ∧ ChainOdd r s bs

theorem oddOK_of_chain : ∀ bs : List Blk, Chain r s bs → ChainOdd r s bs →
    OddOK r s (wk bs) (tot bs)
  | [], h, _ => h.elim
  | [b], h, ho => by simpa [wk, tot] using ho.1
  | b :: b' :: bs, h, ho => by
    have ih := oddOK_of_chain (b' :: bs) h.2.2.2 ho.2
    have hW : ∀ m, m ≤ 2 * b.L → wk (b :: b' :: bs) m = b.pt m := wk_head h
    have hT : ∀ m, wk (b :: b' :: bs) (2 * b.L + m) = wk (b' :: bs) m := wk_tail b b' bs
    intro k hk hodd
    simp only [tot] at hk
    by_cases h1 : k < 2 * b.L
    · rw [hW k (by omega), hW (k - 1) (by omega)]; exact ho.1 k h1 hodd
    · obtain ⟨m, rfl⟩ : ∃ m, k = 2 * b.L + m := ⟨k - 2 * b.L, by omega⟩
      have hm1 : 1 ≤ m := by omega
      rw [hT, show 2 * b.L + m - 1 = 2 * b.L + (m - 1) by omega, hT]
      exact ih m (by simp only [tot]; omega) (by omega)

end Claude4C1
