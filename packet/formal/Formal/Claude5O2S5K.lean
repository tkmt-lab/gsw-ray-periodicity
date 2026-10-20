import Formal.Claude5O2S5

/-! O2 model: closed strip 5, chain and kill lemmas (part 2; split from the generated file at a theorem boundary.) -/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000

namespace Claude5O2

open ClaudeChallenge Claude2Aligned


theorem chain5 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) : Chain (t : ℤ) (d : ℤ) (bs5 t d ++ [b5_0 t d]) := by
  simp only [bs5, List.cons_append, List.nil_append, Chain]
  exact ⟨ok5_0 t d ht hd, by simp only [b5_0]; omega, junc5_0 t d ht hd, ok5_1 t d ht hd, by simp only [b5_1]; omega, junc5_1 t d ht hd, ok5_0 t d ht hd, by simp only [b5_0]; omega⟩
theorem cs5 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) : IsCStrip (t : ℤ) (d : ℤ) (fun k => wk (t : ℤ) (d : ℤ) (bs5 t d ++ [b5_0 t d]) (k % tot (bs5 t d))) (tot (bs5 t d)) := by
  have ht1 := one_le_of_two ht; have hd1 := one_le_of_two hd
  refine cstrip_of_chain ht1 (bs5 t d) (b5_0 t d) [b5_1 t d] rfl (chain5 t d ht hd) (by simp only [bs5, tot, b5_0, b5_1]; omega) ?_
  intro b hb
  simp only [bs5, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  exacts [odd5_0 t d ht hd, odd5_1 t d ht hd]
theorem kf5_0 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 0 ((2 * (t : ℤ)), ((d : ℤ)))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 0 ((2 * (t : ℤ) - 1), ((d : ℤ) + 1))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 0 ((2 * (t : ℤ) - 1), ((d : ℤ)))) : False :=
  kill_at_fwd (two_le_of_two ht) (two_le_of_two hd) (chain5 t d ht hd) (cs5 t d ht hd) 0 (by simp [bs5]) (by simp [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b5_0] <;> omega) (by simp [bs5, tot, b5_0, b5_1] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_0, b5_0] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_1, b5_0] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_2, b5_0] <;> first | rfl | (congr 1; peq))
theorem kb5_0 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 1 ((2 * (t : ℤ)), ((d : ℤ)))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 1 ((2 * (t : ℤ) - 1), ((d : ℤ) + 1))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 1 ((2 * (t : ℤ) - 1), ((d : ℤ)))) : False :=
  kill_at_bwd (two_le_of_two ht) (two_le_of_two hd) (chain5 t d ht hd) (cs5 t d ht hd) 0 1 0 (by simp [bs5]) (by simp [bs5]) (by simp [bs5, tot, b5_0, b5_1] <;> omega) (by simp [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b5_1] <;> omega) (by simp [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs5, tot, b5_0, b5_1] <;> omega) (by simp [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs5, tot, b5_0, b5_1] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [← (junc5_1 t d ht hd).1, pt_e]; simp only [b5_1] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e1 (b5_1 t d) (by simp only [b5_1]; omega)]; simp only [b5_1] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e2 (b5_1 t d) (by simp only [b5_1]; omega)]; simp only [b5_1] <;> first | rfl | (congr 1; peq))
theorem kf5_1 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 1 ((-(d : ℤ)), ((d : ℤ)))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 1 ((-(d : ℤ)), ((d : ℤ) + 1))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 1 ((-(d : ℤ) + 1), ((d : ℤ)))) : False :=
  kill_at_fwd (two_le_of_two ht) (two_le_of_two hd) (chain5 t d ht hd) (cs5 t d ht hd) 1 (by simp [bs5]) (by simp [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b5_1] <;> omega) (by simp [bs5, tot, b5_0, b5_1] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_0, b5_1] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_1, b5_1] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_2, b5_1] <;> first | rfl | (congr 1; peq))
theorem kb5_1 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 0 ((-(d : ℤ)), ((d : ℤ)))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 0 ((-(d : ℤ)), ((d : ℤ) + 1))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 0 ((-(d : ℤ) + 1), ((d : ℤ)))) : False :=
  kill_at_bwd (two_le_of_two ht) (two_le_of_two hd) (chain5 t d ht hd) (cs5 t d ht hd) 1 0 1 (by simp [bs5]) (by simp [bs5]) (by simp [bs5, tot, b5_0, b5_1] <;> omega) (by simp [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b5_0] <;> omega) (by simp [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs5, tot, b5_0, b5_1] <;> omega) (by simp [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs5, tot, b5_0, b5_1] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [← (junc5_0 t d ht hd).1, pt_e]; simp only [b5_0] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e1 (b5_0 t d) (by simp only [b5_0]; omega)]; simp only [b5_0] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs5, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e2 (b5_0 t d) (by simp only [b5_0]; omega)]; simp only [b5_0] <;> first | rfl | (congr 1; peq))
end Claude5O2
