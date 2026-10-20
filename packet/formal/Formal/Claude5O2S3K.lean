import Formal.Claude5O2S3

/-! O2 model: closed strip 3, chain and kill lemmas (part 2; split from the generated file at a theorem boundary.) -/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000

namespace Claude5O2

open ClaudeChallenge Claude2Aligned


theorem chain3 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) : Chain (t : ℤ) (d : ℤ) (bs3 t d ++ [b3_0 t d]) := by
  simp only [bs3, List.cons_append, List.nil_append, Chain]
  exact ⟨ok3_0 t d ht hd, by simp only [b3_0]; omega, junc3_0 t d ht hd, ok3_1 t d ht hd, by simp only [b3_1]; omega, junc3_1 t d ht hd, ok3_0 t d ht hd, by simp only [b3_0]; omega⟩
theorem cs3 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) : IsCStrip (t : ℤ) (d : ℤ) (fun k => wk (t : ℤ) (d : ℤ) (bs3 t d ++ [b3_0 t d]) (k % tot (bs3 t d))) (tot (bs3 t d)) := by
  have ht1 := one_le_of_two ht; have hd1 := one_le_of_two hd
  refine cstrip_of_chain ht1 (bs3 t d) (b3_0 t d) [b3_1 t d] rfl (chain3 t d ht hd) (by simp only [bs3, tot, b3_0, b3_1]; omega) ?_
  intro b hb
  simp only [bs3, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  exacts [odd3_0 t d ht hd, odd3_1 t d ht hd]
theorem kf3_0 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 0 ((0), (0))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 0 ((1), (0))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 0 ((0), (1))) : False :=
  kill_at_fwd (two_le_of_two ht) (two_le_of_two hd) (chain3 t d ht hd) (cs3 t d ht hd) 0 (by simp [bs3]) (by simp [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b3_0] <;> omega) (by simp [bs3, tot, b3_0, b3_1] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_0, b3_0] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_1, b3_0] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_2, b3_0] <;> first | rfl | (congr 1; peq))
theorem kb3_0 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 1 ((0), (0))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 1 ((1), (0))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 1 ((0), (1))) : False :=
  kill_at_bwd (two_le_of_two ht) (two_le_of_two hd) (chain3 t d ht hd) (cs3 t d ht hd) 0 1 0 (by simp [bs3]) (by simp [bs3]) (by simp [bs3, tot, b3_0, b3_1] <;> omega) (by simp [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b3_1] <;> omega) (by simp [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs3, tot, b3_0, b3_1] <;> omega) (by simp [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs3, tot, b3_0, b3_1] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [← (junc3_1 t d ht hd).1, pt_e]; simp only [b3_1] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e1 (b3_1 t d) (by simp only [b3_1]; omega)]; simp only [b3_1] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e2 (b3_1 t d) (by simp only [b3_1]; omega)]; simp only [b3_1] <;> first | rfl | (congr 1; peq))
theorem kf3_1 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 1 ((0), (2 * (t : ℤ) + (d : ℤ)))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 1 ((1), (2 * (t : ℤ) + (d : ℤ) - 1))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 1 ((0), (2 * (t : ℤ) + (d : ℤ) - 1))) : False :=
  kill_at_fwd (two_le_of_two ht) (two_le_of_two hd) (chain3 t d ht hd) (cs3 t d ht hd) 1 (by simp [bs3]) (by simp [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b3_1] <;> omega) (by simp [bs3, tot, b3_0, b3_1] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_0, b3_1] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_1, b3_1] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_2, b3_1] <;> first | rfl | (congr 1; peq))
theorem kb3_1 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 0 ((0), (2 * (t : ℤ) + (d : ℤ)))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 0 ((1), (2 * (t : ℤ) + (d : ℤ) - 1))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 0 ((0), (2 * (t : ℤ) + (d : ℤ) - 1))) : False :=
  kill_at_bwd (two_le_of_two ht) (two_le_of_two hd) (chain3 t d ht hd) (cs3 t d ht hd) 1 0 1 (by simp [bs3]) (by simp [bs3]) (by simp [bs3, tot, b3_0, b3_1] <;> omega) (by simp [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b3_0] <;> omega) (by simp [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs3, tot, b3_0, b3_1] <;> omega) (by simp [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs3, tot, b3_0, b3_1] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [← (junc3_0 t d ht hd).1, pt_e]; simp only [b3_0] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e1 (b3_0 t d) (by simp only [b3_0]; omega)]; simp only [b3_0] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs3, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e2 (b3_0 t d) (by simp only [b3_0]; omega)]; simp only [b3_0] <;> first | rfl | (congr 1; peq))
end Claude5O2
