import Formal.Claude5O2S7

/-! O2 model: closed strip 7, chain and kill lemmas (part 2; split from the generated file at a theorem boundary.) -/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000

namespace Claude5O2

open ClaudeChallenge Claude2Aligned


theorem chain7 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) : Chain (t : ℤ) (d : ℤ) (bs7 t d ++ [b7_0 t d]) := by
  simp only [bs7, List.cons_append, List.nil_append, Chain]
  exact ⟨ok7_0 t d ht hd, by simp only [b7_0]; omega, junc7_0 t d ht hd, ok7_1 t d ht hd, by simp only [b7_1]; omega, junc7_1 t d ht hd, ok7_2 t d ht hd, by simp only [b7_2]; omega, junc7_2 t d ht hd, ok7_3 t d ht hd, by simp only [b7_3]; omega, junc7_3 t d ht hd, ok7_0 t d ht hd, by simp only [b7_0]; omega⟩
theorem cs7 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) : IsCStrip (t : ℤ) (d : ℤ) (fun k => wk (t : ℤ) (d : ℤ) (bs7 t d ++ [b7_0 t d]) (k % tot (bs7 t d))) (tot (bs7 t d)) := by
  have ht1 := one_le_of_two ht; have hd1 := one_le_of_two hd
  refine cstrip_of_chain ht1 (bs7 t d) (b7_0 t d) [b7_1 t d, b7_2 t d, b7_3 t d] rfl (chain7 t d ht hd) (by simp only [bs7, tot, b7_0, b7_1, b7_2, b7_3]; omega) ?_
  intro b hb
  simp only [bs7, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  exacts [odd7_0 t d ht hd, odd7_1 t d ht hd, odd7_2 t d ht hd, odd7_3 t d ht hd]
theorem kf7_0 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 0 (((t : ℤ)), (0))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 0 (((t : ℤ) - 1), (1))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 0 (((t : ℤ)), (1))) : False :=
  kill_at_fwd (two_le_of_two ht) (two_le_of_two hd) (chain7 t d ht hd) (cs7 t d ht hd) 0 (by simp [bs7]) (by simp [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b7_0] <;> omega) (by simp [bs7, tot, b7_0, b7_1, b7_2, b7_3] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_0, b7_0] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_1, b7_0] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_2, b7_0] <;> first | rfl | (congr 1; peq))
theorem kb7_0 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 2 ((0), ((t : ℤ)))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 2 ((0), ((t : ℤ) - 1))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 2 ((1), ((t : ℤ) - 1))) : False :=
  kill_at_bwd (two_le_of_two ht) (two_le_of_two hd) (chain7 t d ht hd) (cs7 t d ht hd) 0 3 0 (by simp [bs7]) (by simp [bs7]) (by simp [bs7, tot, b7_0, b7_1, b7_2, b7_3] <;> omega) (by simp [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b7_3] <;> omega) (by simp [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs7, tot, b7_0, b7_1, b7_2, b7_3] <;> omega) (by simp [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs7, tot, b7_0, b7_1, b7_2, b7_3] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [← (junc7_3 t d ht hd).1, pt_e]; simp only [b7_3] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e1 (b7_3 t d) (by simp only [b7_3]; omega)]; simp only [b7_3] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e2 (b7_3 t d) (by simp only [b7_3]; omega)]; simp only [b7_3] <;> first | rfl | (congr 1; peq))
theorem kf7_1 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 3 ((0), ((t : ℤ)))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 3 ((1), ((t : ℤ)))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 3 ((1), ((t : ℤ) - 1))) : False :=
  kill_at_fwd (two_le_of_two ht) (two_le_of_two hd) (chain7 t d ht hd) (cs7 t d ht hd) 1 (by simp [bs7]) (by simp [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b7_1] <;> omega) (by simp [bs7, tot, b7_0, b7_1, b7_2, b7_3] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_0, b7_1] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_1, b7_1] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_2, b7_1] <;> first | rfl | (congr 1; peq))
theorem kb7_1 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 0 (((t : ℤ)), ((t : ℤ) + (d : ℤ)))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 0 (((t : ℤ) - 1), ((t : ℤ) + (d : ℤ)))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 0 (((t : ℤ)), ((t : ℤ) + (d : ℤ) - 1))) : False :=
  kill_at_bwd (two_le_of_two ht) (two_le_of_two hd) (chain7 t d ht hd) (cs7 t d ht hd) 1 0 1 (by simp [bs7]) (by simp [bs7]) (by simp [bs7, tot, b7_0, b7_1, b7_2, b7_3] <;> omega) (by simp [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b7_0] <;> omega) (by simp [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs7, tot, b7_0, b7_1, b7_2, b7_3] <;> omega) (by simp [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs7, tot, b7_0, b7_1, b7_2, b7_3] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [← (junc7_0 t d ht hd).1, pt_e]; simp only [b7_0] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e1 (b7_0 t d) (by simp only [b7_0]; omega)]; simp only [b7_0] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e2 (b7_0 t d) (by simp only [b7_0]; omega)]; simp only [b7_0] <;> first | rfl | (congr 1; peq))
theorem kf7_2 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 1 (((t : ℤ)), ((t : ℤ) + (d : ℤ)))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 1 (((t : ℤ) - 1), ((t : ℤ) + (d : ℤ)))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 1 (((t : ℤ)), ((t : ℤ) + (d : ℤ) - 1))) : False :=
  kill_at_fwd (two_le_of_two ht) (two_le_of_two hd) (chain7 t d ht hd) (cs7 t d ht hd) 2 (by simp [bs7]) (by simp [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b7_2] <;> omega) (by simp [bs7, tot, b7_0, b7_1, b7_2, b7_3] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_0, b7_2] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_1, b7_2] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_2, b7_2] <;> first | rfl | (congr 1; peq))
theorem kb7_2 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 3 (((t : ℤ)), (0))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 3 (((t : ℤ)), (1))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 3 (((t : ℤ) - 1), (1))) : False :=
  kill_at_bwd (two_le_of_two ht) (two_le_of_two hd) (chain7 t d ht hd) (cs7 t d ht hd) 2 1 1 (by simp [bs7]) (by simp [bs7]) (by simp [bs7, tot, b7_0, b7_1, b7_2, b7_3] <;> omega) (by simp [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b7_1] <;> omega) (by simp [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs7, tot, b7_0, b7_1, b7_2, b7_3] <;> omega) (by simp [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs7, tot, b7_0, b7_1, b7_2, b7_3] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [← (junc7_1 t d ht hd).1, pt_e]; simp only [b7_1] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e1 (b7_1 t d) (by simp only [b7_1]; omega)]; simp only [b7_1] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e2 (b7_1 t d) (by simp only [b7_1]; omega)]; simp only [b7_1] <;> first | rfl | (congr 1; peq))
theorem kf7_3 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 2 (((t : ℤ)), (0))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 2 (((t : ℤ) - 1), (0))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 2 (((t : ℤ) - 1), (1))) : False :=
  kill_at_fwd (two_le_of_two ht) (two_le_of_two hd) (chain7 t d ht hd) (cs7 t d ht hd) 3 (by simp [bs7]) (by simp [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b7_3] <;> omega) (by simp [bs7, tot, b7_0, b7_1, b7_2, b7_3] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_0, b7_3] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_1, b7_3] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_2, b7_3] <;> first | rfl | (congr 1; peq))
theorem kb7_3 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 1 (((t : ℤ)), (0))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 1 (((t : ℤ) - 1), (1))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 1 (((t : ℤ)), (1))) : False :=
  kill_at_bwd (two_le_of_two ht) (two_le_of_two hd) (chain7 t d ht hd) (cs7 t d ht hd) 3 2 1 (by simp [bs7]) (by simp [bs7]) (by simp [bs7, tot, b7_0, b7_1, b7_2, b7_3] <;> omega) (by simp [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b7_2] <;> omega) (by simp [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs7, tot, b7_0, b7_1, b7_2, b7_3] <;> omega) (by simp [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs7, tot, b7_0, b7_1, b7_2, b7_3] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [← (junc7_2 t d ht hd).1, pt_e]; simp only [b7_2] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e1 (b7_2 t d) (by simp only [b7_2]; omega)]; simp only [b7_2] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs7, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e2 (b7_2 t d) (by simp only [b7_2]; omega)]; simp only [b7_2] <;> first | rfl | (congr 1; peq))
end Claude5O2
