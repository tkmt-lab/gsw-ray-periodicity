import Formal.Claude5O2S9

/-! O2 model: closed strip 9, chain and kill lemmas (part 2; split from the generated file at a theorem boundary.) -/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000

namespace Claude5O2

open ClaudeChallenge Claude2Aligned


theorem chain9 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) : Chain (t : ℤ) (d : ℤ) (bs9 t d ++ [b9_0 t d]) := by
  simp only [bs9, List.cons_append, List.nil_append, Chain]
  exact ⟨ok9_0 t d ht hd, by simp only [b9_0]; omega, junc9_0 t d ht hd, ok9_1 t d ht hd, by simp only [b9_1]; omega, junc9_1 t d ht hd, ok9_2 t d ht hd, by simp only [b9_2]; omega, junc9_2 t d ht hd, ok9_3 t d ht hd, by simp only [b9_3]; omega, junc9_3 t d ht hd, ok9_0 t d ht hd, by simp only [b9_0]; omega⟩
theorem cs9 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) : IsCStrip (t : ℤ) (d : ℤ) (fun k => wk (t : ℤ) (d : ℤ) (bs9 t d ++ [b9_0 t d]) (k % tot (bs9 t d))) (tot (bs9 t d)) := by
  have ht1 := one_le_of_two ht; have hd1 := one_le_of_two hd
  refine cstrip_of_chain ht1 (bs9 t d) (b9_0 t d) [b9_1 t d, b9_2 t d, b9_3 t d] rfl (chain9 t d ht hd) (by simp only [bs9, tot, b9_0, b9_1, b9_2, b9_3]; omega) ?_
  intro b hb
  simp only [bs9, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  exacts [odd9_0 t d ht hd, odd9_1 t d ht hd, odd9_2 t d ht hd, odd9_3 t d ht hd]
theorem kf9_0 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 0 (((t : ℤ)), ((t : ℤ) + (d : ℤ)))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 0 (((t : ℤ)), ((t : ℤ) + (d : ℤ) - 1))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 0 (((t : ℤ) - 1), ((t : ℤ) + (d : ℤ)))) : False :=
  kill_at_fwd (two_le_of_two ht) (two_le_of_two hd) (chain9 t d ht hd) (cs9 t d ht hd) 0 (by simp [bs9]) (by simp [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b9_0] <;> omega) (by simp [bs9, tot, b9_0, b9_1, b9_2, b9_3] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_0, b9_0] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_1, b9_0] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_2, b9_0] <;> first | rfl | (congr 1; peq))
theorem kb9_0 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 3 ((0), ((t : ℤ)))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 3 ((0), ((t : ℤ) - 1))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 3 ((1), ((t : ℤ) - 1))) : False :=
  kill_at_bwd (two_le_of_two ht) (two_le_of_two hd) (chain9 t d ht hd) (cs9 t d ht hd) 0 3 0 (by simp [bs9]) (by simp [bs9]) (by simp [bs9, tot, b9_0, b9_1, b9_2, b9_3] <;> omega) (by simp [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b9_3] <;> omega) (by simp [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs9, tot, b9_0, b9_1, b9_2, b9_3] <;> omega) (by simp [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs9, tot, b9_0, b9_1, b9_2, b9_3] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [← (junc9_3 t d ht hd).1, pt_e]; simp only [b9_3] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e1 (b9_3 t d) (by simp only [b9_3]; omega)]; simp only [b9_3] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e2 (b9_3 t d) (by simp only [b9_3]; omega)]; simp only [b9_3] <;> first | rfl | (congr 1; peq))
theorem kf9_1 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 4 ((0), ((t : ℤ)))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 4 ((1), ((t : ℤ)))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 4 ((1), ((t : ℤ) - 1))) : False :=
  kill_at_fwd (two_le_of_two ht) (two_le_of_two hd) (chain9 t d ht hd) (cs9 t d ht hd) 1 (by simp [bs9]) (by simp [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b9_1] <;> omega) (by simp [bs9, tot, b9_0, b9_1, b9_2, b9_3] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_0, b9_1] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_1, b9_1] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_2, b9_1] <;> first | rfl | (congr 1; peq))
theorem kb9_1 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 0 ((-(d : ℤ)), ((t : ℤ) + (d : ℤ)))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 0 ((-(d : ℤ) + 1), ((t : ℤ) + (d : ℤ) - 1))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 0 ((-(d : ℤ) + 1), ((t : ℤ) + (d : ℤ)))) : False :=
  kill_at_bwd (two_le_of_two ht) (two_le_of_two hd) (chain9 t d ht hd) (cs9 t d ht hd) 1 0 1 (by simp [bs9]) (by simp [bs9]) (by simp [bs9, tot, b9_0, b9_1, b9_2, b9_3] <;> omega) (by simp [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b9_0] <;> omega) (by simp [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs9, tot, b9_0, b9_1, b9_2, b9_3] <;> omega) (by simp [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs9, tot, b9_0, b9_1, b9_2, b9_3] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [← (junc9_0 t d ht hd).1, pt_e]; simp only [b9_0] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e1 (b9_0 t d) (by simp only [b9_0]; omega)]; simp only [b9_0] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e2 (b9_0 t d) (by simp only [b9_0]; omega)]; simp only [b9_0] <;> first | rfl | (congr 1; peq))
theorem kf9_2 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 1 ((-(d : ℤ)), ((t : ℤ) + (d : ℤ)))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 1 ((-(d : ℤ) + 1), ((t : ℤ) + (d : ℤ) - 1))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 1 ((-(d : ℤ) + 1), ((t : ℤ) + (d : ℤ)))) : False :=
  kill_at_fwd (two_le_of_two ht) (two_le_of_two hd) (chain9 t d ht hd) (cs9 t d ht hd) 2 (by simp [bs9]) (by simp [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b9_2] <;> omega) (by simp [bs9, tot, b9_0, b9_1, b9_2, b9_3] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_0, b9_2] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_1, b9_2] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_2, b9_2] <;> first | rfl | (congr 1; peq))
theorem kb9_2 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 4 (((t : ℤ)), (0))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 4 (((t : ℤ)), (1))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 4 (((t : ℤ) - 1), (1))) : False :=
  kill_at_bwd (two_le_of_two ht) (two_le_of_two hd) (chain9 t d ht hd) (cs9 t d ht hd) 2 1 1 (by simp [bs9]) (by simp [bs9]) (by simp [bs9, tot, b9_0, b9_1, b9_2, b9_3] <;> omega) (by simp [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b9_1] <;> omega) (by simp [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs9, tot, b9_0, b9_1, b9_2, b9_3] <;> omega) (by simp [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs9, tot, b9_0, b9_1, b9_2, b9_3] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [← (junc9_1 t d ht hd).1, pt_e]; simp only [b9_1] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e1 (b9_1 t d) (by simp only [b9_1]; omega)]; simp only [b9_1] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e2 (b9_1 t d) (by simp only [b9_1]; omega)]; simp only [b9_1] <;> first | rfl | (congr 1; peq))
theorem kf9_3 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 3 (((t : ℤ)), (0))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 3 (((t : ℤ) - 1), (0))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 3 (((t : ℤ) - 1), (1))) : False :=
  kill_at_fwd (two_le_of_two ht) (two_le_of_two hd) (chain9 t d ht hd) (cs9 t d ht hd) 3 (by simp [bs9]) (by simp [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b9_3] <;> omega) (by simp [bs9, tot, b9_0, b9_1, b9_2, b9_3] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_0, b9_3] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_1, b9_3] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, pt_2, b9_3] <;> first | rfl | (congr 1; peq))
theorem kb9_3 (t d : ℕ) (ht : 2 ≤ t) (hd : 2 ≤ d) {n : ℕ} {p : ℕ → MS (t : ℤ) (d : ℤ)} (hp : LiteralPath (GM (t : ℤ) (d : ℤ)) n p) (h0 : (p 0).1 = ch (t : ℤ) (d : ℤ) 1 (((t : ℤ)), ((t : ℤ) + (d : ℤ)))) (h1 : (p 1).1 = ch (t : ℤ) (d : ℤ) 1 (((t : ℤ)), ((t : ℤ) + (d : ℤ) - 1))) (h2 : (p 2).1 = ch (t : ℤ) (d : ℤ) 1 (((t : ℤ) - 1), ((t : ℤ) + (d : ℤ)))) : False :=
  kill_at_bwd (two_le_of_two ht) (two_le_of_two hd) (chain9 t d ht hd) (cs9 t d ht hd) 3 2 1 (by simp [bs9]) (by simp [bs9]) (by simp [bs9, tot, b9_0, b9_1, b9_2, b9_3] <;> omega) (by simp [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, b9_2] <;> omega) (by simp [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs9, tot, b9_0, b9_1, b9_2, b9_3] <;> omega) (by simp [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, bs9, tot, b9_0, b9_1, b9_2, b9_3] <;> omega) hp
    (by rw [h0]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [← (junc9_2 t d ht hd).1, pt_e]; simp only [b9_2] <;> first | rfl | (congr 1; peq))
    (by rw [h1]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e1 (b9_2 t d) (by simp only [b9_2]; omega)]; simp only [b9_2] <;> first | rfl | (congr 1; peq))
    (by rw [h2]; simp only [List.get_eq_getElem, bs9, List.cons_append, List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero]; rw [pt_e2 (b9_2 t d) (by simp only [b9_2]; omega)]; simp only [b9_2] <;> first | rfl | (congr 1; peq))
end Claude5O2
