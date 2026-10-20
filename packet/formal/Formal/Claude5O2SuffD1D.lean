import Formal.Claude5O2SuffD1

/-! O2(t, 1): degrees and the literal path (part 2; split from the generated file at a theorem boundary.) -/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

theorem fD1_deg0 (t d : ℕ) (ht : 3 ≤ t) (hd : d = 1) (v : MS (t : ℤ) (d : ℤ)) (hv0 : v.1 = ch (t : ℤ) (d : ℤ) 0 (((t : ℤ)), (0))) : deg (GM (t : ℤ) (d : ℤ)) v = 5 := by
  have ht1 : (1 : ℤ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hv : v.1 = ch (t : ℤ) (d : ℤ) 0 (((t : ℤ)), (0)) := hv0.trans (by first | rfl | (congr 1; peq2))
  refine deg_eq_of v [ch (t : ℤ) (d : ℤ) 0 (((t : ℤ) + 1), (0)), ch (t : ℤ) (d : ℤ) 0 (((t : ℤ)), (1)), ch (t : ℤ) (d : ℤ) 0 (((t : ℤ) - 1), (1)), ch (t : ℤ) (d : ℤ) 0 (((t : ℤ) - 1), (0)), ch (t : ℤ) (d : ℤ) 2 ((1), ((t : ℤ) - 1))] ?_ ?_ ?_ ?_
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_0R ht1 hd1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk.injEq, ne_eq] at he ⊢; omega)⟩, ⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_0R ht1 hd1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk.injEq, ne_eq] at he ⊢; omega)⟩, ⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_0R ht1 hd1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk.injEq, ne_eq] at he ⊢; omega)⟩, ne_0R ht1 hd1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk.injEq, ne_eq] at he ⊢; omega)⟩
  · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> exact ch_valid ht1 hd1 (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega)
  · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact adj_via ht1 (c := 0) (P := (((t : ℤ)), (0))) (Q := (((t : ℤ) + 1), (0))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 0) (P := (((t : ℤ)), (0))) (Q := (((t : ℤ)), (1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 0) (P := (((t : ℤ)), (0))) (Q := (((t : ℤ) - 1), (1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 0) (P := (((t : ℤ)), (0))) (Q := (((t : ℤ) - 1), (0))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 2) (P := ((0), ((t : ℤ)))) (Q := ((1), ((t : ℤ) - 1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact tr_ch ht1 hd1 (by norm_num) (tr0R ((t : ℤ)) (by omega) (by omega) (by peq2) (by peq2))) (Eq.symm (by first | rfl | (congr 1; peq2)))
  · intro w hw
    obtain ⟨-, c, hc, z, u, hz, hzu, hu, e1, e2⟩ := hw
    rw [hv] at e1
    have hz0 : Dom (t : ℤ) (d : ℤ) 0 (((t : ℤ)), (0)) := by simp only [Dom, Hx, Rh] <;> omega
    rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩
    · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
      obtain rfl : z = (((t : ℤ)), (0)) := by
        rcases hce with ⟨h1, h2⟩ | h | h
        · exact h2
        · simp [Tr] at h
        · simp [Tr] at h
      rw [unit_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [← e2, show ((((t : ℤ)), (0)) : ℤ × ℤ) + (1, 0) = (((t : ℤ) + 1), (0)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inl (by first | rfl | (congr 1; peq2))
      · rw [← e2, show ((((t : ℤ)), (0)) : ℤ × ℤ) + (0, 1) = (((t : ℤ)), (1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inl (by first | rfl | (congr 1; peq2)))
      · rw [← e2, show ((((t : ℤ)), (0)) : ℤ × ℤ) + (-1, 1) = (((t : ℤ) - 1), (1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2))))
      · rw [← e2, show ((((t : ℤ)), (0)) : ℤ × ℤ) + (-1, 0) = (((t : ℤ) - 1), (0)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2)))))
      · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
      · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
    · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
      exfalso
      rcases hce with ⟨h1, h2⟩ | h | h
      · simp at h1
      · simp [Tr] at h
      · obtain ⟨h1, h2⟩ := h; simp only [Prod.ext_iff, OnD] at h1 h2 <;> omega
    · have hi : i < 3 := by omega
      interval_cases i
      · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
        obtain rfl : z = ((0), ((t : ℤ))) := by
          rcases hce with ⟨h1, h2⟩ | h | h
          · simp at h1
          · simp [Tr] at h
          · obtain ⟨l, h0, h1, h2, h3⟩ := h; rw [h3]; simp only [sp, Prod.ext_iff] at h2 ⊢ <;> omega
        rw [unit_iff] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [← e2, show (((0), ((t : ℤ))) : ℤ × ℤ) + (1, 0) = ((1), ((t : ℤ))) by peq2]
          simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inl (Eq.symm (tr_ch ht1 hd1 (by norm_num) (tr0R ((t : ℤ) + 1) (by omega) (by omega) (by peq2) (by peq2))))
        · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
        · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
        · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
        · rw [← e2, show (((0), ((t : ℤ))) : ℤ × ℤ) + (0, -1) = ((0), ((t : ℤ) - 1)) by peq2]
          simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inl (Eq.symm (tr_ch ht1 hd1 (by norm_num) (tr0R ((t : ℤ) - 1) (by omega) (by omega) (by peq2) (by peq2)))))))
        · rw [← e2, show (((0), ((t : ℤ))) : ℤ × ℤ) + (1, -1) = ((1), ((t : ℤ) - 1)) by peq2]
          simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inr ((by first | rfl | (congr 1; peq2))))))
      · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
        exfalso
        rcases hce with ⟨h1, h2⟩ | h | h
        · simp at h1
        · simp [Tr] at h
        · obtain ⟨l, h0, h1, h2, h3⟩ := h; simp only [sp, Prod.ext_iff] at h2 h3 <;> omega
      · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
        exfalso
        rcases hce with ⟨h1, h2⟩ | h | h
        · simp at h1
        · simp [Tr] at h
        · obtain ⟨l, h0, h1, h2, h3⟩ := h; simp only [sp, Prod.ext_iff] at h2 h3 <;> omega
theorem fD1_deg1 (t d : ℕ) (ht : 3 ≤ t) (hd : d = 1) (v : MS (t : ℤ) (d : ℤ)) (hv0 : v.1 = ch (t : ℤ) (d : ℤ) 0 (((t : ℤ)), (1))) : deg (GM (t : ℤ) (d : ℤ)) v = 6 := by
  have ht1 : (1 : ℤ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hv : v.1 = ch (t : ℤ) (d : ℤ) 0 (((t : ℤ)), (1)) := hv0.trans (by first | rfl | (congr 1; peq2))
  refine deg_eq_of v [ch (t : ℤ) (d : ℤ) 0 (((t : ℤ) + 1), (1)), ch (t : ℤ) (d : ℤ) 0 (((t : ℤ)), (2)), ch (t : ℤ) (d : ℤ) 0 (((t : ℤ) - 1), (2)), ch (t : ℤ) (d : ℤ) 0 (((t : ℤ) - 1), (1)), ch (t : ℤ) (d : ℤ) 0 (((t : ℤ)), (0)), ch (t : ℤ) (d : ℤ) 0 (((t : ℤ) + 1), (0))] ?_ ?_ ?_ ?_
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩, ⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩, ⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩, ⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩, ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩
  · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ch_valid ht1 hd1 (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega)
  · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact adj_via ht1 (c := 0) (P := (((t : ℤ)), (1))) (Q := (((t : ℤ) + 1), (1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 0) (P := (((t : ℤ)), (1))) (Q := (((t : ℤ)), (2))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 0) (P := (((t : ℤ)), (1))) (Q := (((t : ℤ) - 1), (2))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 0) (P := (((t : ℤ)), (1))) (Q := (((t : ℤ) - 1), (1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 0) (P := (((t : ℤ)), (1))) (Q := (((t : ℤ)), (0))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 0) (P := (((t : ℤ)), (1))) (Q := (((t : ℤ) + 1), (0))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
  · intro w hw
    obtain ⟨-, c, hc, z, u, hz, hzu, hu, e1, e2⟩ := hw
    rw [hv] at e1
    have hz0 : Dom (t : ℤ) (d : ℤ) 0 (((t : ℤ)), (1)) := by simp only [Dom, Hx, Rh] <;> omega
    rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩
    · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
      obtain rfl : z = (((t : ℤ)), (1)) := by
        rcases hce with ⟨h1, h2⟩ | h | h
        · exact h2
        · simp [Tr] at h
        · simp [Tr] at h
      rw [unit_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [← e2, show ((((t : ℤ)), (1)) : ℤ × ℤ) + (1, 0) = (((t : ℤ) + 1), (1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inl (by first | rfl | (congr 1; peq2))
      · rw [← e2, show ((((t : ℤ)), (1)) : ℤ × ℤ) + (0, 1) = (((t : ℤ)), (2)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inl (by first | rfl | (congr 1; peq2)))
      · rw [← e2, show ((((t : ℤ)), (1)) : ℤ × ℤ) + (-1, 1) = (((t : ℤ) - 1), (2)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2))))
      · rw [← e2, show ((((t : ℤ)), (1)) : ℤ × ℤ) + (-1, 0) = (((t : ℤ) - 1), (1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2)))))
      · rw [← e2, show ((((t : ℤ)), (1)) : ℤ × ℤ) + (0, -1) = (((t : ℤ)), (0)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2))))))
      · rw [← e2, show ((((t : ℤ)), (1)) : ℤ × ℤ) + (1, -1) = (((t : ℤ) + 1), (0)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((by first | rfl | (congr 1; peq2)))))))
    · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
      exfalso
      rcases hce with ⟨h1, h2⟩ | h | h
      · simp at h1
      · simp [Tr] at h
      · obtain ⟨h1, h2⟩ := h; simp only [Prod.ext_iff, OnD] at h1 h2 <;> omega
    · have hi : i < 3 := by omega
      interval_cases i
      · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
        exfalso
        rcases hce with ⟨h1, h2⟩ | h | h
        · simp at h1
        · simp [Tr] at h
        · obtain ⟨l, h0, h1, h2, h3⟩ := h; simp only [sp, Prod.ext_iff] at h2 h3 <;> omega
      · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
        exfalso
        rcases hce with ⟨h1, h2⟩ | h | h
        · simp at h1
        · simp [Tr] at h
        · obtain ⟨l, h0, h1, h2, h3⟩ := h; simp only [sp, Prod.ext_iff] at h2 h3 <;> omega
      · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
        exfalso
        rcases hce with ⟨h1, h2⟩ | h | h
        · simp at h1
        · simp [Tr] at h
        · obtain ⟨l, h0, h1, h2, h3⟩ := h; simp only [sp, Prod.ext_iff] at h2 h3 <;> omega
theorem fD1_deg2 (t d : ℕ) (ht : 3 ≤ t) (hd : d = 1) (v : MS (t : ℤ) (d : ℤ)) (hv0 : v.1 = ch (t : ℤ) (d : ℤ) 1 (((t : ℤ)), ((t : ℤ)))) : deg (GM (t : ℤ) (d : ℤ)) v = 6 := by
  have ht1 : (1 : ℤ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hv : v.1 = ch (t : ℤ) (d : ℤ) 1 (((t : ℤ)), ((t : ℤ))) := hv0.trans (by first | rfl | (congr 1; peq2))
  refine deg_eq_of v [ch (t : ℤ) (d : ℤ) 1 (((t : ℤ) + 1), ((t : ℤ))), ch (t : ℤ) (d : ℤ) 1 (((t : ℤ)), ((t : ℤ) + 1)), ch (t : ℤ) (d : ℤ) 1 (((t : ℤ) - 1), ((t : ℤ) + 1)), ch (t : ℤ) (d : ℤ) 1 (((t : ℤ) - 1), ((t : ℤ))), ch (t : ℤ) (d : ℤ) 1 (((t : ℤ)), ((t : ℤ) - 1)), ch (t : ℤ) (d : ℤ) 1 (((t : ℤ) + 1), ((t : ℤ) - 1))] ?_ ?_ ?_ ?_
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩, ⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩, ⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩, ⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩, ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩
  · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ch_valid ht1 hd1 (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega)
  · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact adj_via ht1 (c := 1) (P := (((t : ℤ)), ((t : ℤ)))) (Q := (((t : ℤ) + 1), ((t : ℤ)))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 1) (P := (((t : ℤ)), ((t : ℤ)))) (Q := (((t : ℤ)), ((t : ℤ) + 1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 1) (P := (((t : ℤ)), ((t : ℤ)))) (Q := (((t : ℤ) - 1), ((t : ℤ) + 1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 1) (P := (((t : ℤ)), ((t : ℤ)))) (Q := (((t : ℤ) - 1), ((t : ℤ)))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 1) (P := (((t : ℤ)), ((t : ℤ)))) (Q := (((t : ℤ)), ((t : ℤ) - 1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 1) (P := (((t : ℤ)), ((t : ℤ)))) (Q := (((t : ℤ) + 1), ((t : ℤ) - 1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
  · intro w hw
    obtain ⟨-, c, hc, z, u, hz, hzu, hu, e1, e2⟩ := hw
    rw [hv] at e1
    have hz0 : Dom (t : ℤ) (d : ℤ) 1 (((t : ℤ)), ((t : ℤ))) := by simp only [Dom, Hx, Rh] <;> omega
    rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩
    · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
      exfalso
      rcases hce with ⟨h1, h2⟩ | h | h
      · simp at h1
      · obtain ⟨h1, h2⟩ := h; simp only [Prod.ext_iff, OnD] at h1 h2 <;> omega
      · simp [Tr] at h
    · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
      obtain rfl : z = (((t : ℤ)), ((t : ℤ))) := by
        rcases hce with ⟨h1, h2⟩ | h | h
        · exact h2
        · simp [Tr] at h
        · simp [Tr] at h
      rw [unit_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [← e2, show ((((t : ℤ)), ((t : ℤ))) : ℤ × ℤ) + (1, 0) = (((t : ℤ) + 1), ((t : ℤ))) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inl (by first | rfl | (congr 1; peq2))
      · rw [← e2, show ((((t : ℤ)), ((t : ℤ))) : ℤ × ℤ) + (0, 1) = (((t : ℤ)), ((t : ℤ) + 1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inl (by first | rfl | (congr 1; peq2)))
      · rw [← e2, show ((((t : ℤ)), ((t : ℤ))) : ℤ × ℤ) + (-1, 1) = (((t : ℤ) - 1), ((t : ℤ) + 1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2))))
      · rw [← e2, show ((((t : ℤ)), ((t : ℤ))) : ℤ × ℤ) + (-1, 0) = (((t : ℤ) - 1), ((t : ℤ))) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2)))))
      · rw [← e2, show ((((t : ℤ)), ((t : ℤ))) : ℤ × ℤ) + (0, -1) = (((t : ℤ)), ((t : ℤ) - 1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2))))))
      · rw [← e2, show ((((t : ℤ)), ((t : ℤ))) : ℤ × ℤ) + (1, -1) = (((t : ℤ) + 1), ((t : ℤ) - 1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((by first | rfl | (congr 1; peq2)))))))
    · have hi : i < 3 := by omega
      interval_cases i
      · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
        exfalso
        rcases hce with ⟨h1, h2⟩ | h | h
        · simp at h1
        · simp [Tr] at h
        · obtain ⟨l, h0, h1, h2, h3⟩ := h; simp only [sp, Prod.ext_iff] at h2 h3 <;> omega
      · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
        exfalso
        rcases hce with ⟨h1, h2⟩ | h | h
        · simp at h1
        · simp [Tr] at h
        · obtain ⟨l, h0, h1, h2, h3⟩ := h; simp only [sp, Prod.ext_iff] at h2 h3 <;> omega
      · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
        exfalso
        rcases hce with ⟨h1, h2⟩ | h | h
        · simp at h1
        · simp [Tr] at h
        · obtain ⟨l, h0, h1, h2, h3⟩ := h; simp only [sp, Prod.ext_iff] at h2 h3 <;> omega
theorem fD1_deg3 (t d : ℕ) (ht : 3 ≤ t) (hd : d = 1) (v : MS (t : ℤ) (d : ℤ)) (hv0 : v.1 = ch (t : ℤ) (d : ℤ) 1 (((t : ℤ)), ((t : ℤ) + 1))) : deg (GM (t : ℤ) (d : ℤ)) v = 5 := by
  have ht1 : (1 : ℤ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hv : v.1 = ch (t : ℤ) (d : ℤ) 1 (((t : ℤ)), ((t : ℤ) + 1)) := hv0.trans (by first | rfl | (congr 1; peq2))
  refine deg_eq_of v [ch (t : ℤ) (d : ℤ) 1 (((t : ℤ) - 1), ((t : ℤ) + 2)), ch (t : ℤ) (d : ℤ) 1 (((t : ℤ) - 1), ((t : ℤ) + 1)), ch (t : ℤ) (d : ℤ) 1 (((t : ℤ)), ((t : ℤ))), ch (t : ℤ) (d : ℤ) 1 (((t : ℤ) + 1), ((t : ℤ))), ch (t : ℤ) (d : ℤ) 3 (((t : ℤ) - 1), (1))] ?_ ?_ ?_ ?_
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_1R ht1 hd1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk.injEq, ne_eq] at he ⊢; omega)⟩, ⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_1R ht1 hd1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk.injEq, ne_eq] at he ⊢; omega)⟩, ⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_1R ht1 hd1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk.injEq, ne_eq] at he ⊢; omega)⟩, ne_1R ht1 hd1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by intro l h0 h1 he; simp only [sp, Prod.mk.injEq, ne_eq] at he ⊢; omega)⟩
  · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> exact ch_valid ht1 hd1 (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega)
  · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact adj_via ht1 (c := 1) (P := (((t : ℤ)), ((t : ℤ) + 1))) (Q := (((t : ℤ) - 1), ((t : ℤ) + 2))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 1) (P := (((t : ℤ)), ((t : ℤ) + 1))) (Q := (((t : ℤ) - 1), ((t : ℤ) + 1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 1) (P := (((t : ℤ)), ((t : ℤ) + 1))) (Q := (((t : ℤ)), ((t : ℤ)))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 1) (P := (((t : ℤ)), ((t : ℤ) + 1))) (Q := (((t : ℤ) + 1), ((t : ℤ)))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 3) (P := (((t : ℤ)), (0))) (Q := (((t : ℤ) - 1), (1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact tr_ch ht1 hd1 (by norm_num) (tr1R ((t : ℤ)) (by omega) (by omega) (by peq2) (by peq2))) (Eq.symm (by first | rfl | (congr 1; peq2)))
  · intro w hw
    obtain ⟨-, c, hc, z, u, hz, hzu, hu, e1, e2⟩ := hw
    rw [hv] at e1
    have hz0 : Dom (t : ℤ) (d : ℤ) 1 (((t : ℤ)), ((t : ℤ) + 1)) := by simp only [Dom, Hx, Rh] <;> omega
    rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩
    · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
      exfalso
      rcases hce with ⟨h1, h2⟩ | h | h
      · simp at h1
      · obtain ⟨h1, h2⟩ := h; simp only [Prod.ext_iff, OnD] at h1 h2 <;> omega
      · simp [Tr] at h
    · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
      obtain rfl : z = (((t : ℤ)), ((t : ℤ) + 1)) := by
        rcases hce with ⟨h1, h2⟩ | h | h
        · exact h2
        · simp [Tr] at h
        · simp [Tr] at h
      rw [unit_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
      · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
      · rw [← e2, show ((((t : ℤ)), ((t : ℤ) + 1)) : ℤ × ℤ) + (-1, 1) = (((t : ℤ) - 1), ((t : ℤ) + 2)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inl (by first | rfl | (congr 1; peq2))
      · rw [← e2, show ((((t : ℤ)), ((t : ℤ) + 1)) : ℤ × ℤ) + (-1, 0) = (((t : ℤ) - 1), ((t : ℤ) + 1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inl (by first | rfl | (congr 1; peq2)))
      · rw [← e2, show ((((t : ℤ)), ((t : ℤ) + 1)) : ℤ × ℤ) + (0, -1) = (((t : ℤ)), ((t : ℤ))) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2))))
      · rw [← e2, show ((((t : ℤ)), ((t : ℤ) + 1)) : ℤ × ℤ) + (1, -1) = (((t : ℤ) + 1), ((t : ℤ))) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2)))))
    · have hi : i < 3 := by omega
      interval_cases i
      · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
        exfalso
        rcases hce with ⟨h1, h2⟩ | h | h
        · simp at h1
        · simp [Tr] at h
        · obtain ⟨l, h0, h1, h2, h3⟩ := h; simp only [sp, Prod.ext_iff] at h2 h3 <;> omega
      · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
        obtain rfl : z = (((t : ℤ)), (0)) := by
          rcases hce with ⟨h1, h2⟩ | h | h
          · simp at h1
          · simp [Tr] at h
          · obtain ⟨l, h0, h1, h2, h3⟩ := h; rw [h3]; simp only [sp, Prod.ext_iff] at h2 ⊢ <;> omega
        rw [unit_iff] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
        · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
        · rw [← e2, show ((((t : ℤ)), (0)) : ℤ × ℤ) + (0, 1) = (((t : ℤ)), (1)) by peq2]
          simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inl (Eq.symm (tr_ch ht1 hd1 (by norm_num) (tr1R ((t : ℤ) + 1) (by omega) (by omega) (by peq2) (by peq2))))
        · rw [← e2, show ((((t : ℤ)), (0)) : ℤ × ℤ) + (-1, 1) = (((t : ℤ) - 1), (1)) by peq2]
          simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inr ((by first | rfl | (congr 1; peq2))))))
        · rw [← e2, show ((((t : ℤ)), (0)) : ℤ × ℤ) + (-1, 0) = (((t : ℤ) - 1), (0)) by peq2]
          simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inl (Eq.symm (tr_ch ht1 hd1 (by norm_num) (tr1R ((t : ℤ) - 1) (by omega) (by omega) (by peq2) (by peq2)))))))
        · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
        · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
      · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
        exfalso
        rcases hce with ⟨h1, h2⟩ | h | h
        · simp at h1
        · simp [Tr] at h
        · obtain ⟨l, h0, h1, h2, h3⟩ := h; simp only [sp, Prod.ext_iff] at h2 h3 <;> omega
theorem fD1_lit (t d : ℕ) (ht : 3 ≤ t) (hd : d = 1) : ∃ n p, LiteralPath (GM (t : ℤ) (d : ℤ)) n p := by
  have ht1 : (1 : ℤ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hS := strip_of_chain _ (fD1_chain t d ht hd)
  have hN : tot (fD1_bs t d) = (4 * t + 2) := by simp [fD1_bs, tot, fD1_0, fD1_1] <;> omega
  refine ⟨(4 * t + 2), fun k => ⟨wk (t : ℤ) (d : ℤ) (fD1_bs t d) (min k (tot (fD1_bs t d))), hS.1 _ (min_le_right _ _)⟩, ?_⟩
  refine literal_of_strip hS (by omega) (by omega) ⟨(2 * t + 1), by ring⟩ (fD1_inj t d ht hd) _ (fun k hk => by simp only [min_eq_left hk]) ?_ ?_ ?_ ?_
  · refine fD1_deg0 t d ht hd _ ?_
    simp only [min_eq_left (show 0 ≤ tot (fD1_bs t d) by omega)]
    rcases fD1_cls t d ht hd (0) (by omega) with ⟨a0, e⟩ | ⟨a0, e⟩ <;>
      first | (exfalso; omega) | ((rw [e]) <;> (try simp only [Blk.pt, Blk.pos, fD1_0, fD1_1]) <;> first | rfl | (congr 1; peq2))
  · refine fD1_deg3 t d ht hd _ ?_
    simp only [min_eq_left (show (4 * t + 2) - 1 ≤ tot (fD1_bs t d) by omega)]
    rcases fD1_cls t d ht hd ((4 * t + 2) - 1) (by omega) with ⟨a0, e⟩ | ⟨a0, e⟩ <;>
      first | (exfalso; omega) | ((rw [e]) <;> (try simp only [Blk.pt, Blk.pos, fD1_0, fD1_1]) <;> first | rfl | (congr 1; peq2))
  · refine fD1_deg1 t d ht hd _ ?_
    simp only [min_eq_left (show 1 ≤ tot (fD1_bs t d) by omega)]
    rcases fD1_cls t d ht hd (1) (by omega) with ⟨a0, e⟩ | ⟨a0, e⟩ <;>
      first | (exfalso; omega) | ((rw [e]) <;> (try simp only [Blk.pt, Blk.pos, fD1_0, fD1_1]) <;> first | rfl | (congr 1; peq2))
  · refine fD1_deg2 t d ht hd _ ?_
    simp only [min_eq_left (show (4 * t + 2) - 2 ≤ tot (fD1_bs t d) by omega)]
    rcases fD1_cls t d ht hd ((4 * t + 2) - 2) (by omega) with ⟨a0, e⟩ | ⟨a0, e⟩ <;>
      first | (exfalso; omega) | ((rw [e]) <;> (try simp only [Blk.pt, Blk.pos, fD1_0, fD1_1]) <;> first | rfl | (congr 1; peq2))
end Claude5O2
