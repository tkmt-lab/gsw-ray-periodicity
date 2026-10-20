import Formal.Claude5O2SuffT1

/-! O2(1, d): degrees and the literal path (part 2; split from the generated file at a theorem boundary.) -/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000

namespace Claude5O2

open ClaudeChallenge Claude2Aligned

theorem fT1_deg0 (t d : ℕ) (ht : t = 1) (hd : 3 ≤ d) (v : MS (t : ℤ) (d : ℤ)) (hv0 : v.1 = ch (t : ℤ) (d : ℤ) 0 ((0), (0))) : deg (GM (t : ℤ) (d : ℤ)) v = 5 := by
  have ht1 : (1 : ℤ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hv : v.1 = ch (t : ℤ) (d : ℤ) 0 ((0), (0)) := hv0.trans (by first | rfl | (congr 1; peq2))
  refine deg_eq_of v [ch (t : ℤ) (d : ℤ) 0 ((1), (0)), ch (t : ℤ) (d : ℤ) 0 ((0), (1)), ch (t : ℤ) (d : ℤ) 0 ((-1), (1)), ch (t : ℤ) (d : ℤ) 1 ((1), (0)), ch (t : ℤ) (d : ℤ) 1 ((0), (1))] ?_ ?_ ?_ ?_
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_01 (by simp only [ne_eq, Prod.mk.injEq, OnD] <;> omega), ne_01 (by simp only [ne_eq, Prod.mk.injEq, OnD] <;> omega)⟩, ⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_01 (by simp only [ne_eq, Prod.mk.injEq, OnD] <;> omega), ne_01 (by simp only [ne_eq, Prod.mk.injEq, OnD] <;> omega)⟩, ⟨ne_01 (by simp only [ne_eq, Prod.mk.injEq, OnD] <;> omega), ne_01 (by simp only [ne_eq, Prod.mk.injEq, OnD] <;> omega)⟩, ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩
  · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> exact ch_valid ht1 hd1 (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega)
  · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact adj_via ht1 (c := 0) (P := ((0), (0))) (Q := ((1), (0))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 0) (P := ((0), (0))) (Q := ((0), (1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 0) (P := ((0), (0))) (Q := ((-1), (1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 1) (P := ((0), (0))) (Q := ((1), (0))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact tr_ch ht1 hd1 (by norm_num) (tr01 (by peq2) (by simp only [OnD, or_true, true_or] <;> omega))) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 1) (P := ((0), (0))) (Q := ((0), (1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact tr_ch ht1 hd1 (by norm_num) (tr01 (by peq2) (by simp only [OnD, or_true, true_or] <;> omega))) (Eq.symm (by first | rfl | (congr 1; peq2)))
  · intro w hw
    obtain ⟨-, c, hc, z, u, hz, hzu, hu, e1, e2⟩ := hw
    rw [hv] at e1
    have hz0 : Dom (t : ℤ) (d : ℤ) 0 ((0), (0)) := by simp only [Dom, Hx, Rh] <;> omega
    rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩
    · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
      obtain rfl : z = ((0), (0)) := by
        rcases hce with ⟨h1, h2⟩ | h | h
        · exact h2
        · simp [Tr] at h
        · simp [Tr] at h
      rw [unit_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [← e2, show (((0), (0)) : ℤ × ℤ) + (1, 0) = ((1), (0)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inl (by first | rfl | (congr 1; peq2))
      · rw [← e2, show (((0), (0)) : ℤ × ℤ) + (0, 1) = ((0), (1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inl (by first | rfl | (congr 1; peq2)))
      · rw [← e2, show (((0), (0)) : ℤ × ℤ) + (-1, 1) = ((-1), (1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2))))
      · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
      · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
      · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
    · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
      obtain rfl : z = ((0), (0)) := by
        rcases hce with ⟨h1, h2⟩ | h | h
        · simp at h1
        · simp [Tr] at h
        · obtain ⟨h1, h2⟩ := h; rw [h1]
      rw [unit_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [← e2, show (((0), (0)) : ℤ × ℤ) + (1, 0) = ((1), (0)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2)))))
      · rw [← e2, show (((0), (0)) : ℤ × ℤ) + (0, 1) = ((0), (1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inr ((by first | rfl | (congr 1; peq2))))))
      · rw [← e2, show (((0), (0)) : ℤ × ℤ) + (-1, 1) = ((-1), (1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inl (Eq.symm (tr_ch ht1 hd1 (by norm_num) (tr01 (by peq2) (by simp only [OnD, or_true, true_or] <;> omega))))))
      · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
      · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
      · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
    · have hi : i < 3 := by omega
      interval_cases i
      · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
        obtain rfl : z = ((0), (0)) := by
          rcases hce with ⟨h1, h2⟩ | h | h
          · simp at h1
          · simp [Tr] at h
          · obtain ⟨l, h0, h1, h2, h3⟩ := h; rw [h3]; simp only [sp, Prod.ext_iff] at h2 ⊢ <;> omega
        rw [unit_iff] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [← e2, show (((0), (0)) : ℤ × ℤ) + (1, 0) = ((1), (0)) by peq2]
          simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inl (Eq.symm (tr_ch ht1 hd1 (by norm_num) (tr1R (1) (by omega) (by omega) (by peq2) (by peq2)))))))
        · rw [← e2, show (((0), (0)) : ℤ × ℤ) + (0, 1) = ((0), (1)) by peq2]
          simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inl (Eq.symm (tr_ch ht1 hd1 (by norm_num) (tr0R (1) (by omega) (by omega) (by peq2) (by peq2))))
        · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
        · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
        · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
        · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
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
theorem fT1_deg1 (t d : ℕ) (ht : t = 1) (hd : 3 ≤ d) (v : MS (t : ℤ) (d : ℤ)) (hv0 : v.1 = ch (t : ℤ) (d : ℤ) 0 ((0), (1))) : deg (GM (t : ℤ) (d : ℤ)) v = 6 := by
  have ht1 : (1 : ℤ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hv : v.1 = ch (t : ℤ) (d : ℤ) 0 ((0), (1)) := hv0.trans (by first | rfl | (congr 1; peq2))
  refine deg_eq_of v [ch (t : ℤ) (d : ℤ) 0 ((1), (1)), ch (t : ℤ) (d : ℤ) 0 ((0), (2)), ch (t : ℤ) (d : ℤ) 0 ((-1), (2)), ch (t : ℤ) (d : ℤ) 0 ((-1), (1)), ch (t : ℤ) (d : ℤ) 0 ((0), (0)), ch (t : ℤ) (d : ℤ) 0 ((1), (0))] ?_ ?_ ?_ ?_
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩, ⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩, ⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩, ⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩, ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩
  · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ch_valid ht1 hd1 (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega)
  · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact adj_via ht1 (c := 0) (P := ((0), (1))) (Q := ((1), (1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 0) (P := ((0), (1))) (Q := ((0), (2))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 0) (P := ((0), (1))) (Q := ((-1), (2))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 0) (P := ((0), (1))) (Q := ((-1), (1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 0) (P := ((0), (1))) (Q := ((0), (0))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 0) (P := ((0), (1))) (Q := ((1), (0))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
  · intro w hw
    obtain ⟨-, c, hc, z, u, hz, hzu, hu, e1, e2⟩ := hw
    rw [hv] at e1
    have hz0 : Dom (t : ℤ) (d : ℤ) 0 ((0), (1)) := by simp only [Dom, Hx, Rh] <;> omega
    rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩
    · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
      obtain rfl : z = ((0), (1)) := by
        rcases hce with ⟨h1, h2⟩ | h | h
        · exact h2
        · simp [Tr] at h
        · simp [Tr] at h
      rw [unit_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [← e2, show (((0), (1)) : ℤ × ℤ) + (1, 0) = ((1), (1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inl (by first | rfl | (congr 1; peq2))
      · rw [← e2, show (((0), (1)) : ℤ × ℤ) + (0, 1) = ((0), (2)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inl (by first | rfl | (congr 1; peq2)))
      · rw [← e2, show (((0), (1)) : ℤ × ℤ) + (-1, 1) = ((-1), (2)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2))))
      · rw [← e2, show (((0), (1)) : ℤ × ℤ) + (-1, 0) = ((-1), (1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2)))))
      · rw [← e2, show (((0), (1)) : ℤ × ℤ) + (0, -1) = ((0), (0)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2))))))
      · rw [← e2, show (((0), (1)) : ℤ × ℤ) + (1, -1) = ((1), (0)) by peq2]
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
theorem fT1_deg2 (t d : ℕ) (ht : t = 1) (hd : 3 ≤ d) (v : MS (t : ℤ) (d : ℤ)) (hv0 : v.1 = ch (t : ℤ) (d : ℤ) 1 ((0), ((d : ℤ) + 1))) : deg (GM (t : ℤ) (d : ℤ)) v = 6 := by
  have ht1 : (1 : ℤ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hv : v.1 = ch (t : ℤ) (d : ℤ) 1 ((0), ((d : ℤ) + 1)) := hv0.trans (by first | rfl | (congr 1; peq2))
  refine deg_eq_of v [ch (t : ℤ) (d : ℤ) 1 ((1), ((d : ℤ) + 1)), ch (t : ℤ) (d : ℤ) 1 ((0), ((d : ℤ) + 2)), ch (t : ℤ) (d : ℤ) 1 ((-1), ((d : ℤ) + 2)), ch (t : ℤ) (d : ℤ) 1 ((-1), ((d : ℤ) + 1)), ch (t : ℤ) (d : ℤ) 1 ((0), ((d : ℤ))), ch (t : ℤ) (d : ℤ) 1 ((1), ((d : ℤ)))] ?_ ?_ ?_ ?_
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩, ⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩, ⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩, ⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩, ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩
  · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ch_valid ht1 hd1 (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega)
  · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact adj_via ht1 (c := 1) (P := ((0), ((d : ℤ) + 1))) (Q := ((1), ((d : ℤ) + 1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 1) (P := ((0), ((d : ℤ) + 1))) (Q := ((0), ((d : ℤ) + 2))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 1) (P := ((0), ((d : ℤ) + 1))) (Q := ((-1), ((d : ℤ) + 2))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 1) (P := ((0), ((d : ℤ) + 1))) (Q := ((-1), ((d : ℤ) + 1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 1) (P := ((0), ((d : ℤ) + 1))) (Q := ((0), ((d : ℤ)))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 1) (P := ((0), ((d : ℤ) + 1))) (Q := ((1), ((d : ℤ)))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
  · intro w hw
    obtain ⟨-, c, hc, z, u, hz, hzu, hu, e1, e2⟩ := hw
    rw [hv] at e1
    have hz0 : Dom (t : ℤ) (d : ℤ) 1 ((0), ((d : ℤ) + 1)) := by simp only [Dom, Hx, Rh] <;> omega
    rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩
    · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
      exfalso
      rcases hce with ⟨h1, h2⟩ | h | h
      · simp at h1
      · obtain ⟨h1, h2⟩ := h; simp only [Prod.ext_iff, OnD] at h1 h2 <;> omega
      · simp [Tr] at h
    · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
      obtain rfl : z = ((0), ((d : ℤ) + 1)) := by
        rcases hce with ⟨h1, h2⟩ | h | h
        · exact h2
        · simp [Tr] at h
        · simp [Tr] at h
      rw [unit_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [← e2, show (((0), ((d : ℤ) + 1)) : ℤ × ℤ) + (1, 0) = ((1), ((d : ℤ) + 1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inl (by first | rfl | (congr 1; peq2))
      · rw [← e2, show (((0), ((d : ℤ) + 1)) : ℤ × ℤ) + (0, 1) = ((0), ((d : ℤ) + 2)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inl (by first | rfl | (congr 1; peq2)))
      · rw [← e2, show (((0), ((d : ℤ) + 1)) : ℤ × ℤ) + (-1, 1) = ((-1), ((d : ℤ) + 2)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2))))
      · rw [← e2, show (((0), ((d : ℤ) + 1)) : ℤ × ℤ) + (-1, 0) = ((-1), ((d : ℤ) + 1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2)))))
      · rw [← e2, show (((0), ((d : ℤ) + 1)) : ℤ × ℤ) + (0, -1) = ((0), ((d : ℤ))) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2))))))
      · rw [← e2, show (((0), ((d : ℤ) + 1)) : ℤ × ℤ) + (1, -1) = ((1), ((d : ℤ))) by peq2]
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
theorem fT1_deg3 (t d : ℕ) (ht : t = 1) (hd : 3 ≤ d) (v : MS (t : ℤ) (d : ℤ)) (hv0 : v.1 = ch (t : ℤ) (d : ℤ) 1 ((0), ((d : ℤ) + 2))) : deg (GM (t : ℤ) (d : ℤ)) v = 5 := by
  have ht1 : (1 : ℤ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hv : v.1 = ch (t : ℤ) (d : ℤ) 0 ((0), ((d : ℤ) + 2)) := hv0.trans (Eq.symm (tr_ch ht1 hd1 (by norm_num) (tr01 (by peq2) (by simp only [OnD, or_true, true_or] <;> omega))))
  refine deg_eq_of v [ch (t : ℤ) (d : ℤ) 0 ((-1), ((d : ℤ) + 2)), ch (t : ℤ) (d : ℤ) 0 ((0), ((d : ℤ) + 1)), ch (t : ℤ) (d : ℤ) 0 ((1), ((d : ℤ) + 1)), ch (t : ℤ) (d : ℤ) 1 ((0), ((d : ℤ) + 1)), ch (t : ℤ) (d : ℤ) 1 ((1), ((d : ℤ) + 1))] ?_ ?_ ?_ ?_
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_01 (by simp only [ne_eq, Prod.mk.injEq, OnD] <;> omega), ne_01 (by simp only [ne_eq, Prod.mk.injEq, OnD] <;> omega)⟩, ⟨ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega), ne_01 (by simp only [ne_eq, Prod.mk.injEq, OnD] <;> omega), ne_01 (by simp only [ne_eq, Prod.mk.injEq, OnD] <;> omega)⟩, ⟨ne_01 (by simp only [ne_eq, Prod.mk.injEq, OnD] <;> omega), ne_01 (by simp only [ne_eq, Prod.mk.injEq, OnD] <;> omega)⟩, ne_same ht1 (by norm_num) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [Dom, Hx, Rh, true_and, and_true] <;> omega) (by simp only [ne_eq, Prod.mk.injEq] <;> omega)⟩
  · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> exact ch_valid ht1 hd1 (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega)
  · intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact adj_via ht1 (c := 0) (P := ((0), ((d : ℤ) + 2))) (Q := ((-1), ((d : ℤ) + 2))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 0) (P := ((0), ((d : ℤ) + 2))) (Q := ((0), ((d : ℤ) + 1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 0) (P := ((0), ((d : ℤ) + 2))) (Q := ((1), ((d : ℤ) + 1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact by first | rfl | (congr 1; peq2)) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 1) (P := ((0), ((d : ℤ) + 2))) (Q := ((0), ((d : ℤ) + 1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact tr_ch ht1 hd1 (by norm_num) (tr01 (by peq2) (by simp only [OnD, or_true, true_or] <;> omega))) (Eq.symm (by first | rfl | (congr 1; peq2)))
    · exact adj_via ht1 (c := 1) (P := ((0), ((d : ℤ) + 2))) (Q := ((1), ((d : ℤ) + 1))) (by norm_num) (by simp only [Dom, Hx, Rh] <;> omega) (by simp only [Dom, Hx, Rh] <;> omega) (by rw [unit_sub]; simp only [U2] <;> omega) (by rw [hv] <;> exact tr_ch ht1 hd1 (by norm_num) (tr01 (by peq2) (by simp only [OnD, or_true, true_or] <;> omega))) (Eq.symm (by first | rfl | (congr 1; peq2)))
  · intro w hw
    obtain ⟨-, c, hc, z, u, hz, hzu, hu, e1, e2⟩ := hw
    rw [hv] at e1
    have hz0 : Dom (t : ℤ) (d : ℤ) 0 ((0), ((d : ℤ) + 2)) := by simp only [Dom, Hx, Rh] <;> omega
    rcases c_cases (c := c) with rfl | rfl | ⟨i, rfl⟩
    · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
      obtain rfl : z = ((0), ((d : ℤ) + 2)) := by
        rcases hce with ⟨h1, h2⟩ | h | h
        · exact h2
        · simp [Tr] at h
        · simp [Tr] at h
      rw [unit_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
      · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
      · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
      · rw [← e2, show (((0), ((d : ℤ) + 2)) : ℤ × ℤ) + (-1, 0) = ((-1), ((d : ℤ) + 2)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inl (by first | rfl | (congr 1; peq2))
      · rw [← e2, show (((0), ((d : ℤ) + 2)) : ℤ × ℤ) + (0, -1) = ((0), ((d : ℤ) + 1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inl (by first | rfl | (congr 1; peq2)))
      · rw [← e2, show (((0), ((d : ℤ) + 2)) : ℤ × ℤ) + (1, -1) = ((1), ((d : ℤ) + 1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2))))
    · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
      obtain rfl : z = ((0), ((d : ℤ) + 2)) := by
        rcases hce with ⟨h1, h2⟩ | h | h
        · simp at h1
        · simp [Tr] at h
        · obtain ⟨h1, h2⟩ := h; rw [h1]
      rw [unit_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
      · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
      · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
      · rw [← e2, show (((0), ((d : ℤ) + 2)) : ℤ × ℤ) + (-1, 0) = ((-1), ((d : ℤ) + 2)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inl (Eq.symm (tr_ch ht1 hd1 (by norm_num) (tr01 (by peq2) (by simp only [OnD, or_true, true_or] <;> omega))))
      · rw [← e2, show (((0), ((d : ℤ) + 2)) : ℤ × ℤ) + (0, -1) = ((0), ((d : ℤ) + 1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inl (by first | rfl | (congr 1; peq2)))))
      · rw [← e2, show (((0), ((d : ℤ) + 2)) : ℤ × ℤ) + (1, -1) = ((1), ((d : ℤ) + 1)) by peq2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inr ((by first | rfl | (congr 1; peq2))))))
    · have hi : i < 3 := by omega
      interval_cases i
      · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
        exfalso
        rcases hce with ⟨h1, h2⟩ | h | h
        · simp at h1
        · simp [Tr] at h
        · obtain ⟨l, h0, h1, h2, h3⟩ := h; simp only [sp, Prod.ext_iff] at h2 h3 <;> omega
      · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
        obtain rfl : z = ((1), (1)) := by
          rcases hce with ⟨h1, h2⟩ | h | h
          · simp at h1
          · simp [Tr] at h
          · obtain ⟨l, h0, h1, h2, h3⟩ := h; rw [h3]; simp only [sp, Prod.ext_iff] at h2 ⊢ <;> omega
        rw [unit_iff] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
        · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
        · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
        · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
        · rw [← e2, show (((1), (1)) : ℤ × ℤ) + (-1, 0) = ((0), (1)) by peq2]
          simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inl (Eq.symm (tr_ch ht1 hd1 (by norm_num) (tr0R (1) (by omega) (by omega) (by peq2) (by peq2))))))
        · rw [← e2, show (((1), (1)) : ℤ × ℤ) + (0, -1) = ((1), (0)) by peq2]
          simp only [List.mem_cons, List.not_mem_nil, or_false] <;> exact Or.inr (Or.inr (Or.inr (Or.inr ((Eq.symm (tr_ch ht1 hd1 (by norm_num) (tr1R (1) (by omega) (by omega) (by peq2) (by peq2))))))))
        · exfalso; simp only [Dom, Hx, Rh, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] at hzu <;> omega
      · have hce := ch_eq ht1 hd1 (by norm_num) (by norm_num) hz hz0 e1
        exfalso
        rcases hce with ⟨h1, h2⟩ | h | h
        · simp at h1
        · simp [Tr] at h
        · obtain ⟨l, h0, h1, h2, h3⟩ := h; simp only [sp, Prod.ext_iff] at h2 h3 <;> omega
theorem fT1_lit (t d : ℕ) (ht : t = 1) (hd : 3 ≤ d) : ∃ n p, LiteralPath (GM (t : ℤ) (d : ℤ)) n p := by
  have ht1 : (1 : ℤ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hS := strip_of_chain _ (fT1_chain t d ht hd)
  have hN : tot (fT1_bs t d) = (4 * d + 4) := by simp [fT1_bs, tot, fT1_0, fT1_1, fT1_2] <;> omega
  refine ⟨(4 * d + 4), fun k => ⟨wk (t : ℤ) (d : ℤ) (fT1_bs t d) (min k (tot (fT1_bs t d))), hS.1 _ (min_le_right _ _)⟩, ?_⟩
  refine literal_of_strip hS (by omega) (by omega) ⟨(2 * d + 2), by ring⟩ (fT1_inj t d ht hd) _ (fun k hk => by simp only [min_eq_left hk]) ?_ ?_ ?_ ?_
  · refine fT1_deg0 t d ht hd _ ?_
    simp only [min_eq_left (show 0 ≤ tot (fT1_bs t d) by omega)]
    rcases fT1_cls t d ht hd (0) (by omega) with ⟨a0, e⟩ | ⟨a0, a1, e⟩ | ⟨a0, e⟩ <;>
      first | (exfalso; omega) | ((rw [e]) <;> (try simp only [Blk.pt, Blk.pos, fT1_0, fT1_1, fT1_2]) <;> first | rfl | (congr 1; peq2))
  · refine fT1_deg3 t d ht hd _ ?_
    simp only [min_eq_left (show (4 * d + 4) - 1 ≤ tot (fT1_bs t d) by omega)]
    rcases fT1_cls t d ht hd ((4 * d + 4) - 1) (by omega) with ⟨a0, e⟩ | ⟨a0, a1, e⟩ | ⟨a0, e⟩ <;>
      first | (exfalso; omega) | ((rw [e]) <;> (try simp only [Blk.pt, Blk.pos, fT1_0, fT1_1, fT1_2]) <;> first | rfl | (congr 1; peq2))
  · refine fT1_deg1 t d ht hd _ ?_
    simp only [min_eq_left (show 1 ≤ tot (fT1_bs t d) by omega)]
    rcases fT1_cls t d ht hd (1) (by omega) with ⟨a0, e⟩ | ⟨a0, a1, e⟩ | ⟨a0, e⟩ <;>
      first | (exfalso; omega) | ((rw [e]) <;> (try simp only [Blk.pt, Blk.pos, fT1_0, fT1_1, fT1_2]) <;> first | rfl | (congr 1; peq2))
  · refine fT1_deg2 t d ht hd _ ?_
    simp only [min_eq_left (show (4 * d + 4) - 2 ≤ tot (fT1_bs t d) by omega)]
    rcases fT1_cls t d ht hd ((4 * d + 4) - 2) (by omega) with ⟨a0, e⟩ | ⟨a0, a1, e⟩ | ⟨a0, e⟩ <;>
      first | (exfalso; omega) | ((rw [e]) <;> (try simp only [Blk.pt, Blk.pos, fT1_0, fT1_1, fT1_2]) <;> first | rfl | (congr 1; peq2))
end Claude5O2
