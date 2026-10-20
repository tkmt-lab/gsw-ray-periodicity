import Formal.Claude3StateBack

/-!
# Theorem 1a, G5 (⇐), part 2: the conditions give a chain of passages

Written by a Claude worker (2026-10-20, Theorem 1a, parts G4/G5).

* `chain_of_condCore` : from a set `X` of states at `t` satisfying `CondCore` (conditions 1,
  3, 4 and the passage condition; condition 3 in its full-tail form gives disjoint outputs,
  since transitions inside the chain are consecutive) we extract a chain
  `a = σ 0 → σ 1 → … → σ r = b` of distinct states of `X`. Paper: "a reached cycle would
  create an extra incoming edge"; the chain from `a` cannot repeat a state, by the unique
  predecessors, so in the finite set `X` it reaches `b`. Connectivity (condition 2) is not
  needed for this direction.
* `pathExists_of_condCore`, `pathExists_of_cond` : **(⇐)** of the reduction theorem.
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo

variable {S : Sig} {t : ℕ}

theorem chain_of_condCore (hV : Valid S t) {X : Set (PState S)}
    (hX : X ⊆ R002.Claude3Fold.St stLo stHi t)
    (hC : CondCore t X) : ∃ C : Chain S t, ∀ j, j ≤ C.r → C.σ j ∈ X := by
  classical
  obtain ⟨hP, ⟨a, ha, b, hb, har, hbt, -, htb, hsucc, hpred⟩, ⟨hD1, hD2, hD3⟩,
    ⟨hE1, hE2, hE3, hE4, hE5, hE6⟩⟩ := hC
  have hfin : X.Finite := (St_finite t).subset hX
  let nxt : PState S → PState S := fun x =>
    if h : x ∈ X ∧ x.1.term = none then (hsucc x h.1 h.2).choose else x
  have nxt_spec : ∀ x ∈ X, x.1.term = none → nxt x ∈ X ∧ Trans t x (nxt x) := by
    intro x hx hxt
    have h : x ∈ X ∧ x.1.term = none := ⟨hx, hxt⟩
    simp only [nxt, h, and_self, ↓reduceDIte]
    exact ⟨(hsucc x hx hxt).choose_spec.1, (hsucc x hx hxt).choose_spec.2.1⟩
  let sq : ℕ → PState S := fun j => nxt^[j] a
  have sq_succ : ∀ j, sq (j + 1) = nxt (sq j) := fun j => Function.iterate_succ_apply' nxt j a
  have sq_zero : sq 0 = a := rfl
  have sq_mem : ∀ j, sq j ∈ X := by
    intro j
    induction j with
    | zero => exact ha
    | succ j ih =>
      rw [sq_succ]
      by_cases h : (sq j).1.term = none
      · exact (nxt_spec _ ih h).1
      · simp only [nxt, h, and_false, ↓reduceDIte]
        exact ih
  have sq_trans : ∀ j, sq j ≠ b → Trans t (sq j) (sq (j + 1)) := by
    intro j hj
    rw [sq_succ]
    have : (sq j).1.term = none := by
      by_contra h
      exact hj (htb _ (sq_mem j) h)
    exact (nxt_spec _ (sq_mem j) this).2
  have inj : ∀ L, (∀ m, m < L → sq m ≠ b) → ∀ j l, j < l → l ≤ L → sq j ≠ sq l := by
    intro L hL j
    induction j with
    | zero =>
      intro l hl hlL e
      obtain ⟨i, hi⟩ := sq_trans (l - 1) (hL _ (by omega))
      rw [show l - 1 + 1 = l by omega, ← e, sq_zero] at hi
      exact har hi.2.1
    | succ j ih =>
      intro l hl hlL e
      obtain ⟨i, hi⟩ := sq_trans j (hL j (by omega))
      have t2 := sq_trans (l - 1) (hL _ (by omega))
      rw [show l - 1 + 1 = l by omega, ← e] at t2
      obtain ⟨x, -, -, huniq⟩ := hpred _ (sq_mem (j + 1)) hi.2.1
      have e1 := huniq _ (sq_mem j) ⟨i, hi⟩
      have e2 := huniq _ (sq_mem (l - 1)) t2
      exact ih (l - 1) (by omega) (by omega) (e1.trans e2.symm)
  have hex : ∃ r, sq r = b := by
    by_contra hne
    push Not at hne
    have hinj : Function.Injective sq := by
      intro j l e
      by_contra hjl
      rcases Nat.lt_or_gt_of_ne hjl with h | h
      · exact inj l (fun m _ => hne m) j l h le_rfl e
      · exact inj j (fun m _ => hne m) l j h le_rfl e.symm
    exact Set.infinite_of_injective_forall_mem hinj sq_mem hfin
  let r := Nat.find hex
  have hr : sq r = b := Nat.find_spec hex
  have hrmin : ∀ m, m < r → sq m ≠ b := fun m hm => Nat.find_min hex hm
  have sinj : ∀ j l, j ≤ r → l ≤ r → j ≠ l → sq j ≠ sq l := by
    intro j l hj hl hjl
    rcases Nat.lt_or_gt_of_ne hjl with h | h
    · exact inj r hrmin j l h hl
    · exact fun e => inj r hrmin l j h hj e.symm
  obtain ⟨i₀, e₀, hent₀, hpass₀⟩ := hP a ha
  have hroot₀ : RootAt t a i₀ :=
    hent₀.resolve_right (by rintro ⟨x, -, hx⟩; exact har hx.2.1)
  let ent : ℕ → ℤ := fun j => match j with
    | 0 => i₀
    | j + 1 => if h : Trans t (sq j) (sq (j + 1)) then h.choose else 0
  have ent_succ : ∀ j, j < r → TransAt t (sq j) (sq (j + 1)) (ent (j + 1)) := by
    intro j hj
    have h := sq_trans j (hrmin j hj)
    simp only [ent, h, ↓reduceDIte]
    exact h.choose_spec
  let ext : ℕ → ℤ := fun j => if h : ∃ e, PassOK t (sq j) (ent j) e then h.choose else 0
  have hpass : ∀ j, j ≤ r → PassOK t (sq j) (ent j) (ext j) := by
    intro j hj
    have h : ∃ e, PassOK t (sq j) (ent j) e := by
      cases j with
      | zero => exact ⟨e₀, hpass₀⟩
      | succ j => exact (ent_succ j (by omega)).2.2.1
    simp only [ext, h, ↓reduceDIte]
    exact h.choose_spec
  have hentry : ∀ j, j ≤ r → PassIn t X (sq j) (ent j) (ext j) := by
    intro j hj
    refine ⟨sq_mem j, ?_, hpass j hj⟩
    cases j with
    | zero => exact Or.inl hroot₀
    | succ j => exact Or.inr ⟨sq j, sq_mem j, ent_succ j (by omega)⟩
  have hbr : (sq r).1.term ≠ none := by rw [hr]; exact hbt
  -- transitions inside the chain are consecutive
  have noTrans : ∀ j l, j ≤ r → l ≤ r → Trans t (sq j) (sq l) → l = j + 1 := by
    intro j l hj hl ⟨i, hi⟩
    have hjr : j < r := by
      refine lt_of_le_of_ne hj fun e => ?_
      rw [e] at hi
      exact hbr hi.1
    obtain ⟨y₀, -, -, huniq⟩ := hsucc (sq j) (sq_mem j) hi.1
    have e1 := huniq _ (sq_mem l) ⟨i, hi⟩
    have e2 := huniq _ (sq_mem (j + 1)) (sq_trans j (hrmin j hjr))
    by_contra hne
    exact sinj l (j + 1) hl hjr hne (e1.trans e2.symm)
  -- own starts and the output inside the full tail
  have hown : ∀ j, j ≤ r → ∃ s, OwnStart t (sq j) s ∧ s ≤ ent j := by
    intro j hj
    cases j with
    | zero => exact ⟨ent 0, Or.inr hroot₀, le_rfl⟩
    | succ j =>
      exact ⟨_, Or.inl ⟨(ent_succ j (by omega)).2.1, rfl⟩, (hpass _ hj).2.1⟩
  have tail : ∀ j, j ≤ r → ∀ s, s ≤ ent j → ∀ v, OutV t (sq j) (ent j) (ext j) v →
      OutV t (sq j) s (ext j) v := by
    rintro j - s hs v ⟨a, h1, h2, h3⟩
    exact ⟨a, by omega, h2, h3⟩
  have hexit : ∀ j, j ≤ r → ExitAt t (sq j) (ext j) := fun j hj => (hpass j hj).2.2.2.2
  have hdisj : ∀ j l, j ≤ r → l ≤ r → j ≠ l → ∀ v, OutV t (sq j) (ent j) (ext j) v →
      ¬ OutV t (sq l) (ent l) (ext l) v := by
    intro j l hj hl hjl v hv hv'
    obtain ⟨s, hs, hsle⟩ := hown j hj
    obtain ⟨s', hs', hsle'⟩ := hown l hl
    by_cases h1 : l = j + 1
    · subst h1
      exact hD2 _ _ _ _ _ _ (sq_mem j) (sq_mem _) hs (hexit j hj) (ent_succ j hl) (hexit _ hl)
        v hv' (tail j hj s hsle v hv)
    by_cases h2 : j = l + 1
    · subst h2
      exact hD2 _ _ _ _ _ _ (sq_mem l) (sq_mem _) hs' (hexit l hl) (ent_succ l hj) (hexit _ hj)
        v hv (tail l hl s' hsle' v hv')
    exact hD1 _ _ _ _ _ _ (sq_mem j) (sq_mem l) hs (hexit j hj) hs' (hexit l hl)
      (sinj j l hj hl hjl) (fun h => h1 (noTrans j l hj hl h))
      (fun h => h2 (noTrans l j hl hj h)) v (tail j hj s hsle v hv) (tail l hl s' hsle' v hv')
  have hsaved : ∀ l, l ≤ r → ∀ v, (RV t (sq 0) (ent 0) v ∨ RV t (sq 0) (ent 0 + 1) v) →
      ¬ OutV t (sq l) (ent l) (ext l) v := by
    intro l hl v hv hout
    by_cases hl0 : l = 0
    · subst hl0
      obtain ⟨a, h1, -, h3⟩ := hout
      rcases hv with hv | hv
      · have := hv.inj hV h3; omega
      · have := hv.inj hV h3; omega
    · obtain ⟨s', hs', hsle'⟩ := hown l hl
      exact hD3 _ _ _ _ _ (sq_mem 0) (sq_mem l) hroot₀
        (sinj l 0 hl (Nat.zero_le _) hl0) hs' (hexit l hl) v hv (tail l hl s' hsle' v hout)
  let C : Chain S t :=
    { r := r
      σ := sq
      ent := ent
      ext := ext
      pass := hpass
      trans := ent_succ
      disj := hdisj
      saved := hsaved
      deg0 := (hE1 a ha i₀ hroot₀).1
      deg1 := (hE1 a ha i₀ hroot₀).2
      degN := (hE2 _ _ _ (hentry r le_rfl) hbr).1
      degN1 := (hE2 _ _ _ (hentry r le_rfl) hbr).2
      par0 := hE3 a ha har
      parS := fun j hj => hE4 _ _ _ _ _ (hentry j hj.le) (sq_mem (j + 1)) (ent_succ j hj)
      parN := hE5 _ _ _ (hentry r le_rfl) hbr
      size := fun h0 => by
        have hb0 : sq 0 = b := by
          have := hr
          rw [h0] at this
          exact this
        exact hE6 _ _ _ (hentry 0 (Nat.zero_le _)) har (by rw [hb0]; exact hbt) }
  exact ⟨C, fun j _ => sq_mem j⟩

/-- **(⇐) of the reduction theorem**, from the conditions without connectivity. -/
theorem pathExists_of_condCore (hV : Valid S t) {X : Set (PState S)}
    (hX : X ⊆ R002.Claude3Fold.St stLo stHi t) (hC : CondCore t X) : PathExists S t := by
  obtain ⟨C, -⟩ := chain_of_condCore hV hX hC
  exact C.pathExists hV

theorem Cond.core {X : Set (PState S)} (h : Cond t X) : CondCore t X :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- **(⇐) of the reduction theorem.** -/
theorem pathExists_of_cond (hV : Valid S t) {X : Set (PState S)}
    (hX : X ⊆ R002.Claude3Fold.St stLo stHi t) (hC : Cond t X) : PathExists S t :=
  pathExists_of_condCore hV hX hC.core

end ClaudeChallenge2.State
