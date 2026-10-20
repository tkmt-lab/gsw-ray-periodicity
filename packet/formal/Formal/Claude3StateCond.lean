import Formal.Claude3StateHit

/-!
# Theorem 1a, G5 (⇒), part 3: the states of a literal path satisfy the four conditions

Written by a Claude worker (2026-10-20, Theorem 1a, parts G4/G5).

`Sup S t` bundles a literal path `p` of length `n`, its greedy maximal-reach decomposition `D`,
and the marked corners `m0`, `m1` at its two ends. The state of passage `j` is `st j`: the chart,
direction and height of the row of `D`, root data `m0` for `j = 0`, terminal data `m1` for
`j = r`, and count parity `pos j mod 2` (vertices before its output: `pos j + 2`). Its entry is
`D.i j`, its exit `ex j = D.i j + D.M j - 2`. The state set is `X = {st j | j ≤ r}`.

* `passOK`, `rootAt`, `transAt` : the passages are valid and consecutive states are linked by the
  generic transition;
* `trans_inv` : conversely every transition between states of `X` is `st j → st (j+1)` with the
  actual entry (from `Decomp.row_hit`);
* `st_inj`, `passIn_eq`, `out_pos` : the states are distinct, every passage of `X` is an actual
  one, and its output is a block of path positions;
* `cond` : **`X` lies in the state domain and satisfies `Cond`** (paper: "Hence the selected
  states satisfy all four conditions");
* `cond_of_pathExists` : **(⇒) of the reduction theorem**.
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo

variable {S : Sig} {t : ℕ}

/-- A literal path with its decomposition and end corners. -/
structure Sup (S : Sig) (t : ℕ) where
  n : ℕ
  p : ℕ → Vertex S t
  hp : LiteralPath (graph S t) n p
  D : Decomp p n
  m0 : Fin S.M
  m1 : Fin S.M
  hm0 : CornerV t m0 (p 0)
  hm1 : CornerV t m1 (p (n - 1))

theorem exists_flip (P : ℕ → Prop) {j : ℕ} (hj : P j) :
    ∀ d, ¬ P (j + d) → ∃ m, j ≤ m ∧ m < j + d ∧ P m ∧ ¬ P (m + 1) := by
  intro d
  induction d with
  | zero => intro h; exact absurd hj h
  | succ d ih =>
    intro h
    by_cases hd : P (j + d)
    · exact ⟨j + d, by omega, by omega, hd, by simpa [Nat.add_assoc] using h⟩
    · obtain ⟨m, h1, h2, h3, h4⟩ := ih hd
      exact ⟨m, h1, by omega, h3, h4⟩

namespace Sup

variable (U : Sup S t)

/-- The state of passage `j`. -/
def st (j : ℕ) : PState S :=
  (⟨(U.D.c j).1.f, (U.D.c j).1.k, if j = 0 then some U.m0 else none,
    if j = U.D.r then some U.m1 else none, decide (U.D.pos j % 2 = 1)⟩, (U.D.c j).2)

/-- The exit index of passage `j`. -/
def ex (j : ℕ) : ℤ := U.D.i j + U.D.M j - 2

/-- The state set of the path. -/
def X : Set (PState S) := {y | ∃ j, j ≤ U.D.r ∧ U.st j = y}

theorem root_none_iff (j : ℕ) : (U.st j).1.root = none ↔ j ≠ 0 := by
  simp [st]

theorem term_none_iff (j : ℕ) : (U.st j).1.term = none ↔ j ≠ U.D.r := by
  simp [st]

theorem rv_path {j : ℕ} (hj : j ≤ U.D.r) {d : ℕ} (hd : d ≤ U.D.M j) :
    RV t (U.st j) (U.D.i j + d) (U.p (U.D.pos j + d)) := U.D.fol hj d hd

theorem passOK (hV : Valid S t) {j : ℕ} (hj : j ≤ U.D.r) :
    PassOK t (U.st j) (U.D.i j) (U.ex j) := by
  obtain ⟨hr, hlo, hhi, hex⟩ := exit_of_max U.hp hV (U.D.max j hj)
  have hM := U.D.two hj
  refine ⟨hr, hlo, by unfold ex; omega, by unfold ex; exact hhi, ?_, ?_⟩
  · intro h
    have hjr : j < U.D.r := lt_of_le_of_ne hj ((U.term_none_iff j).1 h)
    have := U.D.notlast j hjr
    exact hex (by omega)
  · intro m hm
    have hjr : j = U.D.r := by
      by_contra hne
      rw [(U.term_none_iff j).2 hne] at hm
      cases hm
    have hmm : m = U.m1 := by
      simp only [st, hjr, ite_true, Option.some.injEq] at hm
      exact hm.symm
    subst hmm hjr
    refine ⟨U.p (U.n - 1), ?_, U.hm1⟩
    exact (U.rv_path hj le_rfl).pcongr (by unfold ex; ring) U.D.last

theorem rootAt : RootAt t (U.st 0) (U.D.i 0) :=
  ⟨U.m0, by simp [st], U.p 0,
    (U.rv_path (Nat.zero_le _) (Nat.zero_le _)).pcongr (by simp) (by simp [U.D.pos0]), U.hm0⟩

theorem hiS_eq (hV : Valid S t) {j : ℕ} (hj : j < U.D.r) :
    hiS t (U.st j) = U.D.i j + U.D.M j - 2 :=
  ((U.passOK hV hj.le).2.2.2.2.1 ((U.term_none_iff j).2 hj.ne)).symm

theorem transAt (hV : Valid S t) {j : ℕ} (hj : j < U.D.r) :
    TransAt t (U.st j) (U.st (j + 1)) (U.D.i (j + 1)) := by
  have hM := U.D.two hj.le
  have hM' := U.D.two (j := j + 1) hj
  have hb' := U.D.bound (j := j + 1) hj
  have hnext := U.D.next j hj
  have hhi := U.hiS_eq hV hj
  refine ⟨(U.term_none_iff j).2 hj.ne, (U.root_none_iff _).2 (Nat.succ_ne_zero j),
    ⟨_, U.passOK hV hj⟩, ⟨U.p (U.D.pos (j + 1)), ?_, ?_⟩, ⟨U.p (U.D.pos (j + 1) + 1), ?_, ?_⟩, ?_⟩
  · exact (U.rv_path (j := j + 1) hj (Nat.zero_le _)).pcongr (by simp) (by simp)
  · rw [hhi]
    exact (U.rv_path hj.le (d := U.D.M j - 1) (by omega)).pcongr (by omega)
      (by omega)
  · exact (U.rv_path (j := j + 1) hj (d := 1) (by omega)).pcongr (by simp) rfl
  · rw [hhi]
    exact (U.rv_path hj.le (d := U.D.M j) le_rfl).pcongr (by ring) (by omega)
  · intro v w hv hw hvw
    rw [hhi] at hw
    have e1 := hv.unique ((U.rv_path (j := j + 1) hj (d := 2) hM').pcongr (by simp) rfl)
    have e2 := hw.unique ((U.rv_path hj.le (d := U.D.M j - 2) (by omega)).pcongr
      (by omega) rfl)
    have := lp_inj U.hp (by omega) (by omega) (e1.symm.trans (hvw.trans e2))
    omega

/-- Every transition between states of the path is a consecutive one, with the actual entry. -/
theorem trans_inv (hV : Valid S t) {j l : ℕ} (hj : j ≤ U.D.r) (hl : l ≤ U.D.r) {a : ℤ}
    (h : TransAt t (U.st j) (U.st l) a) : j < U.D.r ∧ l = j + 1 ∧ a = U.D.i l := by
  obtain ⟨ht, hr, ⟨e, he⟩, ⟨v, hv1, hv2⟩, -, -⟩ := h
  have hjr : j < U.D.r := lt_of_le_of_ne hj ((U.term_none_iff j).1 ht)
  have hl1 : 1 ≤ l := Nat.pos_of_ne_zero ((U.root_none_iff l).1 hr)
  have hee := (U.passOK hV hl).exit_unique hV he
  have hM := U.D.two hj
  rw [U.hiS_eq hV hjr] at hv2
  have e2 := hv2.unique ((U.rv_path hj (d := U.D.M j - 1) (by omega)).pcongr
    (by omega) (show _ = U.D.pos (j + 1) by rw [U.D.next j hjr]; omega))
  rw [e2] at hv1
  obtain ⟨h1, h2⟩ := U.D.row_hit U.hp hV (j := j + 1) hjr hl (a := a) he.2.1
    (by have := he.2.2.1; unfold ex at hee; omega) (Or.inl hl1) hv1
  exact ⟨hjr, h1.symm, h2⟩

theorem st_inj (hV : Valid S t) {j l : ℕ} (hj : j ≤ U.D.r) (hl : l ≤ U.D.r)
    (e : U.st j = U.st l) : j = l := by
  have key : (j ≠ U.D.r ↔ l ≠ U.D.r) := by
    rw [← U.term_none_iff, ← U.term_none_iff, e]
  by_cases hjr : j = U.D.r
  · have : l = U.D.r := by by_contra h; exact (key.2 h) hjr
    omega
  · have hlr : l ≠ U.D.r := key.1 hjr
    have hjr' : j < U.D.r := lt_of_le_of_ne hj hjr
    have hlr' : l < U.D.r := lt_of_le_of_ne hl hlr
    have hh : hiS t (U.st j) = hiS t (U.st l) := by rw [e]
    have hjl : U.ex j = U.ex l := by
      unfold ex
      rw [← U.hiS_eq hV hjr', ← U.hiS_eq hV hlr', hh]
    have r1 := (U.rv_path hj le_rfl).pcongr (a' := U.ex j + 2) (by unfold ex; ring) rfl
    have r2 := (U.rv_path hl le_rfl).pcongr (a' := U.ex l + 2) (by unfold ex; ring) rfl
    rw [e, hjl] at r1
    have := lp_inj U.hp (U.D.bound hj) (U.D.bound hl) (r1.unique r2)
    have n1 := U.D.next j hjr'
    have n2 := U.D.next l hlr'
    rcases lt_trichotomy j l with h | h | h
    · have := U.D.pos_lt (j := j + 1) (l := l + 1) (by omega) hlr'; omega
    · exact h
    · have := U.D.pos_lt (j := l + 1) (l := j + 1) (by omega) hjr'; omega

theorem out_pos {j : ℕ} (hj : j ≤ U.D.r) {v : Vertex S t}
    (h : OutV t (U.st j) (U.D.i j) (U.ex j) v) :
    ∃ q, U.D.pos j + 2 ≤ q ∧ q ≤ U.D.pos j + U.D.M j ∧ v = U.p q := by
  obtain ⟨a, h1, h2, hv⟩ := h
  obtain ⟨d, hd⟩ : ∃ d : ℕ, a = U.D.i j + d := ⟨(a - U.D.i j).toNat, by omega⟩
  unfold ex at h2
  have := U.rv_path hj (d := d) (by omega)
  rw [← hd] at this
  exact ⟨U.D.pos j + d, by omega, by omega, hv.unique this⟩

theorem root_idx {j : ℕ} {i : ℤ} (h : RootAt t (U.st j) i) : j = 0 := by
  obtain ⟨m, hm, -⟩ := h
  by_contra hne
  rw [(U.root_none_iff j).2 hne] at hm
  cases hm

/-- Every passage of the state set is an actual passage of the path. -/
theorem passIn_eq (hV : Valid S t) {y : PState S} {i e : ℤ} (h : PassIn t U.X y i e) :
    ∃ l, l ≤ U.D.r ∧ y = U.st l ∧ i = U.D.i l ∧ e = U.ex l := by
  obtain ⟨⟨l, hl, rfl⟩, hent, hpass⟩ := h
  have hi : i = U.D.i l := by
    rcases hent with hroot | ⟨x, ⟨j, hj, rfl⟩, htr⟩
    · have hl0 := U.root_idx hroot
      subst hl0
      exact hroot.unique hV U.rootAt
    · exact (U.trans_inv hV hj hl htr).2.2
  subst hi
  exact ⟨l, hl, rfl, rfl, ((U.passOK hV hl).exit_unique hV hpass).symm⟩

theorem condPass (hV : Valid S t) : CondPass t U.X := by
  rintro _ ⟨j, hj, rfl⟩
  refine ⟨U.D.i j, U.ex j, ?_, U.passOK hV hj⟩
  cases j with
  | zero => exact Or.inl U.rootAt
  | succ j => exact Or.inr ⟨U.st j, ⟨j, by omega, rfl⟩, U.transAt hV hj⟩

theorem condDeg (hV : Valid S t) : CondDeg t U.X := by
  have hr0 : (U.st 0).1.root ≠ none := by rw [Ne, U.root_none_iff]; simp
  have hbr : (U.st U.D.r).1.term ≠ none := by rw [Ne, U.term_none_iff]; simp
  refine ⟨U.st 0, ⟨0, Nat.zero_le _, rfl⟩, U.st U.D.r, ⟨U.D.r, le_rfl, rfl⟩, hr0, hbr,
    ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨j, hj, rfl⟩ h
    rw [Ne, U.root_none_iff, not_not] at h
    rw [h]
  · rintro _ ⟨j, hj, rfl⟩ h
    rw [Ne, U.term_none_iff, not_not] at h
    rw [h]
  · rintro _ ⟨j, hj, rfl⟩ h
    have hjr : j < U.D.r := lt_of_le_of_ne hj ((U.term_none_iff j).1 h)
    refine ⟨U.st (j + 1), ⟨j + 1, hjr, rfl⟩, ⟨_, U.transAt hV hjr⟩, ?_⟩
    rintro _ ⟨l, hl, rfl⟩ ⟨a, ha⟩
    rw [(U.trans_inv hV hj hl ha).2.1]
  · rintro _ ⟨l, hl, rfl⟩ h
    have hl1 : l ≠ 0 := (U.root_none_iff l).1 h
    obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
    refine ⟨U.st j, ⟨j, by omega, rfl⟩, ⟨_, U.transAt hV hl⟩, ?_⟩
    rintro _ ⟨j', hj', rfl⟩ ⟨a, ha⟩
    have := (U.trans_inv hV hj' hl ha).2.1
    rw [show j' = j by omega]

theorem condConn (hV : Valid S t) : CondConn t U.X := by
  intro A hA hne hneq
  obtain ⟨y, hy⟩ := hne
  obtain ⟨j, hj, rfl⟩ := hA hy
  obtain ⟨z, hzX, hzA⟩ : ∃ z ∈ U.X, z ∉ A := by
    by_contra h
    push Not at h
    exact hneq (Set.Subset.antisymm hA h)
  obtain ⟨l, hl, rfl⟩ := hzX
  have key : ∃ m, m < U.D.r ∧ (U.st m ∈ A ↔ U.st (m + 1) ∉ A) := by
    rcases Nat.lt_or_ge j l with h | h
    · obtain ⟨m, -, h2, h3, h4⟩ := exists_flip (fun m => U.st m ∈ A) hy (l - j)
        (by rw [show j + (l - j) = l by omega]; exact hzA)
      exact ⟨m, by omega, by tauto⟩
    · have hjl : l < j := lt_of_le_of_ne h (fun e => by rw [e] at hzA; exact hzA hy)
      obtain ⟨m, -, h2, h3, h4⟩ := exists_flip (fun m => U.st m ∉ A) hzA (j - l)
        (by rw [show l + (j - l) = j by omega]; simpa using hy)
      exact ⟨m, by omega, by tauto⟩
  obtain ⟨m, hm, hiff⟩ := key
  exact ⟨U.st m, ⟨m, hm.le, rfl⟩, U.st (m + 1), ⟨m + 1, hm, rfl⟩, ⟨_, U.transAt hV hm⟩, hiff⟩

theorem ownStart_eq (hV : Valid S t) {l : ℕ} {s : ℤ} (h : OwnStart t (U.st l) s) :
    (l = 0 → s = U.D.i 0) ∧ (l ≠ 0 → s = loS t (U.D.c l)) := by
  rcases h with ⟨hr, rfl⟩ | hr
  · have : l ≠ 0 := (U.root_none_iff l).1 hr
    exact ⟨fun h => absurd h this, fun _ => rfl⟩
  · have hl0 := U.root_idx hr
    subst hl0
    exact ⟨fun _ => hr.unique hV U.rootAt, fun h => absurd rfl h⟩

/-- The full tail of a state of the path is a block of path positions after the previous
passage's start. -/
theorem tail_pos (hV : Valid S t) {l : ℕ} (hl : l ≤ U.D.r) {s e : ℤ} {v : Vertex S t}
    (hs : OwnStart t (U.st l) s) (he : ExitAt t (U.st l) e) (h : OutV t (U.st l) s e v) :
    ∃ q, (l = 0 → 2 ≤ q) ∧ (l ≠ 0 → U.D.pos (l - 1) + 3 ≤ q) ∧ q ≤ U.D.pos l + U.D.M l ∧
      v = U.p q := by
  have hee : e = U.ex l := he.unique hV (U.passOK hV hl).2.2.2.2
  subst hee
  obtain ⟨hs0, hs1⟩ := U.ownStart_eq hV hs
  by_cases hl0 : l = 0
  · subst hl0
    rw [hs0 rfl] at h
    obtain ⟨q, h1, h2, h3⟩ := U.out_pos hl h
    exact ⟨q, fun _ => by rw [U.D.pos0] at h1; omega, fun h => absurd rfl h, h2, h3⟩
  · rw [hs1 hl0] at h
    obtain ⟨hpre, F⟩ := U.D.prefix_follow U.hp hV (Nat.pos_of_ne_zero hl0) hl
    obtain ⟨a, h1, h2, hv⟩ := h
    obtain ⟨hr, hlo, -, -⟩ := exit_of_max U.hp hV (U.D.max l hl)
    set d := (U.D.i l - loS t (U.D.c l)).toNat with hd
    have hd' : (d : ℤ) = U.D.i l - loS t (U.D.c l) := by omega
    obtain ⟨m, hm⟩ : ∃ m : ℕ, a = loS t (U.D.c l) + m := ⟨(a - loS t (U.D.c l)).toNat, by omega⟩
    unfold ex at h2
    have hq := F m (by omega)
    rw [← hm] at hq
    exact ⟨U.D.pos l - d + m, fun h => absurd h hl0, fun _ => by omega, by omega, hv.unique hq⟩

theorem condDisj (hV : Valid S t) : CondDisj t U.X := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ s e _ s' e' ⟨l, hl, rfl⟩ ⟨l', hl', rfl⟩ hs he hs' he' hne hn1 hn2 v hv hv'
    have hll : l ≠ l' := fun e => hne (by rw [e])
    obtain ⟨q, hq0, hq1, hq2, rfl⟩ := U.tail_pos hV hl hs he hv
    obtain ⟨q', hq0', hq1', hq2', hqq⟩ := U.tail_pos hV hl' hs' he' hv'
    have hb := U.D.bound hl
    have hb' := U.D.bound hl'
    have := lp_inj U.hp (by omega) (by omega) hqq
    have c1 : l' ≠ l + 1 := fun h => hn1 ⟨_, by subst h; exact U.transAt hV hl'⟩
    have c2 : l ≠ l' + 1 := fun h => hn2 ⟨_, by subst h; exact U.transAt hV hl⟩
    rcases Nat.lt_or_gt_of_ne hll with h1 | h1
    · have := U.D.pos_succ_le (j := l) (l := l' - 1) (by omega) (by omega)
      have := hq1' (by omega)
      omega
    · have := U.D.pos_succ_le (j := l') (l := l - 1) (by omega) (by omega)
      have := hq1 (by omega)
      omega
  · rintro _ s e _ i e' ⟨j, hj, rfl⟩ ⟨l, hl, rfl⟩ hs he htr he' v hv hv'
    obtain ⟨hjr, rfl, rfl⟩ := U.trans_inv hV hj hl htr
    have hee : e' = U.ex (j + 1) := he'.unique hV (U.passOK hV hl).2.2.2.2
    subst hee
    obtain ⟨q, hq1, hq2, rfl⟩ := U.out_pos hl hv
    obtain ⟨q', -, -, hq2', hqq⟩ := U.tail_pos hV hj hs he hv'
    have hb := U.D.bound hl
    have hb' := U.D.bound hj
    have := lp_inj U.hp (by omega) (by omega) hqq
    have := U.D.next j hjr
    omega
  · rintro _ i₀ _ s e ⟨j, hj, rfl⟩ ⟨l, hl, rfl⟩ hroot hne hs he v hv hout
    have hj0 := U.root_idx hroot
    subst hj0
    have hi := hroot.unique hV U.rootAt
    subst hi
    have hl0 : l ≠ 0 := fun h => hne (by rw [h])
    obtain ⟨q, -, hq1, hq2, rfl⟩ := U.tail_pos hV hl hs he hout
    have hq := hq1 hl0
    have hb := U.D.bound hl
    have hM0 := U.D.two (j := 0) (Nat.zero_le _)
    rcases hv with hv | hv
    · have e := hv.unique ((U.rv_path (Nat.zero_le _) (d := 0) (Nat.zero_le _)).pcongr (P' := 0)
        (by simp) (by simp [U.D.pos0]))
      have := lp_inj U.hp (by omega) (by omega) e
      omega
    · have e := hv.unique ((U.rv_path (Nat.zero_le _) (d := 1) (by omega)).pcongr (P' := 1)
        (by simp) (by simp [U.D.pos0]))
      have := lp_inj U.hp (by omega) (by omega) e
      omega

theorem condEnds (hV : Valid S t) : CondEnds t U.X := by
  have hn := U.hp.1
  have hev := U.hp.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨j, hj, rfl⟩ i hroot
    have hj0 := U.root_idx hroot
    subst hj0
    have hi := hroot.unique hV U.rootAt
    subst hi
    have hM0 := U.D.two (j := 0) (Nat.zero_le _)
    constructor
    · intro v hv
      rw [hv.unique ((U.rv_path (Nat.zero_le _) (d := 0) (Nat.zero_le _)).pcongr (P' := 0) (by simp)
        (by simp [U.D.pos0]))]
      exact U.hp.2.2.2.2.2.1
    · intro v hv
      rw [hv.unique ((U.rv_path (Nat.zero_le _) (d := 1) (by omega)).pcongr (P' := 1) (by simp)
        (by simp [U.D.pos0]))]
      exact U.hp.2.2.2.2.2.2.2.1
  · intro y i e h hterm
    obtain ⟨l, hl, rfl, rfl, rfl⟩ := U.passIn_eq hV h
    have hlr : l = U.D.r := by
      by_contra hne
      exact hterm ((U.term_none_iff l).2 hne)
    subst hlr
    have hM := U.D.two hl
    have hlast := U.D.last
    constructor
    · intro v hv
      rw [hv.unique ((U.rv_path hl le_rfl).pcongr (by unfold ex; ring) hlast)]
      exact U.hp.2.2.2.2.2.2.1
    · intro v hv
      rw [hv.unique ((U.rv_path hl (d := U.D.M U.D.r - 1) (by omega)).pcongr
        (by unfold ex; omega) (show _ = U.n - 2 by omega))]
      exact U.hp.2.2.2.2.2.2.2.2
  · rintro _ ⟨j, hj, rfl⟩ h
    have : j = 0 := by
      by_contra hne
      exact h ((U.root_none_iff j).2 hne)
    subst this
    simp [st, U.D.pos0]
  · intro x i e y i' h hy htr
    obtain ⟨j, hj, rfl, rfl, rfl⟩ := U.passIn_eq hV h
    obtain ⟨l, hl, rfl⟩ := hy
    obtain ⟨hjr, rfl, -⟩ := U.trans_inv hV hj hl htr
    have hnext := U.D.next j hjr
    have hM := U.D.two hj
    simp only [st, ex, decide_eq_decide, Int.even_iff]
    rw [hnext]
    omega
  · intro y i e h hterm
    obtain ⟨l, hl, rfl, rfl, rfl⟩ := U.passIn_eq hV h
    have hlr : l = U.D.r := by
      by_contra hne
      exact hterm ((U.term_none_iff l).2 hne)
    subst hlr
    have hlast := U.D.last
    have hM := U.D.two hl
    rw [Nat.even_iff] at hev
    simp only [st, ex, decide_eq_false_iff_not, Int.even_iff]
    omega
  · intro x i e h hroot hterm
    obtain ⟨l, hl, rfl, rfl, rfl⟩ := U.passIn_eq hV h
    have hl0 : l = 0 := by
      by_contra hne
      exact hroot ((U.root_none_iff l).2 hne)
    have hlr : l = U.D.r := by
      by_contra hne
      exact hterm ((U.term_none_iff l).2 hne)
    have hlast := U.D.last
    subst hl0
    rw [← hlr, U.D.pos0] at hlast
    unfold ex
    omega

/-- **The state set of a literal path satisfies the four conditions.** -/
theorem cond (hV : Valid S t) :
    U.X ⊆ R002.Claude3Fold.St stLo stHi t ∧ Cond t U.X := by
  refine ⟨?_, U.condPass hV, U.condDeg hV, U.condConn hV, U.condDisj hV, U.condEnds hV⟩
  rintro _ ⟨j, hj, rfl⟩
  exact (mem_St_iff t _).2 (U.passOK hV hj).1

end Sup

/-- **(⇒) of the reduction theorem.** -/
theorem cond_of_pathExists (hV : Valid S t) (hTC : ClaudeChallenge2.TrianglesInCharts S t)
    (h : PathExists S t) : ∃ X ⊆ R002.Claude3Fold.St (stLo (S := S)) stHi t, Cond t X := by
  obtain ⟨n, p, hp⟩ := h
  obtain ⟨D⟩ := exists_decomp hp hTC
  obtain ⟨m0, hm0⟩ := hV.2.2.2 _ hp.2.2.2.2.2.1
  obtain ⟨m1, hm1⟩ := hV.2.2.2 _ hp.2.2.2.2.2.2.1
  let U : Sup S t := ⟨n, p, hp, D, m0, m1, hm0, hm1⟩
  exact ⟨U.X, (U.cond hV).1, (U.cond hV).2⟩

end ClaudeChallenge2.State
