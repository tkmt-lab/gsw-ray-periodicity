import Formal.Claude3StateLemmas

/-!
# Theorem 1a, G5 (⇐), part 1: a chain of passages gives a literal path

Written by a Claude worker (2026-10-20, Theorem 1a, parts G4/G5).

`Chain S t` : states `σ 0, …, σ r` with entries `ent j` and exits `ext j`, valid passages,
generic transitions `σ j → σ (j+1)`, pairwise disjoint outputs, outputs disjoint from the two
saved root vertices, the endpoint degrees, the count parity and the one-passage size bound.

`Chain.pathExists` : under `Valid`, such a chain gives a literal path (paper `lem:mso-path`,
"Join the passages in this order …"). The path is built from the end: `Claim j` is the
statement for the walk from passage `j` on (backward induction).
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 ClaudeChallenge2.Geo

variable {S : Sig} {t : ℕ}

/-- A chain of passages (the data extracted from a state set satisfying the conditions). -/
structure Chain (S : Sig) (t : ℕ) where
  r : ℕ
  σ : ℕ → PState S
  ent : ℕ → ℤ
  ext : ℕ → ℤ
  pass : ∀ j, j ≤ r → PassOK t (σ j) (ent j) (ext j)
  trans : ∀ j, j < r → TransAt t (σ j) (σ (j + 1)) (ent (j + 1))
  disj : ∀ j l, j ≤ r → l ≤ r → j ≠ l →
    ∀ v, OutV t (σ j) (ent j) (ext j) v → ¬ OutV t (σ l) (ent l) (ext l) v
  saved : ∀ l, l ≤ r → ∀ v, (RV t (σ 0) (ent 0) v ∨ RV t (σ 0) (ent 0 + 1) v) →
    ¬ OutV t (σ l) (ent l) (ext l) v
  deg0 : ∀ v, RV t (σ 0) (ent 0) v → deg (graph S t) v = 5
  deg1 : ∀ v, RV t (σ 0) (ent 0 + 1) v → deg (graph S t) v = 6
  degN : ∀ v, RV t (σ r) (ext r + 2) v → deg (graph S t) v = 5
  degN1 : ∀ v, RV t (σ r) (ext r + 1) v → deg (graph S t) v = 6
  par0 : (σ 0).1.par = false
  parS : ∀ j, j < r → ((σ (j + 1)).1.par = (σ j).1.par ↔ Even (ext j - ent j + 1))
  parN : ((σ r).1.par = false ↔ Even (ext r - ent r + 1))
  size : r = 0 → ent 0 + 1 ≤ ext 0

/-- Four consecutive points of a row function are a forced step. -/
theorem rowfun_next (hV : Valid S t) {σ : PState S} {i : ℤ} {L : ℕ} {w : ℕ → Vertex S t}
    (hw : ∀ m : ℕ, m ≤ L + 2 → RV t σ (i + m) (w m)) (k : ℕ) (hk : k + 3 ≤ L + 2) :
    Next (graph S t) (w k) (w (k + 1)) (w (k + 2)) (w (k + 3)) :=
  RV.next hV (hw k (by omega)) ((hw (k + 1) (by omega)).congr (by push_cast; ring))
    ((hw (k + 2) (by omega)).congr (by push_cast; ring))
    ((hw (k + 3) (by omega)).congr (by push_cast; ring))

namespace Chain

variable (C : Chain S t)

/-- Number of triangles of passage `j`, minus one. -/
def nn (j : ℕ) : ℕ := (C.ext j - C.ent j).toNat

theorem nn_eq {j : ℕ} (hj : j ≤ C.r) : (C.nn j : ℤ) = C.ext j - C.ent j := by
  have := (C.pass j hj).2.2.1
  unfold nn
  omega

theorem exists_rowfun {j : ℕ} (hj : j ≤ C.r) :
    ∃ w : ℕ → Vertex S t, ∀ m : ℕ, m ≤ C.nn j + 2 → RV t (C.σ j) (C.ent j + m) (w m) := by
  have hn := C.nn_eq hj
  obtain ⟨v₀, -⟩ := (C.pass j hj).rv (j := C.ent j) le_rfl (by omega)
  have H : ∀ m : ℕ, ∃ v, m ≤ C.nn j + 2 → RV t (C.σ j) (C.ent j + m) v := by
    intro m
    by_cases hm : m ≤ C.nn j + 2
    · obtain ⟨v, hv⟩ := (C.pass j hj).rv (j := C.ent j + m) (by omega) (by omega)
      exact ⟨v, fun _ => hv⟩
    · exact ⟨v₀, fun h => absurd h hm⟩
  choose w hw using H
  exact ⟨w, hw⟩

/-- The walk from passage `j` on. -/
def Claim (j : ℕ) : Prop :=
  ∃ (w : ℕ → Vertex S t) (N : ℕ),
    (∀ m : ℕ, m ≤ C.nn j + 2 → RV t (C.σ j) (C.ent j + m) (w m)) ∧
    IsForced (graph S t) w N ∧
    C.nn j + 3 ≤ N ∧ (j < C.r → C.nn j + 4 ≤ N) ∧
    (∀ q, 2 ≤ q → q < N → ∃ l, j ≤ l ∧ l ≤ C.r ∧ OutV t (C.σ l) (C.ent l) (C.ext l) (w q)) ∧
    (∀ q q', 2 ≤ q → 2 ≤ q' → q < N → q' < N → w q = w q' → q = q') ∧
    RV t (C.σ C.r) (C.ext C.r + 2) (w (N - 1)) ∧ RV t (C.σ C.r) (C.ext C.r + 1) (w (N - 2)) ∧
    ((C.σ j).1.par = false ↔ Even N)

theorem claim_last (hV : Valid S t) : C.Claim C.r := by
  obtain ⟨w, hw⟩ := C.exists_rowfun le_rfl
  have hn := C.nn_eq le_rfl
  refine ⟨w, C.nn C.r + 3, hw, fun k hk => rowfun_next hV hw k (by omega), le_rfl,
    fun h => absurd h (lt_irrefl _), ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq hq'
    exact ⟨C.r, le_rfl, le_rfl, C.ent C.r + q, by omega, by omega, hw q (by omega)⟩
  · intro q q' _ _ hq hq' e
    have h1 := hw q (by omega)
    rw [e] at h1
    have := h1.inj hV (hw q' (by omega))
    omega
  · rw [show C.nn C.r + 3 - 1 = C.nn C.r + 2 by omega]
    exact (hw _ le_rfl).congr (by push_cast; omega)
  · rw [show C.nn C.r + 3 - 2 = C.nn C.r + 1 by omega]
    exact (hw _ (by omega)).congr (by push_cast; omega)
  · rw [C.parN]
    simp only [Int.even_iff, Nat.even_iff]
    omega

theorem claim_step (hV : Valid S t) {j : ℕ} (hj : j < C.r) (H : C.Claim (j + 1)) :
    C.Claim j := by
  obtain ⟨w', N', ha', hb', hc', -, hd', he', hf', hf2', hg'⟩ := H
  obtain ⟨u, hu⟩ := C.exists_rowfun hj.le
  have hn := C.nn_eq hj.le
  have htr := C.trans j hj
  have hext : C.ext j = hiS t (C.σ j) := (C.pass j hj.le).2.2.2.2.1 htr.1
  set n := C.nn j with hn_def
  let w : ℕ → Vertex S t := fun q => if q ≤ n then u q else w' (q - n - 1)
  have hwlo : ∀ q, q ≤ n → w q = u q := fun q hq => ite_eq_left_iff.2 fun h => absurd hq h
  have hwhi : ∀ q, n + 1 ≤ q → w q = w' (q - n - 1) := fun q hq =>
    ite_eq_right_iff.2 fun h => absurd h (by omega)
  have s0 : RV t (C.σ j) (C.ent j + ((n + 1 : ℕ) : ℤ)) (w' 0) := by
    obtain ⟨v, hv, hxv⟩ := htr.2.2.2.1
    rw [(ha' 0 (by omega)).unique (hv.congr (by simp))]
    exact hxv.congr (by push_cast; omega)
  have s1 : RV t (C.σ j) (C.ent j + ((n + 2 : ℕ) : ℤ)) (w' 1) := by
    obtain ⟨v, hv, hxv⟩ := htr.2.2.2.2.1
    rw [(ha' 1 (by omega)).unique (hv.congr (by simp))]
    exact hxv.congr (by push_cast; omega)
  have ha : ∀ m : ℕ, m ≤ n + 2 → RV t (C.σ j) (C.ent j + m) (w m) := by
    intro m hm
    rcases (show m ≤ n ∨ m = n + 1 ∨ m = n + 2 by omega) with h | rfl | rfl
    · rw [hwlo m h]; exact hu m (by omega)
    · rw [hwhi _ le_rfl, show n + 1 - n - 1 = 0 by omega]; exact s0
    · rw [hwhi _ (by omega), show n + 2 - n - 1 = 1 by omega]; exact s1
  have cross : ∀ q q', 2 ≤ q → q ≤ n + 2 → n + 3 ≤ q' → q' < n + 1 + N' → w q ≠ w q' := by
    intro q q' h1 h2 h3 h4 e
    obtain ⟨l, hl1, hl2, hout⟩ := hd' (q' - n - 1) (by omega) (by omega)
    rw [← hwhi q' (by omega), ← e] at hout
    exact C.disj j l hj.le hl2 (by omega) _ ⟨C.ent j + q, by omega, by omega, ha q h2⟩ hout
  refine ⟨w, n + 1 + N', ha, ?_, by omega, fun _ => by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    by_cases h1 : k + 3 ≤ n + 2
    · exact rowfun_next hV ha k h1
    by_cases h2 : n + 1 ≤ k
    · rw [hwhi k h2, hwhi (k + 1) (by omega), hwhi (k + 2) (by omega), hwhi (k + 3) (by omega)]
      have := hb' (k - n - 1) (by omega)
      rwa [show k + 1 - n - 1 = k - n - 1 + 1 by omega, show k + 2 - n - 1 = k - n - 1 + 2 by omega,
        show k + 3 - n - 1 = k - n - 1 + 3 by omega]
    · have hk : k = n := by omega
      rw [hk, hwlo n le_rfl, hwhi (n + 1) (by omega), hwhi (n + 2) (by omega),
        hwhi (n + 3) (by omega), show n + 1 - n - 1 = 0 by omega,
        show n + 2 - n - 1 = 1 by omega, show n + 3 - n - 1 = 2 by omega]
      exact htr.next hV ((hu n (by omega)).congr (by omega)) ((ha' 0 (by omega)).congr (by simp))
        ((ha' 1 (by omega)).congr (by simp)) ((ha' 2 (by omega)).congr (by simp))
  · intro q hq hq'
    by_cases h : q ≤ n + 2
    · exact ⟨j, le_rfl, hj.le, C.ent j + q, by omega, by omega, ha q h⟩
    · obtain ⟨l, hl1, hl2, hout⟩ := hd' (q - n - 1) (by omega) (by omega)
      rw [← hwhi q (by omega)] at hout
      exact ⟨l, by omega, hl2, hout⟩
  · intro q q' h1 h1' h2 h2' e
    by_cases hq : q ≤ n + 2 <;> by_cases hq' : q' ≤ n + 2
    · have h := ha q hq
      rw [e] at h
      have := h.inj hV (ha q' hq')
      omega
    · exact absurd e (cross q q' h1 hq (by omega) h2')
    · exact absurd e.symm (cross q' q h1' hq' (by omega) h2)
    · rw [hwhi q (by omega), hwhi q' (by omega)] at e
      have := he' _ _ (by omega) (by omega) (by omega) (by omega) e
      omega
  · rw [hwhi _ (by omega), show n + 1 + N' - 1 - n - 1 = N' - 1 by omega]
    exact hf'
  · rw [hwhi _ (by omega), show n + 1 + N' - 2 - n - 1 = N' - 2 by omega]
    exact hf2'
  · have p1 := C.parS j hj
    rw [← hn] at p1
    simp only [Int.even_iff, Nat.even_iff] at p1 hg' ⊢
    cases hp : (C.σ j).1.par <;> cases hp' : (C.σ (j + 1)).1.par <;>
      simp only [hp, hp', true_iff, Bool.false_eq_true, false_iff,
        Bool.true_eq_false] at p1 hg' ⊢ <;> omega

/-- **(⇐), from a chain.** Under `Valid`, a chain of passages gives a literal path. -/
theorem pathExists (C : Chain S t) (hV : Valid S t) : PathExists S t := by
  have key : ∀ d, d ≤ C.r → C.Claim (C.r - d) := by
    intro d
    induction d with
    | zero => intro _; simpa using C.claim_last hV
    | succ d ih =>
      intro hd
      refine C.claim_step hV (j := C.r - (d + 1)) (by omega) ?_
      rw [show C.r - (d + 1) + 1 = C.r - d by omega]
      exact ih (by omega)
  have h0 := key C.r le_rfl
  rw [Nat.sub_self] at h0
  obtain ⟨w, N, ha, hb, hc, hc4, hd, he, hf, hf2, hg⟩ := h0
  have hn := C.nn_eq (Nat.zero_le _)
  have r0 : RV t (C.σ 0) (C.ent 0) (w 0) := (ha 0 (by omega)).congr (by simp)
  have r1 : RV t (C.σ 0) (C.ent 0 + 1) (w 1) := (ha 1 (by omega)).congr (by simp)
  have r2 : RV t (C.σ 0) (C.ent 0 + 2) (w 2) := (ha 2 (by omega)).congr (by simp)
  have h4 : 4 ≤ N := by
    by_cases hr : C.r = 0
    · have := C.size hr; omega
    · exact le_trans (by omega) (hc4 (by omega))
  refine ⟨N, w, (literalPath_iff_forced N w).2 ⟨h4, (hg.1 C.par0), ?_, r0.adj1 hV r1,
    r0.adj2 hV r2, r1.adj1 hV (r2.congr (by ring)), hb, C.deg0 _ r0, C.degN _ hf,
    C.deg1 _ r1, C.degN1 _ hf2⟩⟩
  have early : ∀ i q, i < 2 → 2 ≤ q → q < N → w i ≠ w q := by
    intro i q hi hq hq' e
    obtain ⟨l, -, hl, hout⟩ := hd q hq hq'
    rw [← e] at hout
    refine C.saved l hl (w i) ?_ hout
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact Or.inl r0
    · exact Or.inr r1
  intro i q hi hq e
  by_cases h1 : i < 2 <;> by_cases h2 : q < 2
  · rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
      rcases (show q = 0 ∨ q = 1 by omega) with rfl | rfl
    · rfl
    · rw [e] at r0; have := r0.inj hV r1; omega
    · rw [e] at r1; have := r1.inj hV r0; omega
    · rfl
  · exact absurd e (early i q h1 (by omega) hq)
  · exact absurd e.symm (early q i h2 (by omega) hi)
  · exact he i q (by omega) (by omega) hi hq e

end Chain

end ClaudeChallenge2.State
