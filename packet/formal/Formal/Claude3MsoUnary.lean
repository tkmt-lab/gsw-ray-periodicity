import Formal.Claude3MsoRegular
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Unary corollary: MSO spectra over a one-letter alphabet are eventually periodic

* `eventuallyPeriodic_iterate`: orbits of a self-map of a finite type are eventually periodic.
* `IsRegular.eventuallyPeriodic_replicate`: `{n | replicate n a ∈ L}` for a regular `L`.
* `eventuallyPeriodic_models_replicate`: `{n | replicate n a ⊨ φ}` for an MSO sentence `φ`.
* `eventuallyPeriodic_interleave`, `eventuallyPeriodic_models_residues`,
  `eventuallyPeriodic_models_parity`: combining finitely many residue classes `t = q n + η`,
  each class described by its own sentence.
-/

namespace R002.Claude3Mso

universe u

/-- `S ⊆ ℕ` is eventually periodic. -/
def EventuallyPeriodic (S : Set ℕ) : Prop :=
  ∃ t₀ P : ℕ, 0 < P ∧ ∀ t ≥ t₀, (t ∈ S ↔ t + P ∈ S)

theorem EventuallyPeriodic.mul_period {S : Set ℕ} {t₀ P : ℕ}
    (h : ∀ t ≥ t₀, (t ∈ S ↔ t + P ∈ S)) (c : ℕ) : ∀ t ≥ t₀, (t ∈ S ↔ t + c * P ∈ S) := by
  induction c with
  | zero => intro t _; simp
  | succ c ih =>
    intro t ht
    rw [ih t ht, h (t + c * P) (by omega), Nat.succ_mul, Nat.add_assoc]

/-- Orbits of a self-map of a finite type are eventually periodic. -/
theorem eventuallyPeriodic_iterate {σ : Type*} [Finite σ] (g : σ → σ) (s : σ) (A : Set σ) :
    EventuallyPeriodic {n | g^[n] s ∈ A} := by
  obtain ⟨i, j, hne, hij⟩ := Finite.exists_ne_map_eq_of_infinite (fun n => g^[n] s)
  have key : ∀ i j, i < j → g^[i] s = g^[j] s → EventuallyPeriodic {n | g^[n] s ∈ A} := by
    intro i j hlt heq
    refine ⟨i, j - i, by omega, fun t ht => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    have : g^[i + d + (j - i)] s = g^[i + d] s := by
      rw [show i + d + (j - i) = d + j by omega, Function.iterate_add_apply, ← heq,
        ← Function.iterate_add_apply, Nat.add_comm d i]
    simp only [Set.mem_ofPred_eq, this]
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key i j h hij
  · exact key j i h hij.symm

theorem DFA.eval_replicate {α : Type u} {σ : Type*} (M : DFA α σ) (a : α) (n : ℕ) :
    M.eval (List.replicate n a) = (fun s => M.step s a)^[n] M.start := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ', DFA.eval_append_singleton, ih, Function.iterate_succ_apply']

/-- Unary words of a regular language have an eventually periodic length set. -/
theorem _root_.Language.IsRegular.eventuallyPeriodic_replicate {α : Type u} {L : Language α}
    (h : L.IsRegular) (a : α) : EventuallyPeriodic {n | List.replicate n a ∈ L} := by
  obtain ⟨σ, _, M, rfl⟩ := h
  have := eventuallyPeriodic_iterate (fun s => M.step s a) M.start M.accept
  simpa only [DFA.mem_accepts, DFA.eval_replicate] using this

/-- **Unary corollary.** For an MSO sentence `φ` and a letter `a`,
`{n | replicate n a ⊨ φ}` is eventually periodic. -/
theorem eventuallyPeriodic_models_replicate {α : Type u} (φ : Sentence α) (a : α) :
    EventuallyPeriodic {n | Models (List.replicate n a) φ} :=
  (isRegular_modelsLang φ).eventuallyPeriodic_replicate a

/-- One-letter alphabet: a word is determined by its length, and the length spectrum
`{n | ∃ w, w.length = n ∧ w ⊨ φ}` is eventually periodic. -/
theorem eventuallyPeriodic_models_unique {α : Type u} [Unique α] (φ : Sentence α) :
    EventuallyPeriodic {n | ∃ w : List α, w.length = n ∧ Models w φ} := by
  have e : {n | ∃ w : List α, w.length = n ∧ Models w φ} =
      {n | Models (List.replicate n default) φ} := by
    ext n
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨w, rfl, hw⟩
      have : w = List.replicate w.length default :=
        List.eq_replicate_iff.2 ⟨rfl, fun b _ => Unique.eq_default b⟩
      rwa [← this]
    · exact fun h => ⟨_, List.length_replicate, h⟩
  rw [e]
  exact eventuallyPeriodic_models_replicate φ default

/-- Interleaving finitely many eventually periodic sets along residues mod `q`. -/
theorem eventuallyPeriodic_interleave {q : ℕ} (hq : 0 < q) (S : ℕ → Set ℕ)
    (h : ∀ η < q, EventuallyPeriodic (S η)) :
    EventuallyPeriodic {t | t / q ∈ S (t % q)} := by
  classical
  have h' : ∀ η, ∃ t₀ P : ℕ, 0 < P ∧ ∀ t ≥ t₀, η < q → (t ∈ S η ↔ t + P ∈ S η) := by
    intro η
    by_cases hη : η < q
    · obtain ⟨t₀, P, hP, hper⟩ := h η hη
      exact ⟨t₀, P, hP, fun t ht _ => hper t ht⟩
    · exact ⟨0, 1, one_pos, fun _ _ h => absurd h hη⟩
  choose t₀ P hP hper using h'
  let T := ∑ η ∈ Finset.range q, t₀ η
  let Q := ∏ η ∈ Finset.range q, P η
  have hQ : 0 < Q := Finset.prod_pos fun η _ => hP η
  refine ⟨q * T, q * Q, Nat.mul_pos hq hQ, fun t ht => ?_⟩
  have hη : t % q < q := Nat.mod_lt _ hq
  have hmem : t % q ∈ Finset.range q := Finset.mem_range.2 hη
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem P hmem
  have hT : t₀ (t % q) ≤ t / q := by
    have h1 : t₀ (t % q) ≤ T := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
    have h2 : T ≤ t / q := (Nat.le_div_iff_mul_le hq).2 (by rw [Nat.mul_comm]; exact ht)
    omega
  have hmod : (t + q * Q) % q = t % q := Nat.add_mul_mod_self_left t q Q
  have hdiv : (t + q * Q) / q = t / q + Q := Nat.add_mul_div_left t Q hq
  simp only [Set.mem_ofPred_eq, hmod, hdiv]
  have hcQ : Q = c * P (t % q) := by rw [Nat.mul_comm]; exact hc
  rw [hcQ]
  exact EventuallyPeriodic.mul_period (fun s hs => hper _ s hs hη) c _ hT

/-- Residue classes `t = q n + η` (`η < q`), each described by its own sentence `φ η`. -/
theorem eventuallyPeriodic_models_residues {α : Type u} {q : ℕ} (hq : 0 < q)
    (φ : ℕ → Sentence α) (a : α) :
    EventuallyPeriodic {t | Models (List.replicate (t / q) a) (φ (t % q))} :=
  eventuallyPeriodic_interleave hq (fun η => {n | Models (List.replicate n a) (φ η)})
    (fun η _ => eventuallyPeriodic_models_replicate (φ η) a)

/-- Two residue classes: `t = 2n` governed by `φ₀`, `t = 2n + 1` governed by `φ₁`. -/
theorem eventuallyPeriodic_models_parity {α : Type u} (φ₀ φ₁ : Sentence α) (a : α) :
    EventuallyPeriodic {t | ∃ n, (t = 2 * n ∧ Models (List.replicate n a) φ₀) ∨
      (t = 2 * n + 1 ∧ Models (List.replicate n a) φ₁)} := by
  have := eventuallyPeriodic_models_residues (q := 2) (by norm_num)
    (fun η => if η = 0 then φ₀ else φ₁) a
  convert this using 1
  ext t
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, ⟨rfl, hn⟩ | ⟨rfl, hn⟩⟩
    · have e1 : 2 * n / 2 = n := by omega
      have e2 : 2 * n % 2 = 0 := by omega
      simpa [e1, e2] using hn
    · have e1 : (2 * n + 1) / 2 = n := by omega
      have e2 : (2 * n + 1) % 2 = 1 := by omega
      simpa [e1, e2] using hn
  · intro h
    rcases Nat.mod_two_eq_zero_or_one t with h2 | h2
    · exact ⟨t / 2, Or.inl ⟨by omega, by simpa [h2] using h⟩⟩
    · exact ⟨t / 2, Or.inr ⟨by omega, by simpa [h2] using h⟩⟩

end R002.Claude3Mso
