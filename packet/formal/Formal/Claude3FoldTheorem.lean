import Formal.Claude3FoldMain
import Mathlib.Basic.Finite.Prod
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Main theorem: sentences of the restricted height arithmetic are eventually periodic in `t`

* `evDef_tr`: for every formula `φ`, every assignment `σ` of copies to its free state
  variables and every layout `g` of the per-copy set variables, the truth of `φ` at
  `t = 2n + η` under the decoded valuations is eventually MSO-definable.
* `eventuallyPeriodic_holds`: for every sentence `φ`, `{t | Holds lo hi t φ}` is eventually
  periodic.
* `eventuallyPeriodic_of_holds`: the same for any property that agrees with such a sentence
  for all large `t`.
-/

namespace R002.Claude3Fold

open R002.Claude3Mso MSO

universe u

variable {T : Type u} [Finite T] (lo hi : T → Aff) (η J : ℕ)

omit [Finite T] in
theorem dec_cons {m : ℕ} (n : ℕ) (c : Cp T J) (σ : Fin m → Cp T J) (v : ℕ) (ν : Fin m → ℕ) :
    (fun i => dec η J n ((Fin.cons c σ : Fin (m + 1) → Cp T J) i)
      ((Fin.cons v ν : Fin (m + 1) → ℕ) i)) =
      Fin.cons (dec η J n c v) (fun i => dec η J n (σ i) (ν i)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

/-- **Translation.** Every formula, under decoding, is eventually MSO-definable. -/
theorem evDef_tr (hη : η < 2) (hJ : Bounded lo hi J) :
    ∀ {m k : ℕ} (φ : HF T m k) (K : ℕ) (g : Fin k → Cp T J → Fin K) (σ : Fin m → Cp T J),
      EvDef (fun n ν V => HF.Sat lo hi (2 * n + η) φ (fun i => dec η J n (σ i) (ν i))
        (fun i => decSet lo hi η J n (fun c => V (g i c)))) := by
  have s1 : IsSgn 1 := by simp [IsSgn]
  have s0 : IsSgn 0 := by simp [IsSgn]
  have sm : IsSgn (-1) := by simp [IsSgn]
  intro m k φ
  induction φ with
  | typ x τ =>
    intro K g σ
    exact (EvDef.const ((σ x).1 = τ)).congr 0 fun n _ ν _ V => by simp
  | eq x y =>
    intro K g σ
    exact (evDef_decEq η J (σ x) (σ y) x y).congr 0 fun _ _ _ _ _ => by simp
  | le x f =>
    intro K g σ
    exact (evDef_decLin η J s1 s0 (σ x) (σ x) x x f).congr 0 fun _ _ _ _ _ => by simp
  | nle x f =>
    intro K g σ
    exact (evDef_decLin η J sm s0 (σ x) (σ x) x x f).congr 0 fun _ _ _ _ _ => by simp
  | addLe x y f =>
    intro K g σ
    exact (evDef_decLin η J s1 s1 (σ x) (σ y) x y f).congr 0 fun _ _ _ _ _ => by simp
  | subLe x y f =>
    intro K g σ
    refine (evDef_decLin η J s1 sm (σ x) (σ y) x y f).congr 0 fun _ _ _ _ _ => ?_
    simp only [HF.Sat, one_mul, neg_mul]
    constructor <;> intro h <;> linarith
  | negAddLe x y f =>
    intro K g σ
    refine (evDef_decLin η J sm sm (σ x) (σ y) x y f).congr 0 fun _ _ _ _ _ => ?_
    simp only [HF.Sat, one_mul, neg_mul]
    constructor <;> intro h <;> linarith
  | modEq x q r =>
    intro K g σ
    exact (EvDef.modEq q (cA J (σ x)) (cB η J (σ x)) (sg_isSgn J (σ x)) r x).congr 0
      fun n _ ν _ V => by simp only [HF.Sat, dec_snd]
  | tModEq q r =>
    intro K g σ
    exact (EvDef.tmodEq q η r).congr 0 fun _ _ _ _ _ => by simp
  | tNonneg f =>
    intro K g σ
    refine (EvDef.affine_nonneg (2 * f.a) (f.a * η + f.b)).congr 0 fun n _ _ _ _ => ?_
    simp only [HF.Sat, Aff.eval]
    apply le_iff_le_of_sub_eq
    push_cast
    ring
  | mem x X =>
    intro K g σ
    refine (EvDef.exists_fintype fun c => EvDef.exF
      ((EvDef.of_exact (MSO.mem 0 (g X c)) fun _ _ _ _ => Iff.rfl).and
        ((evDef_valid lo hi η J c 0).and (evDef_decEq η J c (σ x) 0 x.succ)))).congr 0
      fun n _ ν _ V => ?_
    simp only [HF.Sat, MSO.Sat, decSet, Set.mem_ofPred_eq, Fin.cons_zero, Fin.cons_succ]
  | neg φ ih =>
    intro K g σ
    exact (ih K g σ).neg.congr 0 fun _ _ _ _ _ => by simp
  | and φ ψ ih₁ ih₂ =>
    intro K g σ
    exact ((ih₁ K g σ).and (ih₂ K g σ)).congr 0 fun _ _ _ _ _ => by simp
  | exF φ ih =>
    intro K g σ
    refine (EvDef.exists_fintype fun c => EvDef.exF
      ((evDef_valid lo hi η J c 0).and (ih K g (Fin.cons c σ)))).congr (J + 1)
      fun n hn ν _ V => ?_
    simp only [HF.Sat, dec_cons, Fin.cons_zero]
    constructor
    · rintro ⟨c, v, -, hval, hφ⟩
      exact ⟨_, hval, hφ⟩
    · rintro ⟨s, hs, hφ⟩
      obtain ⟨c, v, hv, rfl⟩ := exists_dec lo hi η J hη hJ hn hs
      exact ⟨c, v, hv, hs, hφ⟩
  | @exS m k φ ih =>
    intro K g σ
    let e := Finite.equivFin (Cp T J)
    let g' : Fin (k + 1) → Cp T J → Fin (K + Nat.card (Cp T J)) :=
      Fin.cons (fun c => EvDef.idxW (e c)) (fun i c => EvDef.idxV (g i c))
    have hg : ∀ n (W : Fin (Nat.card (Cp T J)) → Set ℕ) (V : Fin K → Set ℕ),
        (fun i => decSet lo hi η J n (fun c => EvDef.ext _ W V (g' i c))) =
          Fin.cons (decSet lo hi η J n (fun c => W (e c)))
            (fun i => decSet lo hi η J n (fun c => V (g i c))) := by
      intro n W V
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [g', Fin.cons_zero, EvDef.ext_idxW]
      · simp only [g', Fin.cons_succ, EvDef.ext_idxV]
    refine (EvDef.exSN _ (ih (K + Nat.card (Cp T J)) g' σ)).congr (J + 1)
      fun n hn ν _ V => ?_
    simp only [HF.Sat, hg]
    constructor
    · rintro ⟨W, -, hφ⟩
      exact ⟨_, decSet_subset lo hi η J n _, hφ⟩
    · rintro ⟨X, hX, hφ⟩
      refine ⟨fun d => {v | v < n ∧ dec η J n (e.symm d) v ∈ X}, fun d v hv => hv.1, ?_⟩
      simp only [Equiv.symm_apply_apply]
      rw [decSet_eq lo hi η J hη hJ hn hX]
      exact hφ

omit [Finite T] in
theorem eventuallyPeriodic_of_eventually_iff {S S' : Set ℕ} (h : EventuallyPeriodic S')
    (t₁ : ℕ) (hS : ∀ t, t₁ ≤ t → (t ∈ S ↔ t ∈ S')) : EventuallyPeriodic S := by
  obtain ⟨t₀, P, hP, hper⟩ := h
  refine ⟨max t₀ t₁, P, hP, fun t ht => ?_⟩
  rw [hS t (le_of_max_le_right ht), hS (t + P) (by have := le_of_max_le_right ht; omega)]
  exact hper t (le_of_max_le_left ht)

/-- **Main theorem (paper §3.3).** For every sentence `φ` of the restricted arithmetic over
heights, the set of parameters `t` at which `φ` holds is eventually periodic. -/
theorem eventuallyPeriodic_holds (φ : HSentence T) :
    EventuallyPeriodic {t | Holds lo hi t φ} := by
  obtain ⟨J, hJ⟩ := exists_bounded lo hi
  have key : ∀ η, η < 2 → ∃ ψ : Sentence Unit, ∃ N, ∀ n, N ≤ n →
      (Models (List.replicate n ()) ψ ↔ Holds lo hi (2 * n + η) φ) := by
    intro η hη
    obtain ⟨ψ, N, h⟩ := evDef_tr lo hi η J hη hJ φ 0 (fun i => i.elim0) (fun i => i.elim0)
    refine ⟨ψ, N, fun n hn => ?_⟩
    unfold Models Holds
    rw [h n hn (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)]
    beta_reduce
    exact iff_of_eq (by congr 1 <;> funext i <;> exact i.elim0)
  obtain ⟨ψ₀, N₀, h₀⟩ := key 0 (by norm_num)
  obtain ⟨ψ₁, N₁, h₁⟩ := key 1 (by norm_num)
  refine eventuallyPeriodic_of_eventually_iff (eventuallyPeriodic_models_parity ψ₀ ψ₁ ())
    (2 * (N₀ + N₁) + 2) fun t ht => ?_
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    rcases Nat.even_or_odd' t with ⟨n, rfl | rfl⟩
    · exact ⟨n, Or.inl ⟨rfl, (h₀ n (by omega)).2 (by simpa using h)⟩⟩
    · exact ⟨n, Or.inr ⟨rfl, (h₁ n (by omega)).2 h⟩⟩
  · rintro ⟨n, ⟨rfl, hm⟩ | ⟨rfl, hm⟩⟩
    · simpa using (h₀ n (by omega)).1 hm
    · exact (h₁ n (by omega)).1 hm

/-- **Interface for the geometry side.** If a property `P t` agrees with a sentence of the
restricted height arithmetic for all `t ≥ t₀`, then `{t | P t}` is eventually periodic. -/
theorem eventuallyPeriodic_of_holds (P : ℕ → Prop) (φ : HSentence T) (t₀ : ℕ)
    (h : ∀ t, t₀ ≤ t → (P t ↔ Holds lo hi t φ)) : EventuallyPeriodic {t | P t} :=
  eventuallyPeriodic_of_eventually_iff (eventuallyPeriodic_holds lo hi φ) t₀ fun t ht => h t ht

end R002.Claude3Fold
