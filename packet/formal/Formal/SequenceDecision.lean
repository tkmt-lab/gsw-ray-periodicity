import Mathlib.Data.Nat.Find
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-! Logical core of R002's forced-sequence decision.
Geometry, the enumeration of initial triangles, and the Python event calculation
are not formalized here. Indices start at zero; prefixes include their endpoint. -/

namespace R002

variable {α : Type*}

def RepeatAt (p : ℕ → α) (j : ℕ) : Prop := ∃ i < j, p i = p j

def PrefixInjective (p : ℕ → α) (n : ℕ) : Prop :=
  ∀ i ≤ n, ∀ j ≤ n, p i = p j → i = j

def FirstRepeat (p : ℕ → α) (r : ℕ) : Prop :=
  RepeatAt p r ∧ ∀ j < r, ¬ RepeatAt p j

def FirstEndpoint (legal : ℕ → Prop) (e : ℕ) : Prop :=
  legal e ∧ ∀ j, legal j → e ≤ j

def ValidEnd (p : ℕ → α) (legal : ℕ → Prop) (n : ℕ) : Prop :=
  legal n ∧ PrefixInjective p n

theorem prefix_injective_iff_no_repeat (p : ℕ → α) (n : ℕ) :
    PrefixInjective p n ↔ ∀ j ≤ n, ¬ RepeatAt p j := by
  constructor
  · intro h j hj ⟨i, hij, heq⟩
    have := h i (by omega) j hj heq
    omega
  · intro h i hi j hj heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact h j hj ⟨i, hij, heq⟩
    · exact h i hi ⟨j, hji, heq.symm⟩

theorem prefix_injective_iff_before_first_repeat (p : ℕ → α) (r n : ℕ)
    (hr : FirstRepeat p r) : PrefixInjective p n ↔ n < r := by
  rw [prefix_injective_iff_no_repeat]
  constructor
  · intro h
    by_contra hn
    exact h r (by omega) hr.1
  · intro hn j hj
    exact hr.2 j (by omega)

theorem valid_end_iff_before_first_repeat (p : ℕ → α) (legal : ℕ → Prop)
    (r n : ℕ) (hr : FirstRepeat p r) :
    ValidEnd p legal n ↔ legal n ∧ n < r := by
  simp only [ValidEnd, prefix_injective_iff_before_first_repeat p r n hr]

/-- Equality E = R is a failure, even when the repeated point is a legal endpoint. -/
theorem valid_exists_iff_first_endpoint_lt_repeat (p : ℕ → α)
    (legal : ℕ → Prop) (r e : ℕ) (hr : FirstRepeat p r)
    (he : FirstEndpoint legal e) :
    (∃ n, ValidEnd p legal n) ↔ e < r := by
  constructor
  · rintro ⟨n, hn⟩
    have hn' := (valid_end_iff_before_first_repeat p legal r n hr).mp hn
    exact lt_of_le_of_lt (he.2 n hn'.1) hn'.2
  · intro h
    exact ⟨e, (valid_end_iff_before_first_repeat p legal r e hr).mpr ⟨he.1, h⟩⟩

/-- This version includes the case where no legal endpoint exists anywhere. -/
theorem valid_exists_iff_bounded_endpoint (p : ℕ → α) (legal : ℕ → Prop)
    (r : ℕ) (hr : FirstRepeat p r) :
    (∃ n, ValidEnd p legal n) ↔ ∃ e < r, legal e := by
  constructor
  · rintro ⟨n, hn⟩
    have h := (valid_end_iff_before_first_repeat p legal r n hr).mp hn
    exact ⟨n, h.2, h.1⟩
  · rintro ⟨e, her, he⟩
    exact ⟨e, (valid_end_iff_before_first_repeat p legal r e hr).mpr ⟨he, her⟩⟩

theorem no_valid_end_when_no_endpoint (p : ℕ → α) (legal : ℕ → Prop)
    (h : ∀ n, ¬ legal n) : ¬ ∃ n, ValidEnd p legal n := by
  rintro ⟨n, hn⟩
  exact h n hn.1

theorem first_endpoint_exists (legal : ℕ → Prop) (h : ∃ n, legal n) :
    ∃ e, FirstEndpoint legal e := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun _ hn => Nat.find_min' h hn⟩

/-- Pigeonhole plus minimization gives a repeat by index |α|, without a geometric
assumption and without assuming the existence of a repeat as an axiom. -/
theorem first_repeat_exists_bounded [Fintype α] (p : ℕ → α) :
    ∃ r ≤ Fintype.card α, FirstRepeat p r := by
  classical
  have hn : ¬ PrefixInjective p (Fintype.card α) := by
    intro h
    have hi : Function.Injective (fun i : Fin (Fintype.card α + 1) => p i.val) := by
      intro i j hij
      apply Fin.ext
      exact h i.val (by omega) j.val (by omega) hij
    have hc := Fintype.card_le_of_injective _ hi
    simp only [Fintype.card_fin] at hc
    omega
  have hb : ∃ j ≤ Fintype.card α, RepeatAt p j := by
    by_contra h
    apply hn
    rw [prefix_injective_iff_no_repeat]
    intro j hj hr
    exact h ⟨j, hj, hr⟩
  obtain ⟨j, hj, hjr⟩ := hb
  have hex : ∃ r, RepeatAt p r := ⟨j, hjr⟩
  exact ⟨Nat.find hex, le_trans (Nat.find_min' hex hjr) hj,
    Nat.find_spec hex, fun _ hlt => Nat.find_min hex hlt⟩

/-- The literal endpoint conditions used by the unformalized graph adapter. -/
def LegalConeEndpoint (cone : α → Prop) (p : ℕ → α) (j : ℕ) : Prop :=
  3 ≤ j ∧ j % 2 = 1 ∧ cone (p j) ∧ ¬ cone (p (j - 1))

theorem legal_cone_endpoint_has_even_length (cone : α → Prop) (p : ℕ → α)
    (j : ℕ) (h : LegalConeEndpoint cone p j) :
    4 ≤ j + 1 ∧ (j + 1) % 2 = 0 := by
  obtain ⟨hmin, hodd, _, _⟩ := h
  omega

#print axioms prefix_injective_iff_before_first_repeat
#print axioms valid_exists_iff_first_endpoint_lt_repeat
#print axioms valid_exists_iff_bounded_endpoint
#print axioms first_repeat_exists_bounded
#print axioms legal_cone_endpoint_has_even_length

end R002
