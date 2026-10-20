import Formal.Claude2AlignedSpec
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-!
# Sanity of the K3 specification: every label-paired edge is glued, for all `r, s`

`Claude2AlignedSpec.lean` defines the K3 surface by gluing edges whose labels are paired
(`a → b` with `b → a`).  `Glue` is an existence statement, so if some paired edges had different
lengths (or were set up with the wrong orientation), they would silently stay unglued.  This file
rules that out for all integer `r, s`:

* `k3_pairs`          : (decidable, labels only) every label-paired directed edge occurs in the
                        42-entry table `k3GlueTable`;
* `k3_table_glue`     : for every table entry and all `r s : ℤ`, the stated rotation `rotN m`
                        with the forced translation glues the two edges;
* `k3_glue_complete`  : hence every label-paired edge of `k3Sig r s` is glued.
-/

namespace Claude2Aligned

open ClaudeChallenge

theorem Sig.glue_of (S : Sig) {g f : Fin S.N} {i j m : ℕ}
    (hi : i < (S.poly g).length) (hj : j < (S.poly f).length)
    (h1 : S.lb g i = S.lb f (j + 1)) (h2 : S.lb g (i + 1) = S.lb f j)
    (h : rotN m (S.pt g (i + 1)) + (S.pt f (j + 1) - rotN m (S.pt g i)) = S.pt f j) :
    ∃ τ, S.Glue g i f j m τ :=
  ⟨_, hi, hj, h1, h2, by abel, h⟩

/-- The 42 directed edge gluings of K3: `(g, i, f, j, m)`, computed by the Python mirror. -/
def k3GlueTable : List (Fin 11 × ℕ × Fin 11 × ℕ × ℕ) :=
  [(0, 0, 8, 1, 4), (0, 1, 3, 2, 5), (0, 2, 10, 0, 5), (1, 0, 9, 1, 4), (1, 1, 3, 0, 1),
   (1, 2, 8, 0, 5), (2, 0, 10, 1, 4), (2, 1, 3, 1, 3), (2, 2, 9, 0, 5), (3, 0, 1, 1, 5),
   (3, 1, 2, 1, 3), (3, 2, 0, 1, 1), (4, 0, 7, 2, 1), (4, 1, 8, 3, 4), (4, 2, 10, 4, 3),
   (5, 0, 7, 1, 5), (5, 1, 9, 3, 4), (5, 2, 8, 4, 3), (6, 0, 7, 0, 3), (6, 1, 10, 3, 4),
   (6, 2, 9, 4, 3), (7, 0, 6, 0, 3), (7, 1, 5, 0, 1), (7, 2, 4, 0, 5), (8, 0, 1, 2, 1),
   (8, 1, 0, 0, 2), (8, 2, 10, 5, 0), (8, 3, 4, 1, 2), (8, 4, 5, 2, 3), (8, 5, 9, 2, 0),
   (9, 0, 2, 2, 1), (9, 1, 1, 0, 2), (9, 2, 8, 5, 0), (9, 3, 5, 1, 2), (9, 4, 6, 2, 3),
   (9, 5, 10, 2, 0), (10, 0, 0, 2, 1), (10, 1, 2, 0, 2), (10, 2, 9, 5, 0), (10, 3, 6, 1, 2),
   (10, 4, 4, 2, 3), (10, 5, 8, 2, 0)]

/-- K3 labels, independent of `r, s`. -/
def k3lb (g : Fin 11) (i : ℕ) : ℕ := (k3Lab g).getD (i % (k3Lab g).length) 0

theorem k3Sig_lb (r s : ℤ) (g : Fin 11) (i : ℕ) : (k3Sig r s).lb g i = k3lb g i := rfl

theorem k3_pairs : ∀ g : Fin 11, ∀ i : Fin 6, ∀ f : Fin 11, ∀ j : Fin 6,
    i.val < (k3Lab g).length → j.val < (k3Lab f).length →
    k3lb g i = k3lb f (j + 1) → k3lb g (i + 1) = k3lb f j →
    (g, i.val, f, j.val) ∈ k3GlueTable.map (fun e => (e.1, e.2.1, e.2.2.1, e.2.2.2.1)) := by
  decide

theorem k3_poly_length (r s : ℤ) (g : Fin 11) : (k3Poly r s g).length = (k3Lab g).length := by
  fin_cases g <;> rfl

theorem k3_table_glue (r s : ℤ) :
    ∀ e ∈ k3GlueTable, ∃ τ, (k3Sig r s).Glue e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 τ := by
  rw [k3GlueTable]
  simp only [List.forall_mem_cons]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun _ h => by simp at h⟩ <;>
  refine Sig.glue_of (k3Sig r s) ?_ ?_ ?_ ?_ ?_ <;>
  first
    | (rw [k3Sig_lb, k3Sig_lb]; decide)
    | (simp [Sig.pt, k3Sig, k3Poly, walk, rotN, rot, Prod.ext_iff] <;> omega)

/-- Every label-paired directed edge of `k3Sig r s` is glued (for all integers `r, s`). -/
theorem k3_glue_complete (r s : ℤ) (g : Fin 11) (i : ℕ) (f : Fin 11) (j : ℕ)
    (hi : i < ((k3Sig r s).poly g).length) (hj : j < ((k3Sig r s).poly f).length)
    (h1 : (k3Sig r s).lb g i = (k3Sig r s).lb f (j + 1))
    (h2 : (k3Sig r s).lb g (i + 1) = (k3Sig r s).lb f j) :
    ∃ m τ, (k3Sig r s).Glue g i f j m τ := by
  rw [k3Sig_lb, k3Sig_lb] at h1 h2
  have hi' : i < (k3Lab g).length := by rw [← k3_poly_length r s g]; exact hi
  have hj' : j < (k3Lab f).length := by rw [← k3_poly_length r s f]; exact hj
  have hi6 : i < 6 := by have : (k3Lab g).length ≤ 6 := by fin_cases g <;> decide
                         omega
  have hj6 : j < 6 := by have : (k3Lab f).length ≤ 6 := by fin_cases f <;> decide
                         omega
  have hm := k3_pairs g ⟨i, hi6⟩ f ⟨j, hj6⟩ hi' hj' h1 h2
  obtain ⟨e, he, hee⟩ := List.mem_map.1 hm
  obtain ⟨τ, hτ⟩ := k3_table_glue r s e he
  simp only [Prod.mk.injEq] at hee
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hee
  exact ⟨_, τ, hτ⟩

end Claude2Aligned

#print axioms Claude2Aligned.k3_glue_complete
