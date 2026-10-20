import Formal.Claude3SentSkel
import Formal.Claude3SentTail
import Formal.Claude3SentDb

/-!
# Theorem 1a, A: assembly

Written by a Claude worker (2026-10-20, Theorem 1a, parts G6/A).

* `main_statement_of_geo` : `GeoSentenceStatement → ClaudeChallenge2.MainStatement`, from the
  reduction theorem without connectivity (`reduction_core`, G5) and the folding theorem
  (`R002.Claude3Fold.eventuallyPeriodic_of_holds`, F).
* `main_statement_of_atoms` : the same from `∀ S, AtomsStatement S` (`geoSentence_of_atoms`).
* `main_statement_of_DbR` : the same from the definability of the last atom `DbR`
  (condition 3 (b)); all other atoms are proved definable (`atomsStatement_of_DbR`).
* `dbRStatement`, `geoSentenceStatement`, **`main_statement : ClaudeChallenge2.MainStatement`**.
-/

namespace ClaudeChallenge2.State

open ClaudeChallenge2 R002.Claude3Fold

/-- **Assembly.** The sentence statement (G6) implies Theorem 1a. -/
theorem main_statement_of_geo (hG : GeoSentenceStatement) : ClaudeChallenge2.MainStatement := by
  intro S t₁ hval
  obtain ⟨φ, t₂, hφ⟩ := hG S
  have hP : R002.Claude3Mso.EventuallyPeriodic {t | PathExists S t} :=
    eventuallyPeriodic_of_holds stLo stHi (PathExists S) φ (max t₁ t₂) fun t ht => by
      have h1 : t₁ ≤ t := le_of_max_le_left ht
      rw [reduction_core S t (hval t h1).1 (hval t h1).2]
      exact hφ t (le_of_max_le_right ht) (hval t h1).1 (hval t h1).2
  obtain ⟨t₀, P, hP0, hper⟩ := hP
  exact ⟨t₀, P, hP0, fun t ht => hper t ht⟩

/-- **Assembly from the atoms.** If the atomic predicates of the path conditions are
definable (`AtomsStatement`, see `Claude3SentPred`), Theorem 1a holds. -/
theorem main_statement_of_atoms (hAt : ∀ S : Sig, AtomsStatement S) :
    ClaudeChallenge2.MainStatement :=
  main_statement_of_geo (geoSentence_of_atoms hAt)

/-- **Assembly from the remaining gap** (`AtomsGap`: the atoms other than the trivial one). -/
theorem main_statement_of_gap (hGap : ∀ S : Sig, AtomsGap S) : ClaudeChallenge2.MainStatement :=
  main_statement_of_atoms fun S => atomsStatement_of_gap (hGap S)

/-- All transition atoms other than condition 3 (b). -/
theorem def2_pt_all {S : Sig} (q : QIdx) : Def2 S (PT q) := by
  cases q with
  | q0 => exact def2_pt_q0
  | qT => exact def2_pt_qT
  | qP b => exact def2_pt_par _ (by simp) (by simp)
  | qE => exact def2_pt_par _ (by simp) (by simp)
  | qL => exact def2_pt_qL

/-- Every atom except condition 3 (b) is definable, so the atoms statement reduces to `DbR`. -/
theorem atomsStatement_of_DbR {S : Sig} (hb : Def2 S DbR) : AtomsStatement S :=
  ⟨def2_DaR, hb, def2_DcR, def1_E1P, fun q => ⟨def1_pr_all q, def2_pt_all q⟩⟩

/-- **The remaining gap**: condition 3 (b) along a transition (`DbR`) is definable. -/
def DbRStatement : Prop := ∀ S : Sig, Def2 S DbR

/-- **Assembly from the last atom** (condition 3 (b), `DbR`). -/
theorem main_statement_of_DbR (hb : DbRStatement) : ClaudeChallenge2.MainStatement :=
  main_statement_of_atoms fun S => atomsStatement_of_DbR (hb S)

/-- **G6.** The remaining atom is definable. -/
theorem dbRStatement : DbRStatement := fun _ => def2_DbR

/-- **G6.** The path sentence exists. -/
theorem geoSentenceStatement : GeoSentenceStatement :=
  geoSentence_of_atoms fun _ => atomsStatement_of_DbR def2_DbR

/-- **Theorem 1a** (`ClaudeChallenge2.MainStatement`, specification version 2). -/
theorem main_statement : ClaudeChallenge2.MainStatement :=
  main_statement_of_geo geoSentenceStatement

end ClaudeChallenge2.State
