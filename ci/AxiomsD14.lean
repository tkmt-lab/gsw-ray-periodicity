import Formal.Claude5D14ComparatorSolution

/-! Prints the axioms of the D14 declarations of this release.
This is a separate file because the O2 and D14 proofs each define a local helper tactic named
`peq`, so one file cannot import both solution modules. CI fails unless every line lists only
`propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms ClaudeChallengeD14.main
#print axioms Claude5D14.d14_no_path
