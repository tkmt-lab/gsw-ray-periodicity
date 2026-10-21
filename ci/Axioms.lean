import Formal.Claude2FamilyRays
import Formal.Claude2FamilyExamples
import Formal.Claude2K3Sufficient
import Formal.ClaudeCorRays
import Formal.Claude3ComparatorSolution
import Formal.Claude3Residue
import Formal.Claude4K3ComparatorSolution
import Formal.Claude4C1ComparatorSolution
import Formal.Claude5O2ComparatorSolution
import Formal.Claude5E10ComparatorSolution

/-! Prints the axioms of the main declarations of this release.
CI fails unless every line lists only `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms Claude2.k3_ray_all
#print axioms Claude2.e10_ray_all
#print axioms Claude2.b2_ray_all
#print axioms Claude2.c1_ray_all
#print axioms Claude2.a1_ray_all
#print axioms Claude2.a2_ray_all
#print axioms Claude2.a3_ray
#print axioms Claude2.k3_example
#print axioms Claude2.e10_example
#print axioms Claude2K3.k3_sufficient
#print axioms ClaudeCor.criterion_ray
#print axioms ClaudeChallenge2.main
#print axioms ClaudeChallenge2.State.main_statement
#print axioms ClaudeChallenge2.main_residue
#print axioms ClaudeChallengeK3.main
#print axioms Claude4K3.k3_statement
#print axioms Claude4K3.noThree
#print axioms ClaudeChallengeC1.classification
#print axioms ClaudeChallengeC1.main
#print axioms ClaudeChallengeO2.classification
#print axioms ClaudeChallengeO2.main
#print axioms ClaudeChallengeE10.classification
#print axioms ClaudeChallengeE10.main
