import ConstitutiveSearch.SAT.ParametricComposedBitComplexity

namespace ConstitutiveSearch.Tests.SATParametricComposedBitComplexityRegression

open ConstitutiveSearch
open SAT

theorem historyLength3 :
    (composedSource 3).context.decisions.length = 5 :=
  composedState_decisions_length 3 false false

theorem firstWitnessBound3 :
    (composedSourceMiddleWitness 3).binarySize ≤
      composedCertificateAtomBinaryBudget 3 :=
  composedSourceMiddleWitness_binarySize_le_budget 3

theorem secondWitnessBound3 :
    (composedMiddleTargetWitness 3).binarySize ≤
      composedCertificateAtomBinaryBudget 3 :=
  composedMiddleTargetWitness_binarySize_le_budget 3

theorem sourceTargetFirstCharge3 :
    generatedFlipEqualityCharge
        (composedFirstVar 3)
        (composedSource 3)
        (composedTarget 3) ≤
      composedSingleFlipEqualityBinaryBudget 3 :=
  composedState_flipEqualityCharge_le_budget
    3
    (composedFirstVar 3)
    false
    false
    true
    true

theorem phaseRepresentationCostEqBudget3 :
    composedClosurePhaseRepresentationChargedCost 3 =
      composedClosurePhaseRepresentationBudget 3 :=
  composedClosurePhaseRepresentationChargedCost_eq_budget 3

end ConstitutiveSearch.Tests.SATParametricComposedBitComplexityRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATParametricComposedBitComplexityRegression.historyLength3
#print axioms ConstitutiveSearch.Tests.SATParametricComposedBitComplexityRegression.firstWitnessBound3
#print axioms ConstitutiveSearch.Tests.SATParametricComposedBitComplexityRegression.secondWitnessBound3
#print axioms ConstitutiveSearch.Tests.SATParametricComposedBitComplexityRegression.sourceTargetFirstCharge3
#print axioms ConstitutiveSearch.Tests.SATParametricComposedBitComplexityRegression.phaseRepresentationCostEqBudget3
/- AXIOM_AUDIT_END -/
