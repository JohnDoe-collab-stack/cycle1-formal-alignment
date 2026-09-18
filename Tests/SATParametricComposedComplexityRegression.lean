import ConstitutiveSearch.SAT.ParametricComposedComplexity

namespace ConstitutiveSearch.Tests.SATParametricComposedComplexityRegression

open ConstitutiveSearch
open SAT

theorem evidence3 :
    ComposedClosurePhaseEvidence 3 :=
  composedClosurePhaseEvidence 3

theorem frontierSlots3 :
    (composedClosurePhaseCounts 3).frontierSlots = 2 := by
  rfl

theorem certificateAtoms3 :
    (composedClosurePhaseCounts 3).certificateAtoms = 2 := by
  rfl

theorem primitiveQueries3 :
    (composedClosurePhaseCounts 3).closurePrimitiveQueries = 3 := by
  rfl

theorem compositionCandidates3 :
    (composedClosurePhaseCounts 3).closureCompositionCandidates = 1 := by
  rfl

theorem phaseCostEqBudget3
    (costs : AtomicCosts) :
    composedClosurePhaseChargedCost 3 costs =
      composedClosurePhaseBudget costs :=
  composedClosurePhaseChargedCost_eq_budget 3 costs

end ConstitutiveSearch.Tests.SATParametricComposedComplexityRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATParametricComposedComplexityRegression.evidence3
#print axioms ConstitutiveSearch.Tests.SATParametricComposedComplexityRegression.frontierSlots3
#print axioms ConstitutiveSearch.Tests.SATParametricComposedComplexityRegression.certificateAtoms3
#print axioms ConstitutiveSearch.Tests.SATParametricComposedComplexityRegression.primitiveQueries3
#print axioms ConstitutiveSearch.Tests.SATParametricComposedComplexityRegression.compositionCandidates3
#print axioms ConstitutiveSearch.Tests.SATParametricComposedComplexityRegression.phaseCostEqBudget3
/- AXIOM_AUDIT_END -/
