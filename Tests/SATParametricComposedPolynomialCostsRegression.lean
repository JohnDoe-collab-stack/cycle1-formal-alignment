import ConstitutiveSearch.SAT.ParametricComposedPolynomialCosts

namespace ConstitutiveSearch.Tests.SATParametricComposedPolynomialCostsRegression

open ConstitutiveSearch
open SAT

theorem historyBudget3 :
    composedHistoryBinaryBudget 3 =
      composedHistoryPolynomialBudget 3 :=
  composedHistoryBinaryBudget_eq_polynomial 3

theorem stateBudget3 :
    composedStateBinaryBudget 3 =
      composedStatePolynomialBudget 3 :=
  composedStateBinaryBudget_eq_polynomial 3

theorem queryBudget3 :
    composedPrimitiveQueryBinaryBudget 3 =
      composedPrimitiveQueryPolynomialBudget 3 :=
  composedPrimitiveQueryBinaryBudget_eq_polynomial 3

theorem phasePolynomial3 :
    composedClosurePhaseRepresentationChargedCost 3 =
      composedClosurePhaseRepresentationPolynomialBudget 3 :=
  composedClosurePhaseRepresentationChargedCost_eq_polynomial 3

theorem phaseInputIndexed3 :
    composedClosurePhaseRepresentationChargedCost 3 ≤
      composedClosurePhaseInputIndexedPolynomialBudget 3 :=
  composedClosurePhaseRepresentationChargedCost_le_inputIndexedPolynomial 3

end ConstitutiveSearch.Tests.SATParametricComposedPolynomialCostsRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATParametricComposedPolynomialCostsRegression.historyBudget3
#print axioms ConstitutiveSearch.Tests.SATParametricComposedPolynomialCostsRegression.stateBudget3
#print axioms ConstitutiveSearch.Tests.SATParametricComposedPolynomialCostsRegression.queryBudget3
#print axioms ConstitutiveSearch.Tests.SATParametricComposedPolynomialCostsRegression.phasePolynomial3
#print axioms ConstitutiveSearch.Tests.SATParametricComposedPolynomialCostsRegression.phaseInputIndexed3
/- AXIOM_AUDIT_END -/
