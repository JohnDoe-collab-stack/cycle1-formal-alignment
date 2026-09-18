import ConstitutiveSearch.ClosureSearchCosts
import Tests.ClosureSearchRegression

namespace ConstitutiveSearch.Tests.ClosureSearchCostsRegression

open ClosureSearchRegression

theorem primitiveBudget_fuelOne :
    closurePrimitiveQueryBudget 1 1 = 1 := by
  rfl

theorem primitiveBudget_fuelTwo :
    closurePrimitiveQueryBudget 1 2 = 3 := by
  rfl

theorem compositionBudget_fuelOne :
    closureCompositionCandidateBudget 1 1 = 1 := by
  rfl

theorem compositionBudget_fuelTwo :
    closureCompositionCandidateBudget 1 2 = 3 := by
  rfl

theorem fuelTwo_primitive_within_budget :
    fuelTwo.stats.primitiveQueries ≤
      closurePrimitiveQueryBudget 1 2 := by
  exact
    searchTransportClosureBounded_primitiveQueries_le
      primitiveSearch
      [DemoState.b]
      2
      DemoState.a
      DemoState.c

theorem fuelTwo_candidates_within_budget :
    fuelTwo.stats.compositionCandidates ≤
      closureCompositionCandidateBudget 1 2 := by
  exact
    searchTransportClosureBounded_compositionCandidates_le
      primitiveSearch
      [DemoState.b]
      2
      DemoState.a
      DemoState.c

theorem fuelTwo_primitive_budget_tight :
    fuelTwo.stats.primitiveQueries =
      closurePrimitiveQueryBudget 1 2 := by
  rfl

end ConstitutiveSearch.Tests.ClosureSearchCostsRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchCostsRegression.primitiveBudget_fuelOne
#print axioms ConstitutiveSearch.Tests.ClosureSearchCostsRegression.primitiveBudget_fuelTwo
#print axioms ConstitutiveSearch.Tests.ClosureSearchCostsRegression.compositionBudget_fuelOne
#print axioms ConstitutiveSearch.Tests.ClosureSearchCostsRegression.compositionBudget_fuelTwo
#print axioms ConstitutiveSearch.Tests.ClosureSearchCostsRegression.fuelTwo_primitive_within_budget
#print axioms ConstitutiveSearch.Tests.ClosureSearchCostsRegression.fuelTwo_candidates_within_budget
#print axioms ConstitutiveSearch.Tests.ClosureSearchCostsRegression.fuelTwo_primitive_budget_tight
/- AXIOM_AUDIT_END -/
