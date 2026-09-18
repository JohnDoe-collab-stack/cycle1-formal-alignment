import ConstitutiveSearch.ClosureSearchGrowth

namespace ConstitutiveSearch.Tests.ClosureSearchGrowthRegression

theorem primitiveOneFuel4 :
    closurePrimitiveQueryBudget 1 4 = 15 := by
  rfl

theorem compositionOneFuel4 :
    closureCompositionCandidateBudget 1 4 = 15 := by
  rfl

theorem primitiveFuelTwo3Candidates :
    closurePrimitiveQueryBudget 3 2 = 7 := by
  rfl

theorem compositionFuelTwo3Candidates :
    closureCompositionCandidateBudget 3 2 = 21 := by
  rfl

theorem primitiveOneRecurrence3 :
    closurePrimitiveQueryBudget 1 4 =
      closurePrimitiveQueryBudget 1 3 +
        closurePrimitiveQueryBudget 1 3 +
        1 :=
  closurePrimitiveQueryBudget_one_succ 3

theorem compositionOneRecurrence3 :
    closureCompositionCandidateBudget 1 4 =
      closureCompositionCandidateBudget 1 3 +
        closureCompositionCandidateBudget 1 3 +
        1 :=
  closureCompositionCandidateBudget_one_succ 3

end ConstitutiveSearch.Tests.ClosureSearchGrowthRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowthRegression.primitiveOneFuel4
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowthRegression.compositionOneFuel4
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowthRegression.primitiveFuelTwo3Candidates
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowthRegression.compositionFuelTwo3Candidates
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowthRegression.primitiveOneRecurrence3
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowthRegression.compositionOneRecurrence3
/- AXIOM_AUDIT_END -/
