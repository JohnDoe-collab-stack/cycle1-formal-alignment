import ConstitutiveSearch.SAT.SequentialGlobalClosureSeparator

namespace ConstitutiveSearch.Tests.SATSequentialGlobalClosureSeparatorRegression

open ConstitutiveSearch
open SAT

abbrev DemoGenerator
    (_source _target : Nat) : Type :=
  Unit

def alwaysPrimitive :
    RelationSearch DemoGenerator :=
  { find := fun _source _target =>
      some () }

theorem primitiveHitShortCircuit :
    let run :=
      searchTransportClosureBounded
        alwaysPrimitive
        [0, 1, 2, 3]
        7
        0
        3
    run.stats.primitiveQueries = 1 ∧
      run.stats.compositionCandidates = 0 := by
  exact
    searchTransportClosureBounded_primitiveHit_stats
      alwaysPrimitive
      [0, 1, 2, 3]
      7
      0
      3
      (by decide)
      (by
        intro impossible
        cases impossible)

theorem separatorExists :
    SequentialGlobalClosureAccountingSeparator :=
  explicitFamilySequentialGlobalClosureAccountingSeparator

theorem sequentialRelationFind3 :
    (explicitFamilyComplexityCounts 3).relationFindCalls = 6 := by
  rfl

theorem sequentialClosureZero3 :
    (explicitFamilyComplexityCounts 3).closurePrimitiveQueries = 0 ∧
      (explicitFamilyComplexityCounts 3).closureCompositionCandidates = 0 := by
  exact ⟨rfl, rfl⟩

theorem globalSchedule3 :
    (explicitFamilyTrajectoryClosureCandidates 3).length = 6 ∧
      explicitFamilyTrajectoryClosureFuel 3 = 3 := by
  exact
    ⟨explicitFamilyTrajectoryClosureCandidates_length 3,
      explicitFamilyTrajectoryClosureFuel_eq 3⟩

theorem globalPrimitiveBudgetNotPolynomial :
    ¬
      InputPolynomiallyBounded
        explicitFamilyInputBitSize
        explicitFamilyTrajectoryPrimitiveClosureBudget :=
  explicitFamilyTrajectoryPrimitiveClosureBudget_not_inputPolynomiallyBounded

theorem globalCompositionBudgetNotPolynomial :
    ¬
      InputPolynomiallyBounded
        explicitFamilyInputBitSize
        explicitFamilyTrajectoryCompositionClosureBudget :=
  explicitFamilyTrajectoryCompositionClosureBudget_not_inputPolynomiallyBounded

end ConstitutiveSearch.Tests.SATSequentialGlobalClosureSeparatorRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATSequentialGlobalClosureSeparatorRegression.alwaysPrimitive
#print axioms ConstitutiveSearch.Tests.SATSequentialGlobalClosureSeparatorRegression.primitiveHitShortCircuit
#print axioms ConstitutiveSearch.Tests.SATSequentialGlobalClosureSeparatorRegression.separatorExists
#print axioms ConstitutiveSearch.Tests.SATSequentialGlobalClosureSeparatorRegression.sequentialRelationFind3
#print axioms ConstitutiveSearch.Tests.SATSequentialGlobalClosureSeparatorRegression.sequentialClosureZero3
#print axioms ConstitutiveSearch.Tests.SATSequentialGlobalClosureSeparatorRegression.globalSchedule3
#print axioms ConstitutiveSearch.Tests.SATSequentialGlobalClosureSeparatorRegression.globalPrimitiveBudgetNotPolynomial
#print axioms ConstitutiveSearch.Tests.SATSequentialGlobalClosureSeparatorRegression.globalCompositionBudgetNotPolynomial
/- AXIOM_AUDIT_END -/
