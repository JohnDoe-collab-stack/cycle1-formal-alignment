import ConstitutiveSearch.SAT.TrajectoryDerivedClosureComplexity

namespace ConstitutiveSearch.Tests.SATTrajectoryDerivedClosureComplexityRegression

open ConstitutiveSearch
open SAT

theorem primitiveSchedule3 :
    explicitFamilyTrajectoryPrimitiveClosureBudget 3 =
      closurePrimitiveQueryBudget 6 3 :=
  explicitFamilyTrajectoryPrimitiveClosureBudget_eq 3

theorem compositionSchedule3 :
    explicitFamilyTrajectoryCompositionClosureBudget 3 =
      closureCompositionCandidateBudget 6 3 :=
  explicitFamilyTrajectoryCompositionClosureBudget_eq 3

theorem primitiveOneCandidateBelow3 :
    closurePrimitiveQueryBudget 1 3 ≤
      explicitFamilyTrajectoryPrimitiveClosureBudget 3 :=
  oneCandidatePrimitive_le_explicitFamilyTrajectoryBudget 3

theorem compositionOneCandidateBelow3 :
    closureCompositionCandidateBudget 1 3 ≤
      explicitFamilyTrajectoryCompositionClosureBudget 3 :=
  oneCandidateComposition_le_explicitFamilyTrajectoryBudget 3

theorem primitiveDerivedNotPolynomial :
    ¬
      PolynomiallyBounded
        explicitFamilyTrajectoryPrimitiveClosureBudget :=
  explicitFamilyTrajectoryPrimitiveClosureBudget_not_polynomiallyBounded

theorem compositionDerivedNotPolynomial :
    ¬
      PolynomiallyBounded
        explicitFamilyTrajectoryCompositionClosureBudget :=
  explicitFamilyTrajectoryCompositionClosureBudget_not_polynomiallyBounded

theorem primitiveDerivedNotInputPolynomial :
    ¬
      InputPolynomiallyBounded
        explicitFamilyInputBitSize
        explicitFamilyTrajectoryPrimitiveClosureBudget :=
  explicitFamilyTrajectoryPrimitiveClosureBudget_not_inputPolynomiallyBounded

theorem compositionDerivedNotInputPolynomial :
    ¬
      InputPolynomiallyBounded
        explicitFamilyInputBitSize
        explicitFamilyTrajectoryCompositionClosureBudget :=
  explicitFamilyTrajectoryCompositionClosureBudget_not_inputPolynomiallyBounded

end ConstitutiveSearch.Tests.SATTrajectoryDerivedClosureComplexityRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATTrajectoryDerivedClosureComplexityRegression.primitiveSchedule3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryDerivedClosureComplexityRegression.compositionSchedule3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryDerivedClosureComplexityRegression.primitiveOneCandidateBelow3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryDerivedClosureComplexityRegression.compositionOneCandidateBelow3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryDerivedClosureComplexityRegression.primitiveDerivedNotPolynomial
#print axioms ConstitutiveSearch.Tests.SATTrajectoryDerivedClosureComplexityRegression.compositionDerivedNotPolynomial
#print axioms ConstitutiveSearch.Tests.SATTrajectoryDerivedClosureComplexityRegression.primitiveDerivedNotInputPolynomial
#print axioms ConstitutiveSearch.Tests.SATTrajectoryDerivedClosureComplexityRegression.compositionDerivedNotInputPolynomial
/- AXIOM_AUDIT_END -/
