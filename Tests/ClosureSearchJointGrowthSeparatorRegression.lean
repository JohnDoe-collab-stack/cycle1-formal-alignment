import ConstitutiveSearch.ClosureSearchJointGrowthSeparator

namespace ConstitutiveSearch.Tests.ClosureSearchJointGrowthSeparatorRegression

open ConstitutiveSearch

theorem candidateEqualsInputFour :
    jointHardCandidateCount 4 =
      jointHardInputBits 4 :=
  jointHardCandidateCount_eq_input 4

theorem fuelEqualsLogFour :
    jointHardFuel 4 =
      Nat.log2 (jointHardInputBits 4) :=
  jointHardFuel_eq_log2Input 4

theorem primitiveBudgetNotPolynomial :
    ¬
      InputPolynomiallyBounded
        jointHardInputBits
        (fun n =>
          closurePrimitiveQueryBudget
            (jointHardCandidateCount n)
            (jointHardFuel n)) :=
  jointHardPrimitive_not_inputPolynomiallyBounded

theorem compositionBudgetNotPolynomial :
    ¬
      InputPolynomiallyBounded
        jointHardInputBits
        (fun n =>
          closureCompositionCandidateBudget
            (jointHardCandidateCount n)
            (jointHardFuel n)) :=
  jointHardComposition_not_inputPolynomiallyBounded

end ConstitutiveSearch.Tests.ClosureSearchJointGrowthSeparatorRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchJointGrowthSeparatorRegression.candidateEqualsInputFour
#print axioms ConstitutiveSearch.Tests.ClosureSearchJointGrowthSeparatorRegression.fuelEqualsLogFour
#print axioms ConstitutiveSearch.Tests.ClosureSearchJointGrowthSeparatorRegression.primitiveBudgetNotPolynomial
#print axioms ConstitutiveSearch.Tests.ClosureSearchJointGrowthSeparatorRegression.compositionBudgetNotPolynomial
/- AXIOM_AUDIT_END -/
