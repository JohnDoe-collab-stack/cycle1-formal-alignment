import ConstitutiveSearch.ClosureSearchGrowingCandidatesLogFuelSeparator

namespace ConstitutiveSearch.Tests.ClosureSearchGrowingCandidatesLogFuelSeparatorRegression

open ConstitutiveSearch

theorem inputThree :
    growingCandidatesLogInputBits 3 = 16 := by
  rfl

theorem candidatesThree :
    growingCandidatesLogCandidateCount 3 = 16 := by
  rfl

theorem fuelThree :
    growingCandidatesLogFuel 3 = 4 := by
  rfl

theorem fuelIsLogThree :
    growingCandidatesLogFuel 3 =
      Nat.log2
        (growingCandidatesLogInputBits 3) :=
  growingCandidatesLogFuel_eq_log 3

theorem candidateCountInputPolynomial :
    InputPolynomiallyBounded
      growingCandidatesLogInputBits
      growingCandidatesLogCandidateCount :=
  growingCandidatesLogCandidateCount_inputPolynomiallyBounded

theorem fuelUnbounded :
    ∀ cap : Nat,
      ∃ n : Nat,
        cap <
          growingCandidatesLogFuel n :=
  growingCandidatesLogFuel_unbounded

theorem primitiveNotInputPolynomial :
    ¬
      InputPolynomiallyBounded
        growingCandidatesLogInputBits
        (fun n =>
          closurePrimitiveQueryBudget
            (growingCandidatesLogCandidateCount n)
            (growingCandidatesLogFuel n)) :=
  growingCandidatesLogPrimitive_not_inputPolynomiallyBounded

theorem compositionNotInputPolynomial :
    ¬
      InputPolynomiallyBounded
        growingCandidatesLogInputBits
        (fun n =>
          closureCompositionCandidateBudget
            (growingCandidatesLogCandidateCount n)
            (growingCandidatesLogFuel n)) :=
  growingCandidatesLogComposition_not_inputPolynomiallyBounded

end ConstitutiveSearch.Tests.ClosureSearchGrowingCandidatesLogFuelSeparatorRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowingCandidatesLogFuelSeparatorRegression.inputThree
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowingCandidatesLogFuelSeparatorRegression.candidatesThree
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowingCandidatesLogFuelSeparatorRegression.fuelThree
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowingCandidatesLogFuelSeparatorRegression.fuelIsLogThree
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowingCandidatesLogFuelSeparatorRegression.candidateCountInputPolynomial
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowingCandidatesLogFuelSeparatorRegression.fuelUnbounded
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowingCandidatesLogFuelSeparatorRegression.primitiveNotInputPolynomial
#print axioms ConstitutiveSearch.Tests.ClosureSearchGrowingCandidatesLogFuelSeparatorRegression.compositionNotInputPolynomial
/- AXIOM_AUDIT_END -/
