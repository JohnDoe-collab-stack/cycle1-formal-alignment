import ConstitutiveSearch.ClosureSearchJointGrowthPolynomial

namespace ConstitutiveSearch.Tests.ClosureSearchJointGrowthPolynomialRegression

open ConstitutiveSearch

theorem bitWidthThree :
    closureCandidateBitWidth 3 = 4 := by
  rfl

theorem witnessCandidateUnbounded :
    ∀ cap : Nat,
      ∃ n : Nat,
        cap <
          jointGrowingCandidateCount n :=
  jointGrowingCandidateCount_unbounded

theorem witnessFuelUnbounded :
    ∀ cap : Nat,
      ∃ n : Nat,
        cap <
          jointGrowingFuel n :=
  jointGrowingFuel_unbounded

theorem witnessJointCriterion
    (n : Nat) :
    closureCandidateBitWidth
          (jointGrowingCandidateCount n) *
        jointGrowingFuel n ≤
      Nat.log2
        (jointGrowingInputBits n) := by
  have h :=
    jointGrowing_jointLe n
  simpa only [Nat.one_mul] using h

theorem witnessPrimitiveLinear :
    InputPolynomiallyBounded
      jointGrowingInputBits
      (fun n =>
        closurePrimitiveQueryBudget
          (jointGrowingCandidateCount n)
          (jointGrowingFuel n)) :=
  jointGrowingPrimitive_inputPolynomiallyBounded

theorem witnessCompositionLinear :
    InputPolynomiallyBounded
      jointGrowingInputBits
      (fun n =>
        closureCompositionCandidateBudget
          (jointGrowingCandidateCount n)
          (jointGrowingFuel n)) :=
  jointGrowingComposition_inputPolynomiallyBounded

end ConstitutiveSearch.Tests.ClosureSearchJointGrowthPolynomialRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchJointGrowthPolynomialRegression.bitWidthThree
#print axioms ConstitutiveSearch.Tests.ClosureSearchJointGrowthPolynomialRegression.witnessCandidateUnbounded
#print axioms ConstitutiveSearch.Tests.ClosureSearchJointGrowthPolynomialRegression.witnessFuelUnbounded
#print axioms ConstitutiveSearch.Tests.ClosureSearchJointGrowthPolynomialRegression.witnessJointCriterion
#print axioms ConstitutiveSearch.Tests.ClosureSearchJointGrowthPolynomialRegression.witnessPrimitiveLinear
#print axioms ConstitutiveSearch.Tests.ClosureSearchJointGrowthPolynomialRegression.witnessCompositionLinear
/- AXIOM_AUDIT_END -/
