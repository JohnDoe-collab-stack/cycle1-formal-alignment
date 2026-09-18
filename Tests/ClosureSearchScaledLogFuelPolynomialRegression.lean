import ConstitutiveSearch.ClosureSearchScaledLogFuelPolynomial

namespace ConstitutiveSearch.Tests.ClosureSearchScaledLogFuelPolynomialRegression

open ConstitutiveSearch

theorem inputPowerThreeEvalEight :
    (CostPolynomial.inputPower 3).eval 8 =
      8 ^ 3 :=
  CostPolynomial.eval_inputPower
    3
    8

theorem inputPowerThreeDegree :
    (CostPolynomial.inputPower 3).degree =
      3 :=
  CostPolynomial.inputPower_degree
    3

theorem scaledFuelThreeFour :
    scaledLogarithmicWitnessFuel
      3
      4 =
    12 := by
  rfl

theorem scaledPrimitiveExactThreeFour :
    closurePrimitiveQueryBudget
          1
          (scaledLogarithmicWitnessFuel
            3
            4) +
        1 =
      (logarithmicWitnessInputBits 4) ^ 3 :=
  scaledLogarithmicWitnessPrimitive_exact
    3
    4

theorem scaledCompositionExactThreeFour :
    closureCompositionCandidateBudget
          1
          (scaledLogarithmicWitnessFuel
            3
            4) +
        1 =
      (logarithmicWitnessInputBits 4) ^ 3 :=
  scaledLogarithmicWitnessComposition_exact
    3
    4

theorem scaledFuelThreeUnbounded :
    ∀ cap : Nat,
      ∃ n : Nat,
        cap <
          scaledLogarithmicWitnessFuel
            3
            n :=
  scaledLogarithmicWitnessFuel_unbounded
    3
    (by decide)

theorem scaledPrimitiveThreePolynomial :
    InputPolynomiallyBounded
      logarithmicWitnessInputBits
      (fun n =>
        closurePrimitiveQueryBudget
          1
          (scaledLogarithmicWitnessFuel
            3
            n)) :=
  scaledLogarithmicWitnessPrimitive_inputPolynomiallyBounded
    3

theorem scaledCompositionThreePolynomial :
    InputPolynomiallyBounded
      logarithmicWitnessInputBits
      (fun n =>
        closureCompositionCandidateBudget
          1
          (scaledLogarithmicWitnessFuel
            3
            n)) :=
  scaledLogarithmicWitnessComposition_inputPolynomiallyBounded
    3

end ConstitutiveSearch.Tests.ClosureSearchScaledLogFuelPolynomialRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchScaledLogFuelPolynomialRegression.inputPowerThreeEvalEight
#print axioms ConstitutiveSearch.Tests.ClosureSearchScaledLogFuelPolynomialRegression.inputPowerThreeDegree
#print axioms ConstitutiveSearch.Tests.ClosureSearchScaledLogFuelPolynomialRegression.scaledFuelThreeFour
#print axioms ConstitutiveSearch.Tests.ClosureSearchScaledLogFuelPolynomialRegression.scaledPrimitiveExactThreeFour
#print axioms ConstitutiveSearch.Tests.ClosureSearchScaledLogFuelPolynomialRegression.scaledCompositionExactThreeFour
#print axioms ConstitutiveSearch.Tests.ClosureSearchScaledLogFuelPolynomialRegression.scaledFuelThreeUnbounded
#print axioms ConstitutiveSearch.Tests.ClosureSearchScaledLogFuelPolynomialRegression.scaledPrimitiveThreePolynomial
#print axioms ConstitutiveSearch.Tests.ClosureSearchScaledLogFuelPolynomialRegression.scaledCompositionThreePolynomial
/- AXIOM_AUDIT_END -/
