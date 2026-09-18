import ConstitutiveSearch.ClosureSearchLogFuelPolynomial

namespace ConstitutiveSearch.Tests.ClosureSearchLogFuelPolynomialRegression

open ConstitutiveSearch

theorem witnessFuelThree :
    logarithmicWitnessFuel 3 = 3 := by
  rfl

theorem witnessInputThree :
    logarithmicWitnessInputBits 3 = 8 := by
  rfl

theorem witnessFuelIsLogThree :
    logarithmicWitnessFuel 3 =
      Nat.log2
        (logarithmicWitnessInputBits 3) :=
  logarithmicWitnessFuel_eq_log 3

theorem witnessFuelUnbounded :
    ∀ cap : Nat,
      ∃ n : Nat,
        cap <
          logarithmicWitnessFuel n :=
  logarithmicWitnessFuel_unbounded

theorem primitiveWitnessPolynomial :
    InputPolynomiallyBounded
      logarithmicWitnessInputBits
      (fun n =>
        closurePrimitiveQueryBudget
          1
          (logarithmicWitnessFuel n)) :=
  logarithmicWitnessPrimitive_inputPolynomiallyBounded

theorem compositionWitnessPolynomial :
    InputPolynomiallyBounded
      logarithmicWitnessInputBits
      (fun n =>
        closureCompositionCandidateBudget
          1
          (logarithmicWitnessFuel n)) :=
  logarithmicWitnessComposition_inputPolynomiallyBounded

end ConstitutiveSearch.Tests.ClosureSearchLogFuelPolynomialRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchLogFuelPolynomialRegression.witnessFuelThree
#print axioms ConstitutiveSearch.Tests.ClosureSearchLogFuelPolynomialRegression.witnessInputThree
#print axioms ConstitutiveSearch.Tests.ClosureSearchLogFuelPolynomialRegression.witnessFuelIsLogThree
#print axioms ConstitutiveSearch.Tests.ClosureSearchLogFuelPolynomialRegression.witnessFuelUnbounded
#print axioms ConstitutiveSearch.Tests.ClosureSearchLogFuelPolynomialRegression.primitiveWitnessPolynomial
#print axioms ConstitutiveSearch.Tests.ClosureSearchLogFuelPolynomialRegression.compositionWitnessPolynomial
/- AXIOM_AUDIT_END -/
