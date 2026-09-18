import ConstitutiveSearch.ClosureSearchFixedFuelPolynomial

namespace ConstitutiveSearch.Tests.ClosureSearchFixedFuelPolynomialRegression

open ConstitutiveSearch

theorem primitiveFuel3At2 :
    (closurePrimitiveFixedFuelPolynomial 3).eval 2 =
      closurePrimitiveQueryBudget 2 3 :=
  closurePrimitiveFixedFuelPolynomial_eval 3 2

theorem compositionFuel3At2 :
    (closureCompositionFixedFuelPolynomial 3).eval 2 =
      closureCompositionCandidateBudget 2 3 :=
  closureCompositionFixedFuelPolynomial_eval 3 2

theorem primitiveFuel4Polynomial :
    PolynomiallyBounded
      (fun candidateCount =>
        closurePrimitiveQueryBudget
          candidateCount
          4) :=
  closurePrimitiveFixedFuel_polynomiallyBounded 4

theorem compositionFuel4Polynomial :
    PolynomiallyBounded
      (fun candidateCount =>
        closureCompositionCandidateBudget
          candidateCount
          4) :=
  closureCompositionFixedFuel_polynomiallyBounded 4

theorem primitiveInputBound :
    closurePrimitiveQueryBudget 3 4 ≤
      (closurePrimitiveFixedFuelPolynomial 4).eval 5 :=
  closurePrimitiveFixedFuel_le_inputPolynomial
    4
    3
    5
    (by
      exact
        Nat.le_trans
          (Nat.le_succ 3)
          (Nat.le_succ 4))

end ConstitutiveSearch.Tests.ClosureSearchFixedFuelPolynomialRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchFixedFuelPolynomialRegression.primitiveFuel3At2
#print axioms ConstitutiveSearch.Tests.ClosureSearchFixedFuelPolynomialRegression.compositionFuel3At2
#print axioms ConstitutiveSearch.Tests.ClosureSearchFixedFuelPolynomialRegression.primitiveFuel4Polynomial
#print axioms ConstitutiveSearch.Tests.ClosureSearchFixedFuelPolynomialRegression.compositionFuel4Polynomial
#print axioms ConstitutiveSearch.Tests.ClosureSearchFixedFuelPolynomialRegression.primitiveInputBound
/- AXIOM_AUDIT_END -/
