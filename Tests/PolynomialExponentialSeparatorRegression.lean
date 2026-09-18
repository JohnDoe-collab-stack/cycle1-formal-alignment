import ConstitutiveSearch.PolynomialExponentialSeparator

namespace ConstitutiveSearch.Tests.PolynomialExponentialSeparatorRegression

open ConstitutiveSearch

def demoPolynomial :
    CostPolynomial :=
  .mul
    (.add
      .input
      (.constant 3))
    .input

theorem demoMajorant :
    ∀ inputBits : Nat,
      1 ≤ inputBits →
        demoPolynomial.eval inputBits ≤
          demoPolynomial.majorantMass *
            inputBits ^ demoPolynomial.majorantRank :=
  CostPolynomial.eval_le_majorant
    demoPolynomial

theorem demoEscape :
    ∃ inputBits : Nat,
      demoPolynomial.eval inputBits <
        2 ^ inputBits :=
  demoPolynomial.exists_eval_lt_two_pow

theorem exponentialNotPolynomial :
    ¬
      PolynomiallyBounded
        (fun inputBits =>
          2 ^ inputBits) :=
  twoPow_not_polynomiallyBounded

theorem primitiveGrowingFuelNotPolynomial :
    ¬
      PolynomiallyBounded
        (fun inputBits =>
          closurePrimitiveQueryBudget
            1
            inputBits) :=
  closurePrimitiveOneCandidateIdentityFuel_not_polynomiallyBounded

theorem compositionGrowingFuelNotPolynomial :
    ¬
      PolynomiallyBounded
        (fun inputBits =>
          closureCompositionCandidateBudget
            1
            inputBits) :=
  closureCompositionOneCandidateIdentityFuel_not_polynomiallyBounded

end ConstitutiveSearch.Tests.PolynomialExponentialSeparatorRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.PolynomialExponentialSeparatorRegression.demoMajorant
#print axioms ConstitutiveSearch.Tests.PolynomialExponentialSeparatorRegression.demoEscape
#print axioms ConstitutiveSearch.Tests.PolynomialExponentialSeparatorRegression.exponentialNotPolynomial
#print axioms ConstitutiveSearch.Tests.PolynomialExponentialSeparatorRegression.primitiveGrowingFuelNotPolynomial
#print axioms ConstitutiveSearch.Tests.PolynomialExponentialSeparatorRegression.compositionGrowingFuelNotPolynomial
/- AXIOM_AUDIT_END -/
