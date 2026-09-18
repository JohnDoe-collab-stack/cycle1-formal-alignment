import ConstitutiveSearch.ClosureSearchPolynomialComplexity

namespace ConstitutiveSearch.Tests.ClosureSearchPolynomialComplexityRegression

open ConstitutiveSearch

theorem primitiveEval3 :
    closureFuelTwoPrimitivePolynomial.eval 3 = 7 :=
  closureFuelTwoPrimitivePolynomial_eval 3

theorem compositionEval3 :
    closureFuelTwoCompositionPolynomial.eval 3 = 21 :=
  closureFuelTwoCompositionPolynomial_eval 3

theorem totalEval3 :
    closureFuelTwoTotalPolynomial.eval 3 = 28 :=
  closureFuelTwoTotalPolynomial_eval 3

theorem primitivePolynomial :
    PolynomiallyBounded
      closureFuelTwoPrimitiveInputBudget :=
  closureFuelTwoPrimitiveInputBudget_polynomiallyBounded

theorem compositionPolynomial :
    PolynomiallyBounded
      closureFuelTwoCompositionInputBudget :=
  closureFuelTwoCompositionInputBudget_polynomiallyBounded

theorem totalPolynomial :
    PolynomiallyBounded
      closureFuelTwoTotalInputBudget :=
  closureFuelTwoTotalInputBudget_polynomiallyBounded

end ConstitutiveSearch.Tests.ClosureSearchPolynomialComplexityRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchPolynomialComplexityRegression.primitiveEval3
#print axioms ConstitutiveSearch.Tests.ClosureSearchPolynomialComplexityRegression.compositionEval3
#print axioms ConstitutiveSearch.Tests.ClosureSearchPolynomialComplexityRegression.totalEval3
#print axioms ConstitutiveSearch.Tests.ClosureSearchPolynomialComplexityRegression.primitivePolynomial
#print axioms ConstitutiveSearch.Tests.ClosureSearchPolynomialComplexityRegression.compositionPolynomial
#print axioms ConstitutiveSearch.Tests.ClosureSearchPolynomialComplexityRegression.totalPolynomial
/- AXIOM_AUDIT_END -/
