import ConstitutiveSearch.SAT.ComposedLocalCodePolynomial

namespace ConstitutiveSearch.Tests.SATComposedLocalCodePolynomialRegression

open ConstitutiveSearch
open SAT

theorem familyPolynomial :
    LocalSearchableCodeFamilyInputPolynomiallyBounded
      (fun count =>
        composedPrimitiveSearch count)
      (fun count =>
        composedConstitutedCode count)
      explicitFamilyInputBitSize :=
  composedConstitutedCodeFamily_localInputPolynomiallyBounded

theorem primitiveBudget3 :
    localSearchableCodePrimitiveBudget
        (fun count =>
          composedConstitutedCode count)
        3 =
      2 :=
  composedConstitutedCode_localPrimitiveBudget 3

theorem compositionBudget3 :
    localSearchableCodeCompositionBudget 3 =
      0 :=
  composedConstitutedCode_localCompositionBudget 3

end ConstitutiveSearch.Tests.SATComposedLocalCodePolynomialRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATComposedLocalCodePolynomialRegression.familyPolynomial
#print axioms ConstitutiveSearch.Tests.SATComposedLocalCodePolynomialRegression.primitiveBudget3
#print axioms ConstitutiveSearch.Tests.SATComposedLocalCodePolynomialRegression.compositionBudget3
/- AXIOM_AUDIT_END -/
