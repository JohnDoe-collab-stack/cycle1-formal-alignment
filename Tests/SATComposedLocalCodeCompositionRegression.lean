import ConstitutiveSearch.SAT.ComposedLocalCodeComposition

namespace ConstitutiveSearch.Tests.SATComposedLocalCodeCompositionRegression

open ConstitutiveSearch
open SAT

theorem localPiecesCompose3 :
    composeSearchableCodeFamily
        composedFirstLocalCode
        composedSecondLocalCode
        3 =
      composedConstitutedCode 3 :=
  composedLocalCodeComposition_eq_constituted 3

theorem localCompositionPolynomial :
    LocalSearchableCodeFamilyInputPolynomiallyBounded
      (fun count =>
        composedPrimitiveSearch count)
      (composeSearchableCodeFamily
        composedFirstLocalCode
        composedSecondLocalCode)
      explicitFamilyInputBitSize :=
  composedConstitutedCodeFamily_localInputPolynomiallyBounded_byComposition

end ConstitutiveSearch.Tests.SATComposedLocalCodeCompositionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATComposedLocalCodeCompositionRegression.localPiecesCompose3
#print axioms ConstitutiveSearch.Tests.SATComposedLocalCodeCompositionRegression.localCompositionPolynomial
/- AXIOM_AUDIT_END -/
