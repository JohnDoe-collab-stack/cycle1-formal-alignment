import ConstitutiveSearch.SAT.ComposedSearchableCodeValidation

namespace ConstitutiveSearch.Tests.SATComposedSearchableCodeValidationRegression

open ConstitutiveSearch
open SAT

theorem success3 :
    (composedConstitutedCodeValidation 3).success = true :=
  composedConstitutedCodeValidation_success 3

theorem queries3 :
    (composedConstitutedCodeValidation 3).primitiveQueries = 2 :=
  composedConstitutedCodeValidation_primitiveQueries 3

theorem validationPolynomial :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        (composedConstitutedCodeValidation
          count).primitiveQueries) :=
  composedConstitutedCodeValidation_inputPolynomiallyBounded

end ConstitutiveSearch.Tests.SATComposedSearchableCodeValidationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATComposedSearchableCodeValidationRegression.success3
#print axioms ConstitutiveSearch.Tests.SATComposedSearchableCodeValidationRegression.queries3
#print axioms ConstitutiveSearch.Tests.SATComposedSearchableCodeValidationRegression.validationPolynomial
/- AXIOM_AUDIT_END -/
