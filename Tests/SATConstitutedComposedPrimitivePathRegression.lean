import ConstitutiveSearch.SAT.ConstitutedComposedPrimitivePath

namespace ConstitutiveSearch.Tests.SATConstitutedComposedPrimitivePathRegression

open ConstitutiveSearch
open SAT

theorem path3Length :
    (composedConstitutedPrimitivePath 3).length = 2 :=
  composedConstitutedPrimitivePath_length 3

theorem path3Code :
    (composedConstitutedPrimitivePath 3).toTransportCode =
      composedConstitutedCode 3 :=
  composedConstitutedPrimitivePath_code 3

theorem path3ValidationSuccess :
    (validateSearchableCode
      (composedPrimitiveSearch 3)
      (composedConstitutedPrimitivePath 3).toTransportCode).success =
      true :=
  composedConstitutedPrimitivePath_validation_success 3

theorem path3ValidationQueries :
    (validateSearchableCode
      (composedPrimitiveSearch 3)
      (composedConstitutedPrimitivePath 3).toTransportCode).primitiveQueries =
      2 :=
  composedConstitutedPrimitivePath_validation_queries 3

theorem path3EndToEnd :
    ConstitutedPrimitivePath.EndToEndLocalExecution
      (composedPrimitiveSearch 3)
      (composedConstitutedPrimitivePath 3) :=
  composedConstitutedPrimitivePath_endToEnd 3

end ConstitutiveSearch.Tests.SATConstitutedComposedPrimitivePathRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATConstitutedComposedPrimitivePathRegression.path3Length
#print axioms ConstitutiveSearch.Tests.SATConstitutedComposedPrimitivePathRegression.path3Code
#print axioms ConstitutiveSearch.Tests.SATConstitutedComposedPrimitivePathRegression.path3ValidationSuccess
#print axioms ConstitutiveSearch.Tests.SATConstitutedComposedPrimitivePathRegression.path3ValidationQueries
#print axioms ConstitutiveSearch.Tests.SATConstitutedComposedPrimitivePathRegression.path3EndToEnd
/- AXIOM_AUDIT_END -/
