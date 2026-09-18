import ConstitutiveSearch.SAT.ExplicitFamilyInputComplexity

namespace ConstitutiveSearch.Tests.SATExplicitFamilyInputComplexityRegression

open ConstitutiveSearch
open SAT

theorem index3_le_input :
    3 ≤ explicitFamilyInputBitSize 3 :=
  explicitFamilyIndex_le_inputBitSize 3

theorem polynomial3_mono_input :
    explicitFamilyRepresentationPolynomialBudget 3 ≤
      explicitFamilyInputIndexedPolynomialBudget 3 :=
  explicitFamilyRepresentationPolynomialBudget_mono
    (explicitFamilyIndex_le_inputBitSize 3)

theorem charged3_le_inputPolynomial :
    explicitFamilyRepresentationChargedCost 3 ≤
      explicitFamilyInputIndexedPolynomialBudget 3 :=
  explicitFamilyRepresentationChargedCost_le_inputIndexedPolynomial 3

end ConstitutiveSearch.Tests.SATExplicitFamilyInputComplexityRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyInputComplexityRegression.index3_le_input
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyInputComplexityRegression.polynomial3_mono_input
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyInputComplexityRegression.charged3_le_inputPolynomial
/- AXIOM_AUDIT_END -/
