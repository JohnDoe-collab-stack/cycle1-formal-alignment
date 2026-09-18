import ConstitutiveSearch.SAT.ExplicitFamilyInputPolynomialProfile

namespace ConstitutiveSearch.Tests.SATExplicitFamilyInputPolynomialProfileRegression

open ConstitutiveSearch
open SAT

theorem localWidth3 :
    (explicitFamilyConstitutiveProfile 3).maxFrontierWidth ≤ 2 :=
  explicitFamilyConstitutiveProfile_width_le_two 3

theorem localProfilePolynomial :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      explicitFamilyConstitutiveProfile :=
  explicitFamilyConstitutiveProfile_inputPolynomiallyBounded

theorem compositionProfilePolynomial :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      composedClosureConstitutivePhaseProfile :=
  composedClosureConstitutivePhaseProfile_inputPolynomiallyBounded

theorem totalProfilePolynomial :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      explicitFamilyWithCompositionProfile :=
  explicitFamilyWithCompositionProfile_inputPolynomiallyBounded

end ConstitutiveSearch.Tests.SATExplicitFamilyInputPolynomialProfileRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyInputPolynomialProfileRegression.localWidth3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyInputPolynomialProfileRegression.localProfilePolynomial
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyInputPolynomialProfileRegression.compositionProfilePolynomial
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyInputPolynomialProfileRegression.totalProfilePolynomial
/- AXIOM_AUDIT_END -/
