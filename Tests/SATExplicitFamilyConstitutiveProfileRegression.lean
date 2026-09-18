import ConstitutiveSearch.SAT.ExplicitFamilyConstitutiveProfile

namespace ConstitutiveSearch.Tests.SATExplicitFamilyConstitutiveProfileRegression

open ConstitutiveSearch
open SAT

theorem localDepth3 :
    (explicitFamilyConstitutiveProfile 3).depth = 3 := by
  rfl

theorem combinedDepth3 :
    (explicitFamilyWithCompositionProfile 3).depth = 5 := by
  rfl

theorem combinedCertificates3 :
    (explicitFamilyWithCompositionProfile 3).events.certificateAtoms = 5 :=
  explicitFamilyWithCompositionProfile_certificateAtoms 3

theorem combinedClosureQueries3 :
    (explicitFamilyWithCompositionProfile 3).events.closurePrimitiveQueries = 3 :=
  explicitFamilyWithCompositionProfile_closurePrimitiveQueries 3

theorem combinedClosureCandidates3 :
    (explicitFamilyWithCompositionProfile 3).events.closureCompositionCandidates = 1 :=
  explicitFamilyWithCompositionProfile_closureCompositionCandidates 3

theorem combinedRelationFind3 :
    (explicitFamilyWithCompositionProfile 3).events.relationFindCalls = 6 :=
  explicitFamilyWithCompositionProfile_relationFindCalls 3

theorem combinedChargeBound3 :
    (explicitFamilyWithCompositionProfile 3).representationCharge ≤
      explicitFamilyWithCompositionInputPolynomialBudget 3 :=
  explicitFamilyWithCompositionProfile_charge_le_inputPolynomial 3

end ConstitutiveSearch.Tests.SATExplicitFamilyConstitutiveProfileRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyConstitutiveProfileRegression.localDepth3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyConstitutiveProfileRegression.combinedDepth3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyConstitutiveProfileRegression.combinedCertificates3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyConstitutiveProfileRegression.combinedClosureQueries3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyConstitutiveProfileRegression.combinedClosureCandidates3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyConstitutiveProfileRegression.combinedRelationFind3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyConstitutiveProfileRegression.combinedChargeBound3
/- AXIOM_AUDIT_END -/
