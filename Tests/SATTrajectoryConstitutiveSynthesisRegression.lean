import ConstitutiveSearch.SAT.TrajectoryConstitutiveSynthesis

namespace ConstitutiveSearch.Tests.SATTrajectoryConstitutiveSynthesisRegression

open ConstitutiveSearch
open SAT

theorem synthesis3 :
    ExplicitFamilyQuantitativeSynthesis 3 :=
  explicitFamilyQuantitativeSynthesis 3

theorem provenance3 :
    (explicitFamilyConstitutedTotalProfile
      3).events.provenanceUnits =
      3 :=
  explicitFamilyConstitutedTotalProfile_provenance 3

theorem certificates3 :
    (explicitFamilyConstitutedTotalProfile
      3).events.certificateAtoms =
      3 :=
  explicitFamilyConstitutedTotalProfile_certificates 3

theorem productionRelationFindZero3 :
    (explicitFamilyConstitutedProductionProfile
      3).events.relationFindCalls =
      0 := by
  rfl

theorem relationFind3 :
    (explicitFamilyConstitutedTotalProfile
      3).events.relationFindCalls =
      3 :=
  explicitFamilyConstitutedTotalProfile_relationFind 3

theorem closurePrimitive3 :
    (explicitFamilyConstitutedTotalProfile
      3).events.closurePrimitiveQueries =
      3 :=
  explicitFamilyConstitutedTotalProfile_closurePrimitive 3

theorem closureCandidates3 :
    (explicitFamilyConstitutedTotalProfile
      3).events.closureCompositionCandidates =
      0 :=
  explicitFamilyConstitutedTotalProfile_closureCandidates 3

theorem totalPolynomial :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      explicitFamilyConstitutedTotalProfile :=
  explicitFamilyConstitutedTotalProfile_inputPolynomiallyBounded

theorem programClosed :
    ExplicitFamilyQuantitativeProgramClosed :=
  explicitFamilyQuantitativeProgramClosed

end ConstitutiveSearch.Tests.SATTrajectoryConstitutiveSynthesisRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutiveSynthesisRegression.synthesis3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutiveSynthesisRegression.provenance3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutiveSynthesisRegression.certificates3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutiveSynthesisRegression.productionRelationFindZero3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutiveSynthesisRegression.relationFind3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutiveSynthesisRegression.closurePrimitive3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutiveSynthesisRegression.closureCandidates3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutiveSynthesisRegression.totalPolynomial
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutiveSynthesisRegression.programClosed
/- AXIOM_AUDIT_END -/
