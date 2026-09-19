import ConstitutiveSearch.SAT.TrajectoryConstitutedLocalAccounting

namespace ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalAccountingRegression

open ConstitutiveSearch
open SAT

theorem productionMatchesCertificateAtoms3 :
    (explicitFamilyComplexityCounts 3).certificateAtoms =
      ConstitutedLocalSchedule.atomCount
        (explicitFamilyConstitutedLocalWitnesses 3) :=
  explicitFamilyConstitutedProduction_matchesCertificateAtoms 3

theorem productionMatchesProvenance3 :
    (explicitFamilyComplexityCounts 3).provenanceUnits =
      (explicitFamilyResourceTrajectory 3).trajectory.decisionVars.length :=
  explicitFamilyConstitutedProduction_matchesProvenanceUnits 3

theorem provenanceVariableQueries3 :
    explicitFamilyConstitutedProvenanceVariableQueries 3 ≤
      3 * 3 :=
  explicitFamilyConstitutedProvenanceVariableQueries_le_square 3

theorem validationCalls3 :
    (explicitFamilyConstitutedValidationCounts 3).relationFindCalls =
      3 :=
  explicitFamilyConstitutedValidationCounts_relationFindCalls 3

theorem executionQueries3 :
    (explicitFamilyConstitutedExecutionCounts 3).closurePrimitiveQueries =
      3 :=
  explicitFamilyConstitutedExecutionCounts_primitiveQueries 3

theorem executionComposition3 :
    (explicitFamilyConstitutedExecutionCounts 3).closureCompositionCandidates =
      0 :=
  explicitFamilyConstitutedExecutionCounts_compositionCandidates 3

theorem validationChargeBound3 :
    explicitFamilyConstitutedValidationRepresentationCharge 3 ≤
      explicitFamilyConstitutedLocalQueryInputBudget 3 :=
  explicitFamilyConstitutedValidationRepresentationCharge_le_inputBudget 3

theorem executionChargeBound3 :
    explicitFamilyConstitutedExecutionRepresentationCharge 3 ≤
      explicitFamilyConstitutedLocalQueryInputBudget 3 :=
  explicitFamilyConstitutedExecutionRepresentationCharge_le_inputBudget 3

theorem accountingEvidence3 :
    ExplicitFamilyConstitutedLocalAccountingEvidence 3 :=
  explicitFamilyConstitutedLocalAccountingEvidence 3

end ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalAccountingRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalAccountingRegression.productionMatchesCertificateAtoms3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalAccountingRegression.productionMatchesProvenance3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalAccountingRegression.provenanceVariableQueries3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalAccountingRegression.validationCalls3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalAccountingRegression.executionQueries3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalAccountingRegression.executionComposition3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalAccountingRegression.validationChargeBound3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalAccountingRegression.executionChargeBound3
#print axioms ConstitutiveSearch.Tests.SATTrajectoryConstitutedLocalAccountingRegression.accountingEvidence3
/- AXIOM_AUDIT_END -/
