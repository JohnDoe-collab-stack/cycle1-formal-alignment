import ConstitutiveSearch.SAT.AuditedNPAndPObjective

namespace ConstitutiveSearch.Tests.SATAuditedNPAndPObjectiveRegression

open ConstitutiveSearch
open SAT

theorem programClosed :
    AuditedNPAndPProgramClosed :=
  auditedNPAndPProgramClosed

theorem objectiveComplete :
    AuditedNPAndPObjectiveComplete :=
  auditedNPAndPObjectiveComplete

theorem yesStillYes :
    auditedDecisionProblem.Accept 0 :=
  auditedNPAndPProgramClosed.decisionYes

theorem oneStillNo :
    ¬ auditedDecisionProblem.Accept 1 :=
  auditedNPAndPProgramClosed.decisionNo

theorem ungatedLossRetained :
    UngatedConstitutiveProjectionLoss :=
  auditedNPAndPProgramClosed.ungatedProjectionLoss

theorem decisionProjection3 :
    (executeDecider
      auditedDecisionDeciderCode
      3).result =
    (executeAuditedDecision
      3).result :=
  auditedNPAndPObjectiveComplete.extensionalDecisionPreserved
    3

end ConstitutiveSearch.Tests.SATAuditedNPAndPObjectiveRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATAuditedNPAndPObjectiveRegression.programClosed
#print axioms ConstitutiveSearch.Tests.SATAuditedNPAndPObjectiveRegression.objectiveComplete
#print axioms ConstitutiveSearch.Tests.SATAuditedNPAndPObjectiveRegression.yesStillYes
#print axioms ConstitutiveSearch.Tests.SATAuditedNPAndPObjectiveRegression.oneStillNo
#print axioms ConstitutiveSearch.Tests.SATAuditedNPAndPObjectiveRegression.ungatedLossRetained
#print axioms ConstitutiveSearch.Tests.SATAuditedNPAndPObjectiveRegression.decisionProjection3
/- AXIOM_AUDIT_END -/
