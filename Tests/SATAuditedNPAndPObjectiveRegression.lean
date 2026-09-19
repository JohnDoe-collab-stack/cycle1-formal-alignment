import ConstitutiveSearch.SAT.AuditedNPAndPObjective

namespace ConstitutiveSearch.Tests.SATAuditedNPAndPObjectiveRegression

open ConstitutiveSearch
open SAT

/-- The former completion marker cannot silently regain closure status. -/
theorem formerMarkerWithdrawn :
    firstAuditClosureStatus =
      FirstAuditClosureStatus.withdrawnAfterSecondAudit :=
  firstAuditClosure_isWithdrawn

/-- The historical API flag remains stable without being an operational claim. -/
theorem repairedPipelineProducesTerminal
    (input : Nat) :
    (executeCausalDecision input).terminalProduced = true :=
  secondAuditRepair_producesTerminal input

end ConstitutiveSearch.Tests.SATAuditedNPAndPObjectiveRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATAuditedNPAndPObjectiveRegression.formerMarkerWithdrawn
#print axioms ConstitutiveSearch.Tests.SATAuditedNPAndPObjectiveRegression.repairedPipelineProducesTerminal
/- AXIOM_AUDIT_END -/
