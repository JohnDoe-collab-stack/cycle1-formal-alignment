import ConstitutiveSearch.SAT.SecondAuditCausalBenchmark

/-!
# Withdrawn first-audit closure marker

The theorem formerly exported by this module as
`auditedNPAndPObjectiveComplete` was stronger than its premises justified.
The second adversarial audit established two material gaps:

* the historical `DeciderCode`/`VerifierCode` interfaces are not adequate
  models of classical P/NP;
* the historical decision benchmark allowed its constitutive phases to be
  bypassed when producing the terminal answer.

The individual structural theorems remain in their defining modules.  This
module now records only the withdrawal of the old closure status and points to
the second-audit repair.  It intentionally exports no replacement completion
marker before another adversarial audit.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Explicit status of the first-audit closure claim after the second audit. -/
inductive FirstAuditClosureStatus where
  | withdrawnAfterSecondAudit
  deriving DecidableEq, Repr

/-- The former closure claim is withdrawn, not silently renamed. -/
def firstAuditClosureStatus : FirstAuditClosureStatus :=
  .withdrawnAfterSecondAudit

/-- Regression statement fixing the withdrawal in the formal API. -/
theorem firstAuditClosure_isWithdrawn :
    firstAuditClosureStatus =
      .withdrawnAfterSecondAudit :=
  rfl

/--
Legacy compatibility theorem for the historical `terminalProduced` flag.  The
flag records typed phase reachability, not operational state production; the
active operational theorem is in `OperationalProjectionInadequacy`.
-/
theorem secondAuditRepair_producesTerminal
    (input : Nat) :
    (executeCausalDecision input).terminalProduced = true :=
  executeCausalDecision_terminalProduced input

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.FirstAuditClosureStatus
#print axioms ConstitutiveSearch.SAT.firstAuditClosureStatus
#print axioms ConstitutiveSearch.SAT.firstAuditClosure_isWithdrawn
#print axioms ConstitutiveSearch.SAT.secondAuditRepair_producesTerminal
/- AXIOM_AUDIT_END -/
