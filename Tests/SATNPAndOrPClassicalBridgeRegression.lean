import ConstitutiveSearch.SAT.NPAndOrPClassicalBridge

namespace ConstitutiveSearch.Tests.SATNPAndOrPClassicalBridgeRegression

open ConstitutiveSearch
open SAT

/-- The finite-equality projection cannot regain a classical-bridge status. -/
theorem historicalBridgeWithdrawn :
    preAuditClassicalBridgeStatus =
      PreAuditClassicalBridgeStatus.withdrawnBecauseInterfaceWasFiniteEqualityOnly :=
  preAuditClassicalBridge_isWithdrawn

end ConstitutiveSearch.Tests.SATNPAndOrPClassicalBridgeRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATNPAndOrPClassicalBridgeRegression.historicalBridgeWithdrawn
/- AXIOM_AUDIT_END -/
