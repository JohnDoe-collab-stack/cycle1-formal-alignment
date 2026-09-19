import ConstitutiveSearch.ClassicalDecisionComplexity

/-!
# Withdrawn pre-audit classical bridge

The former bridge projected the constitutive program into predicates named
`InP` and `InNP`.  Aristotle II proved that the underlying finite-equality code
languages do not model classical P or NP.  The predicates have been renamed to
`InFiniteEqualityP` and `InFiniteEqualityNP`, and the old bridge/completion
bundles are removed from the active API.

This module retains only an explicit withdrawal status.  No statement of
`P = NP` or `P != NP` is made.
-/

namespace ConstitutiveSearch
namespace SAT

inductive PreAuditClassicalBridgeStatus where
  | withdrawnBecauseInterfaceWasFiniteEqualityOnly
  deriving DecidableEq, Repr

def preAuditClassicalBridgeStatus :
    PreAuditClassicalBridgeStatus :=
  .withdrawnBecauseInterfaceWasFiniteEqualityOnly

theorem preAuditClassicalBridge_isWithdrawn :
    preAuditClassicalBridgeStatus =
      .withdrawnBecauseInterfaceWasFiniteEqualityOnly :=
  rfl

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.PreAuditClassicalBridgeStatus
#print axioms ConstitutiveSearch.SAT.preAuditClassicalBridgeStatus
#print axioms ConstitutiveSearch.SAT.preAuditClassicalBridge_isWithdrawn
/- AXIOM_AUDIT_END -/
