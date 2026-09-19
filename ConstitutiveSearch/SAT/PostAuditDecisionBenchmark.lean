import ConstitutiveSearch.SAT.SecondAuditCausalBenchmark

/-!
# Withdrawn first-audit decision benchmark

The former contents of this module implemented `executeAuditedDecision`.
Aristotle II exhibited a stripped procedure that returned the same Boolean
without discovery, schedule production, validation or local execution.

That bypassable benchmark is no longer part of the active formal API.  Its
replacement is `SecondAuditCausalBenchmark`, whose terminal is indexed by the
execution that produces its state.  This module retains only an explicit
withdrawal status so that downstream code cannot mistake historical
compatibility for a current result.
-/

namespace ConstitutiveSearch
namespace SAT

inductive FirstAuditDecisionBenchmarkStatus where
  | withdrawnBecauseCausallyBypassable
  deriving DecidableEq, Repr

def firstAuditDecisionBenchmarkStatus :
    FirstAuditDecisionBenchmarkStatus :=
  .withdrawnBecauseCausallyBypassable

theorem firstAuditDecisionBenchmark_isWithdrawn :
    firstAuditDecisionBenchmarkStatus =
      .withdrawnBecauseCausallyBypassable :=
  rfl

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.FirstAuditDecisionBenchmarkStatus
#print axioms ConstitutiveSearch.SAT.firstAuditDecisionBenchmarkStatus
#print axioms ConstitutiveSearch.SAT.firstAuditDecisionBenchmark_isWithdrawn
/- AXIOM_AUDIT_END -/
