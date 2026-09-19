import ConstitutiveSearch.SAT.PostAuditDecisionBenchmark

namespace ConstitutiveSearch.Tests.SATPostAuditDecisionBenchmarkRegression

open ConstitutiveSearch
open SAT

/-- Counter-regression: the bypassable benchmark remains formally withdrawn. -/
theorem bypassableBenchmarkWithdrawn :
    firstAuditDecisionBenchmarkStatus =
      FirstAuditDecisionBenchmarkStatus.withdrawnBecauseCausallyBypassable :=
  firstAuditDecisionBenchmark_isWithdrawn

end ConstitutiveSearch.Tests.SATPostAuditDecisionBenchmarkRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATPostAuditDecisionBenchmarkRegression.bypassableBenchmarkWithdrawn
/- AXIOM_AUDIT_END -/
