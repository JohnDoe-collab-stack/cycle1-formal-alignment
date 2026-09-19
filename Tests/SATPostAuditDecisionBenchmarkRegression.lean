import ConstitutiveSearch.SAT.PostAuditDecisionBenchmark

namespace ConstitutiveSearch.Tests.SATPostAuditDecisionBenchmarkRegression

open ConstitutiveSearch
open SAT

theorem yesInstance :
    auditedDecisionProblem.Accept 0 :=
  auditedDecision_yes

theorem noInstance :
    ¬ auditedDecisionProblem.Accept 1 :=
  auditedDecision_no

theorem decisionCorrect3 :
    (executeAuditedDecision 3).result = true ↔
      auditedDecisionProblem.Accept 3 :=
  executeAuditedDecision_correct 3

theorem discoveryCharged3 :
    (executeAuditedDecision 3).stats.discoveryQueries = 1 :=
  executeAuditedDecision_discoveryQueries 3

theorem scheduleCharged3 :
    (executeAuditedDecision 3).stats.scheduleAtoms = 1 :=
  executeAuditedDecision_scheduleAtoms 3

theorem validationCharged3 :
    (executeAuditedDecision 3).stats.validationQueries = 1 :=
  executeAuditedDecision_validationQueries 3

theorem executionCharged3 :
    (executeAuditedDecision 3).stats.executionPrimitiveQueries = 1 :=
  executeAuditedDecision_executionPrimitiveQueries 3

theorem compositionZero3 :
    (executeAuditedDecision 3).stats.executionCompositionCandidates = 0 :=
  executeAuditedDecision_executionCompositionCandidates 3

theorem terminalCharged3 :
    (executeAuditedDecision 3).stats.terminalChecks = 1 :=
  executeAuditedDecision_terminalChecks 3

theorem totalPolynomial :
    InputPolynomiallyBounded
      auditedDecisionProblem.inputSize
      (fun input =>
        (executeAuditedDecision input).stats.total) :=
  executeAuditedDecision_total_inputPolynomiallyBounded

theorem projectedP :
    InP auditedDecisionProblem :=
  auditedDecision_inP

theorem projectedNP :
    InNP auditedDecisionProblem :=
  auditedDecision_inNP

end ConstitutiveSearch.Tests.SATPostAuditDecisionBenchmarkRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATPostAuditDecisionBenchmarkRegression.yesInstance
#print axioms ConstitutiveSearch.Tests.SATPostAuditDecisionBenchmarkRegression.noInstance
#print axioms ConstitutiveSearch.Tests.SATPostAuditDecisionBenchmarkRegression.decisionCorrect3
#print axioms ConstitutiveSearch.Tests.SATPostAuditDecisionBenchmarkRegression.discoveryCharged3
#print axioms ConstitutiveSearch.Tests.SATPostAuditDecisionBenchmarkRegression.scheduleCharged3
#print axioms ConstitutiveSearch.Tests.SATPostAuditDecisionBenchmarkRegression.validationCharged3
#print axioms ConstitutiveSearch.Tests.SATPostAuditDecisionBenchmarkRegression.executionCharged3
#print axioms ConstitutiveSearch.Tests.SATPostAuditDecisionBenchmarkRegression.compositionZero3
#print axioms ConstitutiveSearch.Tests.SATPostAuditDecisionBenchmarkRegression.terminalCharged3
#print axioms ConstitutiveSearch.Tests.SATPostAuditDecisionBenchmarkRegression.totalPolynomial
#print axioms ConstitutiveSearch.Tests.SATPostAuditDecisionBenchmarkRegression.projectedP
#print axioms ConstitutiveSearch.Tests.SATPostAuditDecisionBenchmarkRegression.projectedNP
/- AXIOM_AUDIT_END -/
