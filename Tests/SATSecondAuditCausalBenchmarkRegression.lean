import ConstitutiveSearch.SAT.SecondAuditCausalBenchmark

namespace ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression

open ConstitutiveSearch
open SAT

/-- Concrete state with a syntactic decoy before the useful split variable. -/
def decoyExplorationFormula : Cnf :=
  [ [Literal.positive 2],
    [Literal.positive 0, Literal.positive 1],
    [Literal.negative 0, Literal.positive 1] ]

def decoyExplorationRoot :
    GeneratedStructuralBranchContext decoyExplorationFormula :=
  GeneratedStructuralBranchContext.root decoyExplorationFormula

/-- Extraction really exposes the decoy before the useful candidate. -/
theorem decoyComesFirst :
    extractStructuralCandidates decoyExplorationRoot =
      [2, 0, 1, 0, 1] :=
  rfl

/-- Exploration rejects the decoy, finds the next candidate, and charges both attempts. -/
theorem decoyIsExploredAndRejected :
    (runEndogenousFlipDiscovery
      decoyExplorationRoot).outcome.attempts = 2 :=
  rfl

/-- The useful variable varies with the input rather than being fixed in the procedure. -/
theorem selectedVariableMoves :
    causalDecisionSplitVar 7 = 9 :=
  rfl

/-- Extraction and exploration return that input-derived variable and charge the attempt. -/
theorem endogenousDiscoverySeven :
    exists discovery,
      (runEndogenousFlipDiscovery
        (causalDecisionRoot 7)).outcome.discovered? =
          some discovery /\
      discovery.var = 9 /\
      (runEndogenousFlipDiscovery
        (causalDecisionRoot 7)).outcome.attempts = 1 := by
  rcases causalDecision_discovery_found 7 with
    ⟨discovery, found, selected, attempts⟩
  exact ⟨discovery, found, selected, attempts⟩

/-- The full typed pipeline accepts the genuine YES instance. -/
theorem fullPipelineYes :
    (executeCausalDecision 0).result = true :=
  (executeCausalDecision_correct 0).2
    causalDecision_zero_accepts

/-- The full typed pipeline rejects a genuine NO instance. -/
theorem fullPipelineNo :
    (executeCausalDecision 1).result = false := by
  cases result : (executeCausalDecision 1).result with
  | false =>
      rfl
  | true =>
      have accepted : CausalDecisionAccept 1 :=
        (executeCausalDecision_correct 1).1 result
      exact
        False.elim
          ((causalDecision_nonzero_rejects
            (by decide : (1 : Nat) ≠ 0))
            accepted)

/-- The announced procedure always produces an execution-indexed terminal. -/
theorem terminalReallyProduced
    (input : Nat) :
    (executeCausalDecision input).terminalProduced = true :=
  executeCausalDecision_terminalProduced input

/-- Validation cost is obtained from the exact validation run. -/
theorem validationCostFromRun
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    (schedule : DiscoverySchedule discovery) :
    (runDiscoveryScheduleValidation schedule).primitiveQueries = 1 :=
  runDiscoveryScheduleValidation_queries schedule

/-- Execution costs are obtained from the exact candidate-free execution run. -/
theorem executionCostFromRun
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    (validated : ValidatedDiscoverySchedule schedule) :
    (executeValidatedDiscoverySchedule
        validated).run.stats.primitiveQueries = 1 /\
      (executeValidatedDiscoverySchedule
        validated).run.stats.compositionCandidates = 0 :=
  executeValidatedDiscoverySchedule_stats validated

/-- The execution object retains the code actually returned by its run. -/
theorem executionCarriesReturnedCode
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    (validated : ValidatedDiscoverySchedule schedule) :
    (executeValidatedDiscoverySchedule validated).run.code? =
      some (executeValidatedDiscoverySchedule validated).code :=
  (executeValidatedDiscoverySchedule validated).codeExact

/-- Counter-regression to the old bypass: terminal contents cite their execution. -/
theorem terminalCitesExecution
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    {validated : ValidatedDiscoverySchedule schedule}
    {execution : ExecutedDiscoverySchedule validated}
    (terminal : ExecutedTerminalArtifact execution) :
    terminal.scan =
      scanExecutedTerminal
        execution.producedState.context.formula :=
  terminal.scan_from_execution

end ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.selectedVariableMoves
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.decoyComesFirst
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.decoyIsExploredAndRejected
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.endogenousDiscoverySeven
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.fullPipelineYes
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.fullPipelineNo
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.terminalReallyProduced
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.validationCostFromRun
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.executionCostFromRun
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.executionCarriesReturnedCode
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.terminalCitesExecution
/- AXIOM_AUDIT_END -/
