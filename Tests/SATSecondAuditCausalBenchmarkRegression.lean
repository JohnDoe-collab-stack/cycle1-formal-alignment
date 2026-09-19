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

/-- Extraction counters are produced by the traversal, not inferred from output size. -/
theorem decoyExtractionRunIsInstrumented :
    (runCandidateExtraction decoyExplorationRoot).stats.clauseVisits = 3 /\
      (runCandidateExtraction decoyExplorationRoot).stats.literalVisits = 5 :=
  ⟨rfl, rfl⟩

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
    (causalDecision_signal_true_accepts rfl)

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
          ((causalDecision_signal_false_rejects rfl)
            accepted)

/-- The semantic benchmark has unbounded, strictly growing YES witnesses. -/
theorem unboundedYesWitness
    (index : Nat) :
    CausalDecisionAccept (causalDecisionYesInput index) /\
      causalDecisionYesInput index <
        causalDecisionYesInput (index + 1) :=
  ⟨causalDecisionYesInput_accepts index,
    causalDecisionYesInput_strict index⟩

/-- It also has unbounded, strictly growing NO witnesses. -/
theorem unboundedNoWitness
    (index : Nat) :
    ¬ CausalDecisionAccept (causalDecisionNoInput index) /\
      causalDecisionNoInput index <
        causalDecisionNoInput (index + 1) :=
  ⟨causalDecisionNoInput_rejects index,
    causalDecisionNoInput_strict index⟩

/-- The public certified run retains a terminal tied to its execution. -/
theorem certifiedRunRetainsCausalChain
    (input : Nat) :
    let run := executeCausalDecisionCertified input
    run.execution.run.code? = some run.execution.code /\
      run.terminal.scan =
        scanExecutedTerminal
          run.execution.producedState.context.formula :=
  ⟨(executeCausalDecisionCertified input).execution_found,
    (executeCausalDecisionCertified input).terminal_from_execution⟩

/-- Schedule production is itself retained as an exact, charged run. -/
theorem certifiedScheduleWasProduced
    (input : Nat) :
    let run := executeCausalDecisionCertified input
    run.scheduleRun =
        runDiscoveryScheduleProduction run.discovery /\
      run.scheduleRun.atomsEmitted =
        run.scheduleRun.schedule.entry.code.size :=
  ⟨(executeCausalDecisionCertified input).scheduleRunExact,
    (executeCausalDecisionCertified input).scheduleRun.atomsExact⟩

/-- The published schedule charge is read from the retained producer run. -/
theorem scheduleCostFromProducerRun
    (input : Nat) :
    let run := executeCausalDecisionCertified input
    run.stats.scheduleAtoms = run.scheduleRun.atomsEmitted := by
  dsimp
  rw [(executeCausalDecisionCertified input).statsExact]
  unfold causalDecisionStatsFromPhases
  rfl

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
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.decoyExtractionRunIsInstrumented
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.decoyIsExploredAndRejected
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.endogenousDiscoverySeven
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.fullPipelineYes
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.fullPipelineNo
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.unboundedYesWitness
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.unboundedNoWitness
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.certifiedRunRetainsCausalChain
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.certifiedScheduleWasProduced
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.scheduleCostFromProducerRun
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.terminalReallyProduced
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.validationCostFromRun
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.executionCostFromRun
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.executionCarriesReturnedCode
#print axioms ConstitutiveSearch.Tests.SATSecondAuditCausalBenchmarkRegression.terminalCitesExecution
/- AXIOM_AUDIT_END -/
