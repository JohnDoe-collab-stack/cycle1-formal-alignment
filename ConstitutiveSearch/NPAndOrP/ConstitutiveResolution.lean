import ConstitutiveSearch.NPAndOrP.ExecutedLocalSchedule
import ConstitutiveSearch.NPAndOrP.GenericConcreteRefinement
import ConstitutiveSearch.NPAndOrP.IntegratedProjection
import ConstitutiveSearch.NPAndOrP.MeasuredDiscoveryBounds
import ConstitutiveSearch.NPAndOrP.MeasuredGeneration
import ConstitutiveSearch.NPAndOrP.MeasuredAssignmentBounds
import ConstitutiveSearch.NPAndOrP.ConstitutiveFullStep
import ConstitutiveSearch.NPAndOrP.ConstitutiveRoleCycle

/-!
# Integrated concrete `NP AND/OR P` resolution run

This module packages the construction proved by the isolated integration
layer.  Its scope is deliberately exact: it establishes a nonempty unbounded
family of constituted, discovered, validated, locally executed histories and a
same-input operational non-factorization result.  It does not introduce a
global completion marker and does not identify this concrete family with every
possible decision problem.
-/

namespace ConstitutiveSearch
namespace NPAndOrP

open Alignment
open StrongPerimetralTurning
open StrongPerimetralTurning.Example
open StrongPerimetralTurning.IteratedConstitutivePersistence
open StrongPerimetralTurning.Examples.ConcreteContinuation.LoggedAlgebra
open SAT

/-- Canonical nonempty history length assigned to an external input. -/
def resolutionLength (input : Nat) : Nat := input + 1

/-- Unary external encoding used by the complexity statement. -/
def encodeConstitutiveInput : Nat → List Unit
  | 0 => []
  | input + 1 => () :: encodeConstitutiveInput input

theorem encodeConstitutiveInput_length (input : Nat) :
    (encodeConstitutiveInput input).length = input := by
  induction input with
  | zero => rfl
  | succ input inductionHypothesis =>
      change (encodeConstitutiveInput input).length + 1 = input + 1
      rw [inductionHypothesis]

def resolutionProduction (input : Nat) : ConstitutiveProductionRun input (resolutionLength input) :=
  let initialized := initializeConstitutiveHistory input
  produceMeasuredConstitutiveHistory input (resolutionLength input) initialized.history.endpoint
    (congrArg RootedGeneratedHistory.endpoint initialized.historyExact)

/-- Entire constitutive history produced before operational traversal. -/
def resolutionGeneratedHistory (input : Nat) :
    CanonicalGeneratedHistory input (resolutionLength input) :=
  (resolutionProduction input).history

theorem resolutionGeneratedHistory_eq_reference (input : Nat) :
    resolutionGeneratedHistory input =
      produceCanonicalGeneratedHistory input (resolutionLength input) :=
  (resolutionProduction input).historyExact

/-- The actual causally threaded history for one external input. -/
def resolutionHistory (input : Nat) :
    SequentialHistory
      input
      (initialSequentialAssignment input)
      (resolutionLength input) :=
  executeSequentialHistory
    input
    (resolutionLength input)
    (initialSequentialAssignment input)

/--
Public result of the integrated concrete procedure.  Its only argument is the
external input; discovery, schedules, validation, returned code, applications,
terminal data, decision, and statistics are stored as produced descendants.
-/
structure ConstitutiveResolutionRun (input : Nat) where
  initialization : ConstitutiveInitializationRun input
  initializationExact : initialization = initializeConstitutiveHistory input
  production : ConstitutiveProductionRun input (resolutionLength input)
  productionExact : production = produceMeasuredConstitutiveHistory input (resolutionLength input)
    initialization.history.endpoint (congrArg RootedGeneratedHistory.endpoint initialization.historyExact)
  generatedHistory :
    CanonicalGeneratedHistory input (resolutionLength input)
  generatedHistoryExact :
    generatedHistory = resolutionGeneratedHistory input
  generatedHistoryFromProduction : generatedHistory = production.history
  history :
    SequentialHistory
      input
      (initialSequentialAssignment input)
      (resolutionLength input)
  historyExact : history = resolutionHistory input
  historyConsumesGeneration :
    executeGeneratedHistory
        generatedHistory
        (initialSequentialAssignment input) = history
  discoveryTraversal :
    GeneratedHistoryTraversalResult
      input
      (initialSequentialAssignment input)
      (resolutionLength input)
  discoveryTraversalExact :
    discoveryTraversal =
      discoverGeneratedHistoryTransportPath
        generatedHistory
        (initialSequentialAssignment input)
  discoveryTraversalExecutionExact :
    discoveryTraversal.execution? = some history
  discoveryTraversalRunsExact :
    discoveryTraversal.discoveryRuns = resolutionLength input
  successfulDiscoveriesExact :
    discoveryTraversal.successfulDiscoveries = resolutionLength input
  discoveryFailureAbsent : discoveryTraversal.failureDepth? = none
  acceptedHistory : AcceptedSequentialHistory history
  fullHistoryExecution : FullHistoryExecution history
  roleHistory : ConstitutiveRoleHistory history
  genericRefinement : GenericRefinedHistory history
  terminal : SequentialTerminalArtifact history
  terminalExact : terminal = terminalFromSequentialHistory history
  decision : Bool
  decisionExact : decision = decideSequentialTerminal terminal
  stats : SequentialHistoryStats
  statsExact : stats = history.stats
  measuredComparisonWork : ComparisonWork
  measuredComparisonWorkExact : measuredComparisonWork = history.measuredComparisonWork
  measuredConstructionWork : ComparisonWork
  measuredConstructionWorkExact : measuredConstructionWork = history.measuredConstructionWork
  measuredValidationWork : ComparisonWork
  measuredValidationWorkExact : measuredValidationWork = history.measuredValidationWork
  measuredExecutionWork : ComparisonWork
  measuredExecutionWorkExact : measuredExecutionWork = history.measuredExecutionWork
  measuredRealizationWork : ComparisonWork
  measuredRealizationWorkExact : measuredRealizationWork = discoveryTraversal.realizationWork
  structuralProfileCost : Nat
  structuralProfileCostExact : structuralProfileCost = history.totalStructuralProfileCost
  phaseAccounting : ResolutionPhaseAccounting
  phaseAccountingExact : phaseAccounting = history.phaseAccounting
  phaseAccountingTotalExact : phaseAccounting.total = structuralProfileCost
  projectionExperiment : IntegratedProjectionExperiment history.firstStage
  projectionExperimentExact :
    projectionExperiment = runIntegratedProjectionExperiment history.firstStage

/-- Execute the whole concrete procedure from the input alone. -/
def executeConstitutiveResolution
    (input : Nat) : ConstitutiveResolutionRun input :=
  let initialization := initializeConstitutiveHistory input
  let production := produceMeasuredConstitutiveHistory input (resolutionLength input)
    initialization.history.endpoint (congrArg RootedGeneratedHistory.endpoint initialization.historyExact)
  let generatedHistory := production.history
  let traversal :=
    discoverGeneratedHistoryTransportPath
      generatedHistory
      (initialSequentialAssignment input)
  have traversed :=
    discoverGeneratedHistoryTransportPath_exact
      generatedHistory
      (initialSequentialAssignment input)
  have traversalSuccess : traversal.execution? ≠ none := by
    rw [traversed.1]
    intro impossible
    cases impossible
  let history := traversal.successfulHistory traversalSuccess
  have traversalReturns : traversal.execution? = some history :=
    traversal.successfulHistory_exact traversalSuccess
  let terminal := terminalFromSequentialHistory history
  have consumed :
      executeGeneratedHistory
          generatedHistory
          (initialSequentialAssignment input) = history := by
    exact Option.some.inj (Eq.trans traversed.1.symm traversalReturns)
  have historyCanonical : history = resolutionHistory input := by
    have reference : generatedHistory =
        produceCanonicalGeneratedHistory input (resolutionLength input) :=
      resolutionGeneratedHistory_eq_reference input
    rw [reference] at consumed
    exact Eq.trans consumed.symm
      (executeProducedHistory_exact
        input
        (resolutionLength input)
        (initialSequentialAssignment input))
  { history := history
    initialization := initialization
    initializationExact := rfl
    production := production
    productionExact := rfl
    generatedHistory := generatedHistory
    generatedHistoryExact := rfl
    generatedHistoryFromProduction := rfl
    historyExact := historyCanonical
    historyConsumesGeneration := consumed
    discoveryTraversal := traversal
    discoveryTraversalExact := rfl
    discoveryTraversalExecutionExact := traversalReturns
    discoveryTraversalRunsExact := traversed.2.1
    successfulDiscoveriesExact := traversed.2.2.1
    discoveryFailureAbsent := traversed.2.2.2
    acceptedHistory := by
      rw [← consumed]
      exact
        executeGeneratedHistory_accepted
          generatedHistory
          (initialSequentialAssignment input)
    fullHistoryExecution := executeFullHistory history
    roleHistory := buildConstitutiveRoleHistory history
    terminal := terminal
    genericRefinement := executedHistory_genericRefinement history
    terminalExact := rfl
    decision := decideSequentialTerminal terminal
    decisionExact := rfl
    stats := history.stats
    statsExact := rfl
    measuredComparisonWork := history.measuredComparisonWork
    measuredComparisonWorkExact := rfl
    measuredConstructionWork := history.measuredConstructionWork
    measuredConstructionWorkExact := rfl
    measuredValidationWork := history.measuredValidationWork
    measuredValidationWorkExact := rfl
    measuredExecutionWork := history.measuredExecutionWork
    measuredExecutionWorkExact := rfl
    measuredRealizationWork := traversal.realizationWork
    measuredRealizationWorkExact := rfl
    structuralProfileCost := history.totalStructuralProfileCost
    structuralProfileCostExact := rfl
    phaseAccounting := history.phaseAccounting
    phaseAccountingExact := rfl
    phaseAccountingTotalExact := history.phaseAccounting_exact
    projectionExperiment := runIntegratedProjectionExperiment history.firstStage
    projectionExperimentExact := rfl }

/-- The number of actual producer calls is the nonconstant requested length. -/
theorem executeConstitutiveResolution_generatedSteps (input : Nat) :
    (executeConstitutiveResolution input).stats.generatedSteps = input + 1 := by
  rw [
    (executeConstitutiveResolution input).statsExact,
    (executeConstitutiveResolution input).historyExact
  ]
  exact
    executedHistory_generatedSteps
      input
      (resolutionLength input)
      (initialSequentialAssignment input)

/-- One discovered schedule atom is produced per generated stage. -/
theorem executeConstitutiveResolution_scheduleAtoms (input : Nat) :
    (executeConstitutiveResolution input).stats.scheduleAtoms = input + 1 := by
  rw [
    (executeConstitutiveResolution input).statsExact,
    (executeConstitutiveResolution input).historyExact
  ]
  exact
    executedHistory_scheduleAtoms
      input
      (resolutionLength input)
      (initialSequentialAssignment input)

/-- Validation performs one primitive query per generated stage. -/
theorem executeConstitutiveResolution_validationQueries (input : Nat) :
    (executeConstitutiveResolution input).stats.validationPrimitiveQueries =
      input + 1 := by
  rw [
    (executeConstitutiveResolution input).statsExact,
    (executeConstitutiveResolution input).historyExact
  ]
  exact
    executedHistory_validationQueries
      input
      (resolutionLength input)
      (initialSequentialAssignment input)

/-- Local execution performs one primitive query per generated stage. -/
theorem executeConstitutiveResolution_executionQueries (input : Nat) :
    (executeConstitutiveResolution input).stats.executionPrimitiveQueries =
      input + 1 := by
  rw [
    (executeConstitutiveResolution input).statsExact,
    (executeConstitutiveResolution input).historyExact
  ]
  exact
    executedHistory_executionQueries
      input
      (resolutionLength input)
      (initialSequentialAssignment input)

/-- Every code returned by the local runs is actually applied once. -/
theorem executeConstitutiveResolution_appliedAtoms (input : Nat) :
    (executeConstitutiveResolution input).stats.appliedCodeAtoms = input + 1 := by
  rw [
    (executeConstitutiveResolution input).statsExact,
    (executeConstitutiveResolution input).historyExact
  ]
  exact
    executedHistory_appliedAtoms
      input
      (resolutionLength input)
      (initialSequentialAssignment input)

/-- No global composition candidate is inspected anywhere in the history. -/
theorem executeConstitutiveResolution_noGlobalComposition (input : Nat) :
    (executeConstitutiveResolution input).stats.compositionCandidates = 0 := by
  rw [
    (executeConstitutiveResolution input).statsExact,
    (executeConstitutiveResolution input).historyExact
  ]
  exact
    executedHistory_compositionCandidates
      input
      (resolutionLength input)
      (initialSequentialAssignment input)

/--
All structural cardinalities are consequences of the objects already produced
by the run.  No numeric witness is accepted by the public procedure.
-/
theorem executeConstitutiveResolution_correspondences (input : Nat) :
    let run := executeConstitutiveResolution input
    run.generatedHistory.stepCount = input + 1 ∧
      run.stats.generatedSteps = input + 1 ∧
      run.discoveryTraversal.successfulDiscoveries = input + 1 ∧
      run.stats.scheduleAtoms = input + 1 ∧
      run.stats.appliedCodeAtoms = input + 1 ∧
      run.stats.validationPrimitiveQueries = input + 1 ∧
      run.stats.executionPrimitiveQueries = input + 1 ∧
      run.stats.compositionCandidates = 0 := by
  let run := executeConstitutiveResolution input
  exact
    ⟨by rw [run.generatedHistoryExact, resolutionGeneratedHistory_eq_reference];
        exact producedHistory_stepCount input (resolutionLength input),
      executeConstitutiveResolution_generatedSteps input,
      run.successfulDiscoveriesExact,
      executeConstitutiveResolution_scheduleAtoms input,
      executeConstitutiveResolution_appliedAtoms input,
      executeConstitutiveResolution_validationQueries input,
      executeConstitutiveResolution_executionQueries input,
      executeConstitutiveResolution_noGlobalComposition input⟩

/-- The final decision reads the terminal produced from the threaded history. -/
theorem executeConstitutiveResolution_decision_from_terminal (input : Nat) :
    (executeConstitutiveResolution input).decision =
      decideSequentialTerminal
        (executeConstitutiveResolution input).terminal :=
  (executeConstitutiveResolution input).decisionExact

/-- The decision is the alternating signal of actually applied trace atoms. -/
theorem executeConstitutiveResolution_decision (input : Nat) :
    (executeConstitutiveResolution input).decision =
      alternatingExecutionDecision (input + 1) := by
  let run := executeConstitutiveResolution input
  rw [run.decisionExact, run.terminalExact, run.historyExact]
  exact
    executedHistory_decision_exact
      input
      input
      (initialSequentialAssignment input)

/-- The family contains a concrete YES instance. -/
theorem executeConstitutiveResolution_zero_yes :
    (executeConstitutiveResolution 0).decision = true := by
  rw [executeConstitutiveResolution_decision]
  rfl

/-- The family contains a concrete NO instance. -/
theorem executeConstitutiveResolution_one_no :
    (executeConstitutiveResolution 1).decision = false := by
  rw [executeConstitutiveResolution_decision]
  rfl

/-- Successive external inputs execute strictly more constituted stages. -/
theorem resolution_generatedSteps_strict (input : Nat) :
    (executeConstitutiveResolution input).stats.generatedSteps <
      (executeConstitutiveResolution (input + 1)).stats.generatedSteps := by
  rw [
    executeConstitutiveResolution_generatedSteps,
    executeConstitutiveResolution_generatedSteps
  ]
  exact Nat.lt_succ_self (input + 1)

/--
Strict growth of the attempts accumulated by the complete integrated history.
-/
theorem resolution_discoveryAttempts_strict (input : Nat) :
    (executeConstitutiveResolution input).stats.discoveryAttempts <
      (executeConstitutiveResolution (input + 1)).stats.discoveryAttempts := by
  rw [(executeConstitutiveResolution input).statsExact,
    (executeConstitutiveResolution input).historyExact,
    (executeConstitutiveResolution (input + 1)).statsExact,
    (executeConstitutiveResolution (input + 1)).historyExact]
  unfold resolutionHistory
  rw [executedHistory_attemptCount, executedHistory_attemptCount]
  exact historyAttemptCount_integrated_strict input

theorem natFunction_strict_of_successor (function : Nat → Nat)
    (successor : ∀ input, function input < function (input + 1))
    {first second : Nat} (before : first < second) : function first < function second := by
  induction second with
  | zero => exact False.elim (Nat.not_lt_zero first before)
  | succ second ih =>
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ before) with
    | inl earlier => exact Nat.lt_trans (ih earlier) (successor second)
    | inr same => cases same; exact successor first

theorem resolution_discoveryAttempts_strict_between
    {first second : Nat} (before : first < second) :
    (executeConstitutiveResolution first).stats.discoveryAttempts <
      (executeConstitutiveResolution second).stats.discoveryAttempts :=
  natFunction_strict_of_successor _ resolution_discoveryAttempts_strict before

def resolutionStageSurfacePolynomial : CostPolynomial :=
  CostPolynomial.mul
    (CostPolynomial.add
      CostPolynomial.input
      (CostPolynomial.constant 1))
    (CostPolynomial.substitute
      sequentialStageSurfacePolynomial
      (CostPolynomial.add
        CostPolynomial.input
        (CostPolynomial.add
          CostPolynomial.input
          (CostPolynomial.constant 1))))

/-- Stage work plus all terminal parity reads and its final list observation. -/
def resolutionSurfacePolynomial : CostPolynomial :=
  CostPolynomial.add
    (CostPolynomial.add
      resolutionStageSurfacePolynomial
      (CostPolynomial.add
        CostPolynomial.input
        (CostPolynomial.constant 1)))
    (CostPolynomial.constant 1)

/-- The legacy structural profile is bounded by this cubic envelope. -/
theorem executeConstitutiveResolution_surface_le (input : Nat) :
    (executeConstitutiveResolution input).structuralProfileCost ≤
      resolutionSurfacePolynomial.eval input := by
  have historyBound :=
    executedHistory_cost_le
      input
      (resolutionLength input)
      (initialSequentialAssignment input)
  have terminalReads :=
    executedHistory_bits_length
      input
      (resolutionLength input)
      (initialSequentialAssignment input)
  rw [
    (executeConstitutiveResolution input).structuralProfileCostExact,
    (executeConstitutiveResolution input).historyExact
  ]
  change
    (resolutionHistory input).totalStructuralProfileCost ≤
      resolutionSurfacePolynomial.eval input
  unfold resolutionHistory
  unfold resolutionLength
  unfold resolutionLength at historyBound
  unfold resolutionLength at terminalReads
  unfold SequentialHistory.totalStructuralProfileCost
  rw [runTerminalReadout_visits]
  unfold resolutionSurfacePolynomial
  unfold resolutionStageSurfacePolynomial
  change
    (executeSequentialHistory
          input
          (input + 1)
          (initialSequentialAssignment input)).structuralProfileCost +
        (executeSequentialHistory
          input
          (input + 1)
          (initialSequentialAssignment input)).executedBits.length + 1 ≤
      ((input + 1) *
          (CostPolynomial.substitute
            sequentialStageSurfacePolynomial
            (CostPolynomial.add
              CostPolynomial.input
              (CostPolynomial.add
                CostPolynomial.input
                (CostPolynomial.constant 1)))).eval input +
        (input + 1)) + 1
  rw [CostPolynomial.eval_substitute]
  exact
    Nat.add_le_add
      (Nat.add_le_add
        historyBound
        (Nat.le_of_eq terminalReads))
      (Nat.le_refl 1)

/-- Polynomial bound on the legacy structural profile, not on complete runtime. -/
theorem constitutiveResolutionSurface_inputPolynomial :
    InputPolynomiallyBounded
      (fun input => (encodeConstitutiveInput input).length)
      (fun input => (executeConstitutiveResolution input).structuralProfileCost) := by
  refine ⟨resolutionSurfacePolynomial, ?_⟩
  intro input
  change
    (executeConstitutiveResolution input).structuralProfileCost ≤
      resolutionSurfacePolynomial.eval
        (encodeConstitutiveInput input).length
  rw [encodeConstitutiveInput_length]
  exact executeConstitutiveResolution_surface_le input

/--
Named causal obligations for one concrete stage.  This record makes the
phase-to-phase equalities inspectable without deriving any operational object
from the constitutive generation witness alone.
-/
structure ConstitutiveCausalStageEvidence (depth : Nat) : Type 2 where
  run : SequentialStageRun depth (initialSequentialAssignment depth)
  runExact : run =
    executeSequentialStage depth (initialSequentialAssignment depth)
  discoveryComesFromExecutedSearch :
    (stageRecordedDiscoveryRun (depth + 1)).outcome.discovered? =
      some run.discovery
  relationComesFromDiscovery :
    run.schedule.entry.relation = run.discovery.relation
  validationConsumesProducedSchedule :
    run.validated.run = runDiscoveryScheduleValidation run.schedule
  executionConsumesValidatedSchedule :
    run.execution.run = run.schedule.entry.executionRun
  returnedCodeComesFromDiscoveredRelation :
    run.execution.code = run.schedule.entry.code
  continuationComesFromReturnedCode :
    run.application.output =
      (run.execution.code.eval
        (generatedStructuralFlipAtAction
          (distinctGrowingDiscoveryFormula
            (constructStage (depth + 1)).searchIndex)
          run.schedule.entry.var)).map
        run.sourceContinuation
  sourceIsAccepted :
    GeneratedStructuralBranchAccept
      run.schedule.entry.source run.sourceContinuation
  outputIsAccepted :
    GeneratedStructuralBranchAccept
      run.schedule.entry.target run.application.output

def constitutiveCausalStageEvidence
    (depth : Nat) : ConstitutiveCausalStageEvidence depth :=
  let run := executeSequentialStage depth (initialSequentialAssignment depth)
  { run := run
    runExact := rfl
    discoveryComesFromExecutedSearch := run.discoveryExact
    relationComesFromDiscovery := concreteRelation_comes_from_discovery run
    validationConsumesProducedSchedule := run.validated.runExact
    executionConsumesValidatedSchedule := run.execution.runExact
    returnedCodeComesFromDiscoveredRelation :=
      executedDiscoverySchedule_code run.execution
    continuationComesFromReturnedCode := run.application.outputExact
    sourceIsAccepted := run.sourceAccepted
    outputIsAccepted := run.outputAccepted }

/--
The exact aggregate required by §6.  The fields do not reconstruct a second
execution: they expose, in one typed package, the equalities and recursive
witnesses already carried by the unique public run.
-/
structure Section6OperationalSuccessionEvidence {input : Nat}
    (run : ConstitutiveResolutionRun input) : Type 2 where
  sourceIsInitial :
    executeGeneratedHistory run.generatedHistory
        (initialSequentialAssignment input) = run.history
  discoveryTraversalReturnsHistory :
    run.discoveryTraversal.execution? = some run.history
  successionIsTyped : FullHistoryExecution run.history
  discoveryProvenanceIsRetained : GenericRefinedHistory run.history
  returnedCodesComeFromDiscoveredPath :
    run.history.localPath.map LocalPrimitiveAtom.compile = run.history.returnedCodes
  terminalComesFromExecution :
    run.terminal = terminalFromSequentialHistory run.history
  targetIsHistoryEndpoint :
    run.terminal.assignment = run.history.final.assignment
  executedAtomsAreGeneratedSteps :
    run.stats.appliedCodeAtoms = run.generatedHistory.stepCount
  compositionCandidatesAreZero :
    run.stats.compositionCandidates = 0
  terminalContinuationIsOperationalFold :
    run.terminal.assignment =
      foldOperationalSteps run.history.returnedCodes
        (initialSequentialAssignment input).assignment

def section6OperationalSuccessionEvidence {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    Section6OperationalSuccessionEvidence run :=
  { sourceIsInitial := run.historyConsumesGeneration
    discoveryTraversalReturnsHistory := run.discoveryTraversalExecutionExact
    successionIsTyped := run.fullHistoryExecution
    discoveryProvenanceIsRetained := run.genericRefinement
    returnedCodesComeFromDiscoveredPath := localPath_compiles_to_returnedCodes run.history
    terminalComesFromExecution := run.terminalExact
    targetIsHistoryEndpoint := run.terminal.assignmentExact
    executedAtomsAreGeneratedSteps := by
      calc
        run.stats.appliedCodeAtoms = input + 1 := by
          rw [run.statsExact, run.historyExact]
          exact executedHistory_appliedAtoms input (resolutionLength input)
            (initialSequentialAssignment input)
        _ = run.generatedHistory.stepCount := by
          rw [run.generatedHistoryExact, resolutionGeneratedHistory_eq_reference]
          exact (producedHistory_stepCount input (resolutionLength input)).symm
    compositionCandidatesAreZero := by
      rw [run.statsExact, run.historyExact]
      exact executedHistory_compositionCandidates input (resolutionLength input)
        (initialSequentialAssignment input)
    terminalContinuationIsOperationalFold :=
      Eq.trans run.terminal.assignmentExact
        (terminalAssignment_is_operational_fold run.history) }

/--
Exact evidence exposed for every input.  Each field names a construction or a
theorem already tied to the executed run; no conditional operational premise
is left open.
-/
structure ConstitutiveAndOrResolutionEvidence (input : Nat) : Type 3 where
  foundation : ConstitutiveStageFoundationEvidence input
  oldOccurrencesPersist :
    ∀ occurrence : History.Occurrence (constitutedHistory input).history,
      (successorOccurrenceSplit examplePresentation input).forward
          (.inl occurrence) =
        History.Occurrence.earlier occurrence
  freshOccurrenceRemainsDistinct :
    ∀ occurrence : History.Occurrence (constitutedHistory input).history,
      History.Occurrence.earlier occurrence ≠
        (History.Occurrence.last :
          History.Occurrence (constitutedHistory (input + 1)).history)
  provenancePersists :
    PreservesProvenance
      (constructStage input).history.endpoint
      (constructStage (input + 1)).history.endpoint
  occurrenceOrderPreserved :
    ∀ {first second : History.Occurrence (constitutedHistory input).history},
      History.OccurrencePrecedes first second →
        History.OccurrencePrecedes
          ((successorOccurrenceSplit examplePresentation input).forward (.inl first))
          ((successorOccurrenceSplit examplePresentation input).forward (.inl second))
  residualDifferencePreserved :
    FreshBoundaryDifference (constructStage input).history.endpoint
  realizationNaturality :
    ∀ {sourceDepth targetDepth : Nat}
      (extension : DepthExtension sourceDepth targetDepth)
      (occurrence :
        (iteratedRealization
          examplePresentation exampleConcreteAlgebra sourceDepth).Concrete),
      (((iteratedRealization
          examplePresentation exampleConcreteAlgebra targetDepth).transport
          (iteratedRealization
            examplePresentation loggedConcreteAlgebra targetDepth)).forward
        ((iteratedRealization
          examplePresentation exampleConcreteAlgebra sourceDepth).extend
          (iteratedRealization
            examplePresentation exampleConcreteAlgebra targetDepth)
          extension occurrence)) =
        (iteratedRealization
          examplePresentation loggedConcreteAlgebra sourceDepth).extend
          (iteratedRealization
            examplePresentation loggedConcreteAlgebra targetDepth)
          extension
          (((iteratedRealization
              examplePresentation exampleConcreteAlgebra sourceDepth).transport
            (iteratedRealization
              examplePresentation loggedConcreteAlgebra sourceDepth)).forward
              occurrence)
  realization : RealizedConstitutiveStage input
  realizationExact : realization = realizeConstitutedStage input
  interfaceRealizationExact :
    concreteConstitutiveOperationalInterface.realize
        (constitutedEndpoint input) =
      constitutedSearchIndex input
  causalStage : ConstitutiveCausalStageEvidence input
  run : ConstitutiveResolutionRun input
  runExact : run = executeConstitutiveResolution input
  generatedHistoryExact : run.stats.generatedSteps = input + 1
  generationCallsExact : run.stats.generateCalls = input + 1
  provenanceUnitsExact : run.stats.provenanceUnits = input + 1
  generationCertificatesExact :
    run.stats.generationCertificates = input + 1
  generatedObjectHasExactLength : run.generatedHistory.stepCount = input + 1
  operationalHistoryConsumesGeneratedObject :
    executeGeneratedHistory
        run.generatedHistory
        (initialSequentialAssignment input) = run.history
  failureAwareTraversalConsumesDiscovery :
    run.discoveryTraversal.execution? = some run.history
  discoveryRunsExact : run.discoveryTraversal.discoveryRuns = input + 1
  successfulDiscoveriesExact :
    run.discoveryTraversal.successfulDiscoveries = input + 1
  noDiscoveryFailure : run.discoveryTraversal.failureDepth? = none
  section6Succession : Section6OperationalSuccessionEvidence run
  acceptedExecutionHistory : AcceptedSequentialHistory run.history
  compiledPathIsReturnedCode :
    run.history.localPath.map LocalPrimitiveAtom.compile = run.history.returnedCodes
  producedPathLength : run.history.localPath.length = input + 1
  returnedCodeSize : compiledLocalSize run.history.returnedCodes = input + 1
  terminalAssignmentIsExecutedFold :
    run.history.final.assignment = foldOperationalSteps run.history.returnedCodes
      (initialSequentialAssignment input).assignment
  scheduleProductionExact : run.stats.scheduleAtoms = input + 1
  validationExact : run.stats.validationPrimitiveQueries = input + 1
  localExecutionExact : run.stats.executionPrimitiveQueries = input + 1
  applicationExact : run.stats.appliedCodeAtoms = input + 1
  relationQueriesAreAttempts :
    run.stats.relationQueries = run.stats.discoveryAttempts
  noGlobalComposition : run.stats.compositionCandidates = 0
  structuralProfileCostProduced : run.structuralProfileCost = run.history.totalStructuralProfileCost
  phaseAccountingProduced : run.phaseAccounting = run.history.phaseAccounting
  phaseAccountingSumExact :
    run.phaseAccounting.total = run.structuralProfileCost
  terminalReadoutInstrumented :
    run.terminal.readoutRun.bitVisits = run.terminal.observedBits.length
  structuralProfileCostPolynomial :
    run.structuralProfileCost ≤ resolutionSurfacePolynomial.eval input
  terminalProducedByHistory :
    run.terminal = terminalFromSequentialHistory run.history
  transportedBitsProducedByExecution :
    run.terminal.observedBits = run.history.executedBits
  terminalReadoutPreserved :
    run.terminal.executedVariables.map run.terminal.assignment = run.terminal.observedBits
  decisionReadsTerminalOnly :
    run.decision = decideSequentialTerminal run.terminal
  decisionReadsTransportedBits :
    run.decision = transportedBitParity run.terminal.observedBits
  projectionSplitComesFromConstitution :
    projectionSplitVar input =
      growingDiscoverySplitVar (constitutedSearchIndex input)
  projectionRootComesFromConstitution :
    projectionRootFormula input =
      symmetricBlockFamily
        (growingDiscoverySplitVar (constitutedSearchIndex input))
        (growingDiscoveryAnchorVar (constitutedSearchIndex input))
        []
  sameInputConstitutionsDistinct :
    (integratedMarkedTarget run.history.firstStage 2 (by decide)).context.decisions ≠
      (integratedMarkedTarget run.history.firstStage 4 (by decide)).context.decisions
  sameInputProjectionEqual :
    integratedInputProjection run.history.firstStage .compatible =
      integratedInputProjection run.history.firstStage .incompatible
  operationalProjectionNonFactorization :
    ¬ ValueFactorsThrough
        (integratedInputProjection run.history.firstStage)
        (fun organization => (integratedOrganizationObservation run.history.firstStage organization).terminalBit)
  projectionUsesSection31Primitives :
    Section31PrimitiveRaccord run.history.firstStage
  projectionPositiveCodeAtoms :
    run.projectionExperiment.positiveRun.codeAtoms = 1
  projectionNegativeCodeAtoms :
    run.projectionExperiment.negativeRun.codeAtoms = 0
  projectionRunsIntegrated :
    run.projectionExperiment = runIntegratedProjectionExperiment run.history.firstStage

/-- Closed construction of the exact evidence package for every input. -/
def constitutiveAndOrResolutionEvidence
    (input : Nat) : ConstitutiveAndOrResolutionEvidence input :=
  let run := executeConstitutiveResolution input
  { foundation := constitutiveStageFoundationEvidence input
    oldOccurrencesPersist := constitutedOldOccurrence_persists input
    freshOccurrenceRemainsDistinct := constitutedOldOccurrence_ne_fresh input
    occurrenceOrderPreserved := constitutedOccurrence_order_preserved input
    provenancePersists :=
      (constitutiveStageFoundationEvidence input).provenancePersists
    residualDifferencePreserved :=
      (constitutiveStageFoundationEvidence input).residualDifferenceRemainsFresh
    realizationNaturality :=
      constitutedRealization_natural
        exampleConcreteAlgebra loggedConcreteAlgebra
    realization := realizeConstitutedStage input
    realizationExact := rfl
    interfaceRealizationExact :=
      concreteInterface_realize_constitutedEndpoint input
    causalStage := constitutiveCausalStageEvidence input
    run := run
    runExact := rfl
    generatedHistoryExact :=
      executeConstitutiveResolution_generatedSteps input
    generationCallsExact :=
      by
        rw [run.statsExact, run.historyExact]
        exact
          executedHistory_generateCalls
            input
            (resolutionLength input)
            (initialSequentialAssignment input)
    provenanceUnitsExact :=
      by
        rw [run.statsExact, run.historyExact]
        exact
          executedHistory_provenanceUnits
            input
            (resolutionLength input)
            (initialSequentialAssignment input)
    generationCertificatesExact :=
      by
        rw [run.statsExact, run.historyExact]
        exact
          executedHistory_generationCertificates
            input
            (resolutionLength input)
            (initialSequentialAssignment input)
    generatedObjectHasExactLength := by
      rw [run.generatedHistoryExact, resolutionGeneratedHistory_eq_reference]
      exact producedHistory_stepCount input (resolutionLength input)
    operationalHistoryConsumesGeneratedObject :=
      run.historyConsumesGeneration
    failureAwareTraversalConsumesDiscovery :=
      run.discoveryTraversalExecutionExact
    discoveryRunsExact := run.discoveryTraversalRunsExact
    successfulDiscoveriesExact := run.successfulDiscoveriesExact
    noDiscoveryFailure := run.discoveryFailureAbsent
    section6Succession := section6OperationalSuccessionEvidence run
    acceptedExecutionHistory := run.acceptedHistory
    compiledPathIsReturnedCode := localPath_compiles_to_returnedCodes run.history
    producedPathLength := localPath_length run.history
    returnedCodeSize := returnedCodes_size run.history
    terminalAssignmentIsExecutedFold := terminalAssignment_is_operational_fold run.history
    scheduleProductionExact :=
      executeConstitutiveResolution_scheduleAtoms input
    validationExact :=
      executeConstitutiveResolution_validationQueries input
    localExecutionExact :=
      executeConstitutiveResolution_executionQueries input
    applicationExact :=
      executeConstitutiveResolution_appliedAtoms input
    relationQueriesAreAttempts :=
      by
        rw [run.statsExact, run.historyExact]
        exact
          executedHistory_relationQueries
            input
            (resolutionLength input)
            (initialSequentialAssignment input)
    noGlobalComposition :=
      executeConstitutiveResolution_noGlobalComposition input
    structuralProfileCostProduced := run.structuralProfileCostExact
    phaseAccountingProduced := run.phaseAccountingExact
    phaseAccountingSumExact := run.phaseAccountingTotalExact
    terminalReadoutInstrumented := by
      rw [run.terminal.readoutRunExact]
      exact runTerminalReadout_visits _
    structuralProfileCostPolynomial :=
      executeConstitutiveResolution_surface_le input
    terminalProducedByHistory := run.terminalExact
    transportedBitsProducedByExecution :=
      run.terminal.observedBitsExact
    terminalReadoutPreserved := by
      rw [run.terminal.executedVariablesExact, run.terminal.assignmentExact,
        run.terminal.observedBitsExact]
      exact run.history.readout_preserved
    decisionReadsTerminalOnly := run.decisionExact
    decisionReadsTransportedBits := by
      calc
        run.decision = run.terminal.decisionBit := run.decisionExact
        _ = run.terminal.readoutRun.decision :=
          run.terminal.decisionBitExact
        _ = (runTerminalReadout run.terminal.observedBits).decision :=
          congrArg
            (fun readout : TerminalReadoutRun => readout.decision)
            run.terminal.readoutRunExact
        _ = transportedBitParity run.terminal.observedBits :=
          runTerminalReadout_decision _
    projectionSplitComesFromConstitution :=
      projectionSplitVar_from_constitution input
    projectionRootComesFromConstitution :=
      projectionRootFormula_from_constitution input
    sameInputConstitutionsDistinct :=
      integrated_marked_constitutions_distinct run.history.firstStage
    sameInputProjectionEqual := congrArg (fun formula => (input, formula))
      (integrated_marked_projection_equal run.history.firstStage)
    operationalProjectionNonFactorization :=
      integrated_projection_not_factors run.history.firstStage
    projectionUsesSection31Primitives := run.projectionExperiment.section31Raccord
    projectionPositiveCodeAtoms := run.projectionExperiment.positiveCodeAtoms
    projectionNegativeCodeAtoms := run.projectionExperiment.negativeCodeAtoms
    projectionRunsIntegrated := run.projectionExperimentExact }

/-- Execution retains the precise generated steps supplied to its traversal. -/
theorem ConstitutiveResolutionRun.generatorsExact {input : Nat} (run : ConstitutiveResolutionRun input) :
    run.history.generatedHistory = run.generatedHistory := by
  rw [← run.historyConsumesGeneration]
  exact executedGeneratedHistory_retains_generators _ _

/-- The generic traversal returns the actual local discoveries of the public run.
HEq accounts only for the proved equality of the two history indices. -/
theorem ConstitutiveResolutionRun.genericTraversalExact {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    HEq (concreteConstitutiveOperationalInterface.discoverHistory run.generatedHistory.asGeneric)
      (some run.history.genericDiscovered) := by
  rw [← run.generatorsExact]
  exact heq_of_eq (executedHistory_genericTraversal run.history)

/-- Only the four instrumented search/construction subprograms, not total run cost. -/
def ConstitutiveResolutionRun.measuredSearchWork {input : Nat} (run : ConstitutiveResolutionRun input) : Nat :=
  (run.measuredComparisonWork.add run.measuredConstructionWork).total +
    (run.measuredValidationWork.add run.measuredExecutionWork).total

def resolutionMeasuredSearchPolynomial : CostPolynomial :=
  let count : CostPolynomial := .add .input (.constant 1)
  let last : CostPolynomial := .add .input count
  .add (.mul count (stageDiscoveryPolynomial last))
    (.mul count (.add (stageRelationPolynomial last) (stageRelationPolynomial last)))

theorem ConstitutiveResolutionRun.measuredSearchWork_bound {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.measuredSearchWork ≤ resolutionMeasuredSearchPolynomial.eval input := by
  unfold ConstitutiveResolutionRun.measuredSearchWork
  rw [run.measuredComparisonWorkExact, run.measuredConstructionWorkExact,
    run.measuredValidationWorkExact, run.measuredExecutionWorkExact]
  exact Nat.add_le_add (historyDiscovery_measured_bound run.history)
    (historyValidationExecution_measured_bound run.history)

/-- Polynomial bound on actual measured subprogram work, relative to the
executable unary input encoding. Initialization and driver costs are excluded. -/
theorem constitutiveMeasuredSearch_inputPolynomial :
    InputPolynomiallyBounded (fun input => (encodeConstitutiveInput input).length)
      (fun input => (executeConstitutiveResolution input).measuredSearchWork) := by
  refine ⟨resolutionMeasuredSearchPolynomial, ?_⟩
  intro input
  dsimp only
  rw [encodeConstitutiveInput_length]
  exact (executeConstitutiveResolution input).measuredSearchWork_bound

def resolutionTerminalReadPolynomial : CostPolynomial :=
  let count : CostPolynomial := .add .input (.constant 1)
  let last : CostPolynomial := .add .input count
  let largest : CostPolynomial := .add (.mul (.constant 2) (.add last (.constant 3))) (.constant 2)
  let reading : CostPolynomial := .add (.add largest (.constant 1))
    (.mul count (.add largest (.constant 2)))
  .add (.add (.add (.add count (.constant 1))
    (.add (.mul (.add reading (.constant 1)) count) (.constant 1))) reading) count

theorem ConstitutiveResolutionRun.terminalReadWork_bound {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.terminal.measuredReadWork ≤ resolutionTerminalReadPolynomial.eval input := by
  rw [run.terminalExact, run.historyExact]
  have bounded := concreteTerminalReadWork_bound input input
  dsimp only at bounded
  have labelExact : stageSelectedVar (input + (input + 1)) =
      2 * ((input + (input + 1)) + 3) + 2 := by
    change constitutedSearchIndex (input + (input + 1)) + 2 = _
    rw [constitutedSearchIndex_exact]
  rw [labelExact] at bounded
  exact bounded

def resolutionRealizationPolynomial : CostPolynomial :=
  let count : CostPolynomial := .add .input (.constant 1)
  let last : CostPolynomial := .add .input count
  .mul count (.add (.mul (.constant 2)
    (.add (.mul (.constant 2) (.add last (.constant 3))) (.constant 1))) (.constant 16))

theorem ConstitutiveResolutionRun.realizationWork_bound {input : Nat}
    (run : ConstitutiveResolutionRun input) :
    run.measuredRealizationWork.total ≤ resolutionRealizationPolynomial.eval input := by
  rw [run.measuredRealizationWorkExact, run.discoveryTraversalExact]
  exact generatedHistoryRealizationWork_bound run.generatedHistory _

/-- Count producer invocations once. Appended steps and provenance indicators
describe their outputs; they are deliberately not added as duplicate calls. -/
def ConstitutiveResolutionRun.productionCalls {input : Nat} (run : ConstitutiveResolutionRun input) : Nat :=
  run.initialization.generateCalls + run.production.generateCalls

theorem ConstitutiveResolutionRun.productionCalls_exact {input : Nat}
    (run : ConstitutiveResolutionRun input) : run.productionCalls = input + (input + 1) := by
  unfold ConstitutiveResolutionRun.productionCalls
  rw [run.productionExact]
  rw [(produceMeasuredConstitutiveHistory_counts input (resolutionLength input) _ _).1]
  rw [run.initializationExact, (initializeConstitutiveHistory_counts input).1]
  rfl

end NPAndOrP
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NPAndOrP.ConstitutiveResolutionRun.terminalReadWork_bound
#print axioms ConstitutiveSearch.NPAndOrP.ConstitutiveResolutionRun.realizationWork_bound
#print axioms ConstitutiveSearch.NPAndOrP.ConstitutiveResolutionRun.productionCalls
#print axioms ConstitutiveSearch.NPAndOrP.ConstitutiveResolutionRun.productionCalls_exact
#print axioms ConstitutiveSearch.NPAndOrP.resolutionProduction
#print axioms ConstitutiveSearch.NPAndOrP.ConstitutiveResolutionRun.measuredSearchWork
#print axioms ConstitutiveSearch.NPAndOrP.ConstitutiveResolutionRun.measuredSearchWork_bound
#print axioms ConstitutiveSearch.NPAndOrP.constitutiveMeasuredSearch_inputPolynomial
#print axioms ConstitutiveSearch.NPAndOrP.ConstitutiveResolutionRun.generatorsExact
#print axioms ConstitutiveSearch.NPAndOrP.ConstitutiveResolutionRun.genericTraversalExact
#print axioms ConstitutiveSearch.NPAndOrP.resolution_discoveryAttempts_strict_between
#print axioms ConstitutiveSearch.NPAndOrP.resolutionGeneratedHistory_eq_reference
#print axioms ConstitutiveSearch.NPAndOrP.resolution_discoveryAttempts_strict
#print axioms ConstitutiveSearch.NPAndOrP.executeConstitutiveResolution
#print axioms ConstitutiveSearch.NPAndOrP.encodeConstitutiveInput_length
#print axioms ConstitutiveSearch.NPAndOrP.executeConstitutiveResolution_decision_from_terminal
#print axioms ConstitutiveSearch.NPAndOrP.executeConstitutiveResolution_decision
#print axioms ConstitutiveSearch.NPAndOrP.executeConstitutiveResolution_zero_yes
#print axioms ConstitutiveSearch.NPAndOrP.executeConstitutiveResolution_one_no
#print axioms ConstitutiveSearch.NPAndOrP.executeConstitutiveResolution_noGlobalComposition
#print axioms ConstitutiveSearch.NPAndOrP.executeConstitutiveResolution_correspondences
#print axioms ConstitutiveSearch.NPAndOrP.resolution_generatedSteps_strict
#print axioms ConstitutiveSearch.NPAndOrP.executeConstitutiveResolution_surface_le
#print axioms ConstitutiveSearch.NPAndOrP.constitutiveResolutionSurface_inputPolynomial
#print axioms ConstitutiveSearch.NPAndOrP.constitutiveCausalStageEvidence
#print axioms ConstitutiveSearch.NPAndOrP.section6OperationalSuccessionEvidence
#print axioms ConstitutiveSearch.NPAndOrP.constitutiveAndOrResolutionEvidence
/- AXIOM_AUDIT_END -/
