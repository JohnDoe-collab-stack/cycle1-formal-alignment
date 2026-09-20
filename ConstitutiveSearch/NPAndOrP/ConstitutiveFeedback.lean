import ConstitutiveSearch.NPAndOrP.ConstitutiveFullStep

/-!
# Constitutive feedback into the next discovery

This layer refines the already executed sequential history.  It does not
replace `GeneratedStep` by an operational relation.  Instead, it threads the
assignment returned by the executed code together with the ordered AND
decisions and their provenance.  The next candidate list is produced only
after that transmitted state has been inspected.
-/

namespace ConstitutiveSearch.NPAndOrP

open SAT

/-- Executed scan of the transmitted determinations.  `available = false`
means that the variable governing the next local relation was already fixed. -/
structure TransmittedDecisionInspection where
  available : Bool
  visits : Nat

def inspectTransmittedDecisions (selected : Var) :
    (decisions : List StructuralBranchDecision) →
      TransmittedDecisionInspection
  | decisions =>
      ⟨structuralDecisionsAvoidCheck selected decisions, decisions.length⟩

theorem structuralDecisionsAvoidCheck_true_of_avoid
    (selected : Var) (decisions : List StructuralBranchDecision)
    (avoid : StructuralDecisionsAvoid selected decisions) :
    structuralDecisionsAvoidCheck selected decisions = true := by
  induction decisions with
  | nil => rfl
  | cons decision rest inductionHypothesis =>
      rw [structuralDecisionsAvoidCheck]
      rw [if_neg avoid.1]
      exact inductionHypothesis avoid.2

theorem inspectTransmittedDecisions_available_of_all_lt
    (selected : Var) (decisions : List StructuralBranchDecision)
    (before : ∀ decision, decision ∈ decisions → decision.var < selected) :
    (inspectTransmittedDecisions selected decisions).available = true := by
  apply structuralDecisionsAvoidCheck_true_of_avoid
  induction decisions with
  | nil => exact True.intro
  | cons decision rest inductionHypothesis =>
      constructor
      · exact Nat.ne_of_lt (before decision (List.Mem.head rest))
      · apply inductionHypothesis
        intro prior member
        exact before prior (List.Mem.tail decision member)

theorem inspectTransmittedDecisions_visits_of_all_ne
    (selected : Var) (decisions : List StructuralBranchDecision)
    (_different : ∀ decision, decision ∈ decisions → decision.var ≠ selected) :
    (inspectTransmittedDecisions selected decisions).visits = decisions.length := by
  rfl

/-- The state transmitted between stages.  `assignment.reader` is the reader
produced by the preceding transport interpreter.  Decisions and provenance are
stored newest first, so their exact common order remains computational data. -/
structure ThreadedConstitutiveState (depth : Nat)
    (assignment : SequentialAssignment depth) where
  threadedAssignment : SequentialAssignment depth
  threadedAssignmentExact : threadedAssignment = assignment
  generation : CanonicalStageGeneration depth
  decisions : List StructuralBranchDecision
  provenance : List Var
  provenanceExact : provenance = decisions.map (fun decision => decision.var)
  decisionsHold : StructuralDecisionsHold assignment.assignment decisions
  decisionsBeforeNext :
    ∀ decision, decision ∈ decisions →
      decision.var < stageSelectedVar (depth + 1)

def initialThreadedConstitutiveState (depth : Nat) :
    ThreadedConstitutiveState depth (initialSequentialAssignment depth) :=
  { threadedAssignment := initialSequentialAssignment depth
    threadedAssignmentExact := rfl
    generation := generateCanonicalStage depth
    decisions := []
    provenance := []
    provenanceExact := rfl
    decisionsHold := True.intro
    decisionsBeforeNext := by intro _ impossible; cases impossible }

theorem structuralDecisionsAvoid_of_all_lt
    (selected : Var) (decisions : List StructuralBranchDecision)
    (before : ∀ decision, decision ∈ decisions → decision.var < selected) :
    StructuralDecisionsAvoid selected decisions := by
  induction decisions with
  | nil => exact True.intro
  | cons decision rest inductionHypothesis =>
      constructor
      · exact Nat.ne_of_lt (before decision (List.Mem.head rest))
      · apply inductionHypothesis
        intro prior member
        exact before prior (List.Mem.tail decision member)

theorem ThreadedConstitutiveState.decisionsAvoidNext
    {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) :
    StructuralDecisionsAvoid (stageSelectedVar (depth + 1)) state.decisions := by
  exact structuralDecisionsAvoid_of_all_lt _ _ state.decisionsBeforeNext

/-- Single executable engine used both by the active threaded state and by
the same-projection separator. -/
structure FeedbackDiscoveryFromDataRun (depth : Nat)
    (generation : CanonicalStageGeneration depth)
    (decisions : List StructuralBranchDecision) where
  generated : GeneratedDiscoveryBundle generation
  generatedExact : generated = measuredGeneratedDiscovery generation
  inspection : TransmittedDecisionInspection
  inspectionExact : inspection =
    inspectTransmittedDecisions (stageSelectedVar (depth + 1)) decisions
  candidates : List Var
  candidatesExact : candidates =
    if inspection.available then generated.recorded.extraction.candidates else []
  outcome : RecordedDiscoveryOutcome (constructStage (depth + 1)).operationalRoot
  outcomeExact : outcome = exploreRecordedCandidates
    (constructStage (depth + 1)).operationalRoot candidates

def runFeedbackDiscoveryFromData (depth : Nat)
    (generation : CanonicalStageGeneration depth)
    (decisions : List StructuralBranchDecision) :
    FeedbackDiscoveryFromDataRun depth generation decisions :=
  let generated := measuredGeneratedDiscovery generation
  let inspection := inspectTransmittedDecisions (stageSelectedVar (depth + 1)) decisions
  let candidates := if inspection.available then generated.recorded.extraction.candidates else []
  { generated := generated
    generatedExact := rfl
    inspection := inspection
    inspectionExact := rfl
    candidates := candidates
    candidatesExact := rfl
    outcome := exploreRecordedCandidates (constructStage (depth + 1)).operationalRoot candidates
    outcomeExact := rfl }

/-- Discovery executed from a generated target after inspecting the complete
transmitted AND history.  If the next split is already determined, no local
candidate is admitted and the ordinary optional failure branch is taken. -/
structure ThreadedNextDiscoveryRun (depth : Nat)
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) where
  generated : GeneratedDiscoveryBundle state.generation
  generatedExact : generated = measuredGeneratedDiscovery state.generation
  inspection :
    TransmittedDecisionInspection
  inspectionExact : inspection =
    inspectTransmittedDecisions (stageSelectedVar (depth + 1)) state.decisions
  candidates : List Var
  candidatesExact : candidates =
    if inspection.available then generated.recorded.extraction.candidates else []
  outcome : RecordedDiscoveryOutcome (constructStage (depth + 1)).operationalRoot
  outcomeExact : outcome =
    exploreRecordedCandidates (constructStage (depth + 1)).operationalRoot candidates

def runThreadedNextDiscovery {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) :
    ThreadedNextDiscoveryRun depth state :=
  let core := runFeedbackDiscoveryFromData depth state.generation state.decisions
  { generated := core.generated
    generatedExact := core.generatedExact
    inspection := core.inspection
    inspectionExact := core.inspectionExact
    candidates := core.candidates
    candidatesExact := core.candidatesExact
    outcome := core.outcome
    outcomeExact := core.outcomeExact }

def ThreadedNextDiscoveryRun.asRecorded {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ThreadedNextDiscoveryRun depth state) :
    RecordedStageDiscoveryRun (constructStage (depth + 1)).operationalRoot :=
  { extraction := run.generated.recorded.extraction
    outcome := run.outcome }

theorem runThreadedNextDiscovery_exact {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) :
    (runThreadedNextDiscovery state).asRecorded =
      stageRecordedDiscoveryRun (depth + 1) := by
  have available := inspectTransmittedDecisions_available_of_all_lt
    (stageSelectedVar (depth + 1)) state.decisions
    state.decisionsBeforeNext
  unfold ThreadedNextDiscoveryRun.asRecorded runThreadedNextDiscovery
    runFeedbackDiscoveryFromData
  dsimp only
  rw [available]
  rw [(measuredGeneratedDiscovery state.generation).recordedExact]
  rfl

theorem runThreadedNextDiscovery_found {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) :
    (runThreadedNextDiscovery state).outcome.discovered? ≠ none := by
  have exactRun := runThreadedNextDiscovery_exact state
  change (runThreadedNextDiscovery state).asRecorded.outcome.discovered? ≠ none
  rw [exactRun]
  exact stageRecordedDiscovery_ne_none (depth + 1)

/-- Recursive append producer for chronological provenance. -/
structure ProvenanceAppendRun (history : List Var) (next : Var) where
  output : List Var
  outputExact : output = history ++ [next]
  visits : Nat
  visitsExact : visits = history.length + 1

def appendProvenanceMeasured (next : Var) :
    (history : List Var) → ProvenanceAppendRun history next
  | [] => ⟨[next], rfl, 1, rfl⟩
  | head :: tail =>
      let suffix := appendProvenanceMeasured next tail
      { output := head :: suffix.output
        outputExact := by rw [suffix.outputExact]; rfl
        visits := suffix.visits + 1
        visitsExact := by rw [suffix.visitsExact]; rfl }

/-- Constant-time producer for newest-first provenance. -/
structure ProvenancePrependRun (history : List Var) (next : Var) where
  output : List Var
  outputExact : output = next :: history
  visits : Nat
  visitsExact : visits = 1

def prependProvenanceMeasured (next : Var) (history : List Var) :
    ProvenancePrependRun history next :=
  ⟨next :: history, rfl, 1, rfl⟩

theorem structuralDecisionsHold_transport
    (before after : Assignment) (decisions : List StructuralBranchDecision)
    (held : StructuralDecisionsHold before decisions)
    (preserved : ∀ decision, decision ∈ decisions →
      after decision.var = before decision.var) :
    StructuralDecisionsHold after decisions := by
  induction decisions with
  | nil => exact True.intro
  | cons decision rest inductionHypothesis =>
      constructor
      · rw [preserved decision (List.Mem.head rest)]
        exact held.1
      · apply inductionHypothesis
        · exact held.2
        · intro prior member
          exact preserved prior (List.Mem.tail decision member)

theorem stageNext_preserves_threadedDecisions {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (stage : SequentialStageRun depth assignment) :
    StructuralDecisionsHold stage.next.assignment state.decisions := by
  apply structuralDecisionsHold_transport
    assignment.assignment stage.next.assignment state.decisions state.decisionsHold
  intro decision member
  have different : decision.var ≠ stageSelectedVar (depth + 1) :=
    Nat.ne_of_lt (state.decisionsBeforeNext decision member)
  rw [sequentialStage_next_from_input, Assignment.flipAt_other]
  rw [sequentialStage_selected_exact]
  exact different

/-- Instrumented realization of the complete next state.  It consumes the
actual generated target, the executed continuation and the accumulated AND
history; the next discovery is then computed from the returned state. -/
structure NextOperationalStateRun {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (stage : SequentialStageRun depth assignment) where
  provenanceRun : ProvenancePrependRun state.provenance (stageSelectedVar (depth + 1))
  next : ThreadedConstitutiveState (depth + 1) stage.next
  assignmentFromExecution : next.threadedAssignment.assignment = stage.next.assignment
  generationFromProducedTarget :
    next.generation =
      generateCanonicalStageFromSource state.generation.target state.generation.targetExact
  decisionsFromExecution :
    next.decisions =
      ⟨stageSelectedVar (depth + 1), true⟩ :: state.decisions
  provenanceFromExecution :
    next.provenance = stageSelectedVar (depth + 1) :: state.provenance
  decisionAccumulationWork : Nat
  decisionAccumulationWorkExact : decisionAccumulationWork = 1
  provenanceWork : Nat
  provenanceWorkExact : provenanceWork = provenanceRun.visits
  stateInspectionWork : Nat
  stateInspectionWorkExact :
    stateInspectionWork = (runThreadedNextDiscovery next).inspection.visits

def realizeNextOperationalState {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (stage : SequentialStageRun depth assignment) :
    NextOperationalStateRun state stage := by
  let selected := stageSelectedVar (depth + 1)
  let provenanceRun := prependProvenanceMeasured selected state.provenance
  let nextGeneration :=
    generateCanonicalStageFromSource state.generation.target state.generation.targetExact
  have selectedTrue : stage.next.assignment selected = true := by
    rw [sequentialStage_next_from_input, sequentialStage_selected_exact,
      Assignment.flipAt_selected, assignment.futureSelectedFalse _ (Nat.le_refl _)]
    rfl
  have oldHold : StructuralDecisionsHold stage.next.assignment state.decisions :=
    stageNext_preserves_threadedDecisions state stage
  have oldBeforeNext :
      ∀ decision, decision ∈ state.decisions →
        decision.var < stageSelectedVar ((depth + 1) + 1) := by
    intro decision member
    exact Nat.lt_trans (state.decisionsBeforeNext decision member)
      (by rw [stageSelectedVar_succ]; exact Nat.lt_add_of_pos_right (by decide))
  have selectedBeforeNext :
      selected < stageSelectedVar ((depth + 1) + 1) := by
    rw [stageSelectedVar_succ]
    exact Nat.lt_add_of_pos_right (by decide)
  let next : ThreadedConstitutiveState (depth + 1) stage.next :=
    { threadedAssignment := stage.next
      threadedAssignmentExact := rfl
      generation := nextGeneration
      decisions := ⟨selected, true⟩ :: state.decisions
      provenance := provenanceRun.output
      provenanceExact := by
        rw [provenanceRun.outputExact, state.provenanceExact]
        rfl
      decisionsHold := ⟨selectedTrue, oldHold⟩
      decisionsBeforeNext := by
        intro decision member
        cases member with
        | head => exact selectedBeforeNext
        | tail _ prior => exact oldBeforeNext decision prior }
  exact
    { provenanceRun := provenanceRun
      next := next
      assignmentFromExecution := rfl
      generationFromProducedTarget := rfl
      decisionsFromExecution := rfl
      provenanceFromExecution := provenanceRun.outputExact
      decisionAccumulationWork := 1
      decisionAccumulationWorkExact := rfl
      provenanceWork := provenanceRun.visits
      provenanceWorkExact := rfl
      stateInspectionWork := (runThreadedNextDiscovery next).inspection.visits
      stateInspectionWorkExact := rfl }

/-- One existing P stage refined by the state that actually feeds its
discovery and by the fully realized state returned to the following stage. -/
structure ThreadedConstitutiveStageRun {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (stage : SequentialStageRun depth assignment) where
  discoveryRun : ThreadedNextDiscoveryRun depth state
  discoveryRunExact : discoveryRun = runThreadedNextDiscovery state
  relationFromTransmittedState :
    discoveryRun.outcome.discovered? = some stage.discovery
  returnedCodeFromThatRelation : stage.execution.code = stage.schedule.entry.code
  executedOutputFromThatCode :
    stage.application.output =
      (stage.execution.code.eval
        (generatedStructuralFlipAtAction
          (distinctGrowingDiscoveryFormula (constructStage (depth + 1)).searchIndex)
          stage.schedule.entry.var)).map stage.sourceContinuation
  nextRun : NextOperationalStateRun state stage

def executeThreadedConstitutiveStage {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (stage : SequentialStageRun depth assignment) :
    ThreadedConstitutiveStageRun state stage := by
  let discoveryRun := runThreadedNextDiscovery state
  have found : discoveryRun.outcome.discovered? = some stage.discovery := by
    have exactRun := runThreadedNextDiscovery_exact state
    change discoveryRun.asRecorded.outcome.discovered? = some stage.discovery
    rw [exactRun]
    exact stage.discoveryExact
  exact
    { discoveryRun := discoveryRun
      discoveryRunExact := rfl
      relationFromTransmittedState := found
      returnedCodeFromThatRelation := executedDiscoverySchedule_code stage.execution
      executedOutputFromThatCode := stage.application.outputExact
      nextRun := realizeNextOperationalState state stage }

/-- The active tail is indexed by the complete state returned by the head. -/
inductive ConstitutiveExecutionHistory :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      (state : ThreadedConstitutiveState depth assignment) →
      SequentialHistory depth assignment count → Type 2 where
  | nil {depth : Nat} {assignment : SequentialAssignment depth}
      (state : ThreadedConstitutiveState depth assignment) :
      ConstitutiveExecutionHistory state (.nil depth assignment)
  | step {depth count : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      (head : SequentialStageRun depth assignment)
      (tail : SequentialHistory (depth + 1) head.next count)
      (headRun : ThreadedConstitutiveStageRun state head)
      (tailRun : ConstitutiveExecutionHistory headRun.nextRun.next tail) :
      ConstitutiveExecutionHistory state (.step head tail)

/-- Consume an already produced sequential history.  This is the unique
feedback traversal: it does not reconstruct a second success history from the
external input. -/
def threadConstitutiveExecutionHistory :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      (history : SequentialHistory depth assignment count) →
      (state : ThreadedConstitutiveState depth assignment) →
      ConstitutiveExecutionHistory state history
  | _, _, _, .nil _ _, state => .nil state
  | _, _, _, .step head tail, state =>
      let headRun := executeThreadedConstitutiveStage state head
      .step head tail headRun
        (threadConstitutiveExecutionHistory tail headRun.nextRun.next)

def executeConstitutiveExecutionHistory
    (depth count : Nat) (assignment : SequentialAssignment depth)
    (state : ThreadedConstitutiveState depth assignment) :
    ConstitutiveExecutionHistory state
      (executeSequentialHistory depth count assignment) :=
  threadConstitutiveExecutionHistory
    (executeSequentialHistory depth count assignment) state

/-- Accounting emitted by the feedback recursion itself.  Extraction and
next-discovery work remain owned by the existing extraction/discovery phases;
they are not added again here. -/
structure ConstitutiveFeedbackStats where
  decisionAccumulations : Nat
  provenanceVisits : Nat
  transmittedStateInspections : Nat
  deriving DecidableEq, Repr

def ConstitutiveFeedbackStats.zero : ConstitutiveFeedbackStats := ⟨0, 0, 0⟩

def ConstitutiveFeedbackStats.addStage (stats : ConstitutiveFeedbackStats)
    {depth : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) : ConstitutiveFeedbackStats :=
  { decisionAccumulations := stats.decisionAccumulations + run.nextRun.decisionAccumulationWork
    provenanceVisits := stats.provenanceVisits + run.nextRun.provenanceWork
    transmittedStateInspections :=
      stats.transmittedStateInspections + run.discoveryRun.inspection.visits }

def ConstitutiveExecutionHistory.feedbackStats :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : SequentialHistory depth assignment count} →
      ConstitutiveExecutionHistory state history → ConstitutiveFeedbackStats
  | _, _, _, _, _, .nil _ => .zero
  | _, _, _, _, _, .step _ _ headRun tailRun =>
      tailRun.feedbackStats.addStage headRun

theorem ConstitutiveExecutionHistory.decisionAccumulations_eq_count
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : SequentialHistory depth assignment count}
    (run : ConstitutiveExecutionHistory state history) :
    run.feedbackStats.decisionAccumulations = count := by
  induction run with
  | nil => rfl
  | step head tail headRun tailRun inductionHypothesis =>
      dsimp only [ConstitutiveExecutionHistory.feedbackStats,
        ConstitutiveFeedbackStats.addStage]
      rw [inductionHypothesis, headRun.nextRun.decisionAccumulationWorkExact]

theorem ConstitutiveExecutionHistory.provenanceVisits_eq_count
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : SequentialHistory depth assignment count}
    (run : ConstitutiveExecutionHistory state history) :
    run.feedbackStats.provenanceVisits = count := by
  induction run with
  | nil => rfl
  | step head tail headRun tailRun inductionHypothesis =>
      dsimp only [ConstitutiveExecutionHistory.feedbackStats,
        ConstitutiveFeedbackStats.addStage]
      rw [inductionHypothesis, headRun.nextRun.provenanceWorkExact,
        headRun.nextRun.provenanceRun.visitsExact]

theorem ConstitutiveExecutionHistory.inspections_bound
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {history : SequentialHistory depth assignment count}
    (run : ConstitutiveExecutionHistory state history) :
    run.feedbackStats.transmittedStateInspections ≤
      count * (state.decisions.length + count) := by
  induction run with
  | nil => exact Nat.zero_le _
  | @step depth count assignment state head tail headRun tailRun inductionHypothesis =>
      have nextLength : headRun.nextRun.next.decisions.length = state.decisions.length + 1 :=
        Eq.trans
          (congrArg List.length headRun.nextRun.decisionsFromExecution)
          (Eq.refl (state.decisions.length + 1))
      have inspectionExact : headRun.discoveryRun.inspection.visits = state.decisions.length :=
        Eq.trans
          (congrArg TransmittedDecisionInspection.visits
            headRun.discoveryRun.inspectionExact)
          (Eq.refl state.decisions.length)
      dsimp only [ConstitutiveExecutionHistory.feedbackStats,
        ConstitutiveFeedbackStats.addStage]
      rw [inspectionExact]
      calc
        _ ≤ count * (headRun.nextRun.next.decisions.length + count) +
              state.decisions.length := Nat.add_le_add_right inductionHypothesis _
        _ = count * (state.decisions.length + (count + 1)) +
              state.decisions.length := by
                exact congrArg (fun value => count * value + state.decisions.length)
                  (Eq.trans
                    (congrArg (fun value => value + count) nextLength)
                    (Eq.trans
                      (Nat.succ_add state.decisions.length count)
                      (Nat.add_succ state.decisions.length count).symm))
        _ ≤ count * (state.decisions.length + (count + 1)) +
              (state.decisions.length + (count + 1)) :=
            Nat.add_le_add_left (Nat.le_add_right _ _) _
        _ = (count + 1) * (state.decisions.length + (count + 1)) :=
              (Nat.succ_mul count (state.decisions.length + (count + 1))).symm

theorem executedFeedbackHistory_decisionAccumulations
    (depth count : Nat) (assignment : SequentialAssignment depth)
    (state : ThreadedConstitutiveState depth assignment) :
    (executeConstitutiveExecutionHistory depth count assignment state).feedbackStats.decisionAccumulations =
      count := by
  exact (executeConstitutiveExecutionHistory depth count assignment state).decisionAccumulations_eq_count

theorem executedFeedbackHistory_provenanceVisits
    (depth count : Nat) (assignment : SequentialAssignment depth)
    (state : ThreadedConstitutiveState depth assignment) :
    (executeConstitutiveExecutionHistory depth count assignment state).feedbackStats.provenanceVisits =
      count := by
  exact (executeConstitutiveExecutionHistory depth count assignment state).provenanceVisits_eq_count

theorem executedFeedbackHistory_inspections_bound
    (depth count : Nat) (assignment : SequentialAssignment depth)
    (state : ThreadedConstitutiveState depth assignment) :
    (executeConstitutiveExecutionHistory depth count assignment state).feedbackStats.transmittedStateInspections ≤
      count * (state.decisions.length + count) := by
  exact (executeConstitutiveExecutionHistory depth count assignment state).inspections_bound

/-- Four-role reading of one feedback stage. -/
structure ThreadedConstitutiveRoleStage {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) where
  npState : ThreadedConstitutiveState depth assignment
  npStateExact : npState = state
  orOpening : AcceptingExactBinarySplit
    (generatedStructuralBranchSystem
      (distinctGrowingDiscoveryFormula (constructStage (depth + 1)).searchIndex))
    (constructStage (depth + 1)).operationalRoot
    ((constructStage (depth + 1)).operationalRoot.child stage.discovery.var false stage.discovery.fresh)
    ((constructStage (depth + 1)).operationalRoot.child stage.discovery.var true stage.discovery.fresh)
  andDecision : StructuralBranchDecision
  andDecisionExact : andDecision = ⟨stageSelectedVar (depth + 1), true⟩
  pRelationComesFromTransmittedState :
    run.discoveryRun.outcome.discovered? = some stage.discovery
  pExecutionProducesContinuation :
    stage.application.output =
      (stage.execution.code.eval
        (generatedStructuralFlipAtAction
          (distinctGrowingDiscoveryFormula (constructStage (depth + 1)).searchIndex)
          stage.schedule.entry.var)).map stage.sourceContinuation
  nextNpState : ThreadedConstitutiveState (depth + 1) stage.next
  nextNpStateExact : nextNpState = run.nextRun.next

def threadedConstitutiveRoleStage {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    ThreadedConstitutiveRoleStage run :=
  { npState := state
    npStateExact := rfl
    orOpening := generatedStructuralSplit
      (constructStage (depth + 1)).operationalRoot stage.discovery.var stage.discovery.fresh
    andDecision := ⟨stageSelectedVar (depth + 1), true⟩
    andDecisionExact := rfl
    pRelationComesFromTransmittedState := run.relationFromTransmittedState
    pExecutionProducesContinuation := run.executedOutputFromThatCode
    nextNpState := run.nextRun.next
    nextNpStateExact := rfl }

theorem roleStage_output_constitutes_nextOperationalState {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : ThreadedConstitutiveStageRun state stage) :
    run.nextRun.next.threadedAssignment.assignment = stage.application.output.1 ∧
      run.nextRun.next.decisions =
        ⟨stageSelectedVar (depth + 1), true⟩ :: state.decisions ∧
      run.nextRun.next.provenance =
        stageSelectedVar (depth + 1) :: state.provenance := by
  refine ⟨?_, run.nextRun.decisionsFromExecution, run.nextRun.provenanceFromExecution⟩
  rw [run.nextRun.assignmentFromExecution]
  exact stage.nextAssignmentExact

/-- The four-role reading follows the same dependent tail as the operational
feedback history; no independent role history can be injected. -/
inductive ThreadedConstitutiveRoleHistory :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : SequentialHistory depth assignment count} →
      (run : ConstitutiveExecutionHistory state history) → Type 2 where
  | nil {depth : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment} :
      ThreadedConstitutiveRoleHistory (ConstitutiveExecutionHistory.nil state)
  | step {depth count : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {head : SequentialStageRun depth assignment}
      {tail : SequentialHistory (depth + 1) head.next count}
      {headRun : ThreadedConstitutiveStageRun state head}
      {tailRun : ConstitutiveExecutionHistory headRun.nextRun.next tail}
      (headRole : ThreadedConstitutiveRoleStage headRun)
      (tailRoles : ThreadedConstitutiveRoleHistory tailRun) :
      ThreadedConstitutiveRoleHistory
        (ConstitutiveExecutionHistory.step head tail headRun tailRun)

def buildThreadedConstitutiveRoleHistory :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      {history : SequentialHistory depth assignment count} →
      (run : ConstitutiveExecutionHistory state history) →
      ThreadedConstitutiveRoleHistory run
  | _, _, _, _, _, .nil _ => .nil
  | _, _, _, _, _, .step _ _ headRun tailRun =>
      .step (threadedConstitutiveRoleStage headRun)
        (buildThreadedConstitutiveRoleHistory tailRun)

/-- Two same-depth constitutions used by the decisive next-discovery probe. -/
inductive NextDiscoveryOrganization where
  | retained
  | predecided
  deriving DecidableEq

def nextDiscoveryDecisions (depth : Nat) : NextDiscoveryOrganization →
    List StructuralBranchDecision
  | .retained => []
  | .predecided => [⟨stageSelectedVar (depth + 1), false⟩]

structure NextDiscoveryConstitution (depth : Nat) where
  generation : CanonicalStageGeneration depth
  decisions : List StructuralBranchDecision

def nextDiscoveryConstitution (depth : Nat)
    (organization : NextDiscoveryOrganization) : NextDiscoveryConstitution depth :=
  ⟨generateCanonicalStage depth, nextDiscoveryDecisions depth organization⟩

def nextDiscoveryProjection {depth : Nat} (_ : NextDiscoveryConstitution depth) : Nat × Cnf :=
  (depth, (constructStage (depth + 1)).operationalRoot.context.formula)

def nextDiscoveryOutcome {depth : Nat} (state : NextDiscoveryConstitution depth) :=
  (runFeedbackDiscoveryFromData depth state.generation state.decisions).outcome.discovered?

theorem nextDiscovery_retained_found (depth : Nat) :
    nextDiscoveryOutcome (nextDiscoveryConstitution depth .retained) ≠ none := by
  change
    (exploreRecordedCandidates (constructStage (depth + 1)).operationalRoot
      (measuredGeneratedDiscovery (generateCanonicalStage depth)).recorded.extraction.candidates).discovered? ≠ none
  rw [(measuredGeneratedDiscovery (generateCanonicalStage depth)).recordedExact]
  exact stageRecordedDiscovery_ne_none (depth + 1)

theorem nextDiscovery_predecided_none (depth : Nat) :
    nextDiscoveryOutcome (nextDiscoveryConstitution depth .predecided) = none := by
  have unavailable :
      (inspectTransmittedDecisions (stageSelectedVar (depth + 1))
        [⟨stageSelectedVar (depth + 1), false⟩]).available = false := by
    unfold inspectTransmittedDecisions structuralDecisionsAvoidCheck
    change (if stageSelectedVar (depth + 1) = stageSelectedVar (depth + 1)
      then false else true) = false
    rw [if_pos rfl]
  unfold nextDiscoveryOutcome nextDiscoveryConstitution runFeedbackDiscoveryFromData
    nextDiscoveryDecisions
  dsimp only
  rw [unavailable]
  rfl

theorem nextDiscovery_constitutions_distinct (depth : Nat) :
    nextDiscoveryConstitution depth .retained ≠
      nextDiscoveryConstitution depth .predecided := by
  intro impossible
  have decisionsEqual := congrArg NextDiscoveryConstitution.decisions impossible
  cases decisionsEqual

theorem nextDiscovery_projection_equal (depth : Nat) :
    nextDiscoveryProjection (nextDiscoveryConstitution depth .retained) =
      nextDiscoveryProjection (nextDiscoveryConstitution depth .predecided) :=
  rfl

theorem nextDiscovery_outcome_different (depth : Nat) :
    nextDiscoveryOutcome (nextDiscoveryConstitution depth .retained) ≠
      nextDiscoveryOutcome (nextDiscoveryConstitution depth .predecided) := by
  rw [nextDiscovery_predecided_none]
  exact nextDiscovery_retained_found depth

theorem nextDiscovery_not_factors (depth : Nat) :
    ¬ ValueFactorsThrough (nextDiscoveryProjection (depth := depth))
        (nextDiscoveryOutcome (depth := depth)) := by
  apply value_not_factors_of_same_projection _ _
    (nextDiscoveryConstitution depth .retained)
    (nextDiscoveryConstitution depth .predecided)
  · exact nextDiscovery_projection_equal depth
  · exact nextDiscovery_outcome_different depth

/-- Failure exposes no code, next state or terminal placeholder. -/
structure FeedbackFailureArtifacts where
  codeAtoms : Nat
  nextProduced : Bool
  terminalProduced : Bool
  deriving DecidableEq, Repr

def feedbackFailureArtifacts (depth : Nat) : FeedbackFailureArtifacts :=
  match nextDiscoveryOutcome (nextDiscoveryConstitution depth .predecided) with
  | none => ⟨0, false, false⟩
  | some _ => ⟨1, true, true⟩

theorem feedbackFailureArtifacts_exact (depth : Nat) :
    feedbackFailureArtifacts depth = ⟨0, false, false⟩ := by
  unfold feedbackFailureArtifacts
  rw [nextDiscovery_predecided_none]

end ConstitutiveSearch.NPAndOrP

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NPAndOrP.inspectTransmittedDecisions
#print axioms ConstitutiveSearch.NPAndOrP.structuralDecisionsAvoidCheck_true_of_avoid
#print axioms ConstitutiveSearch.NPAndOrP.inspectTransmittedDecisions_available_of_all_lt
#print axioms ConstitutiveSearch.NPAndOrP.inspectTransmittedDecisions_visits_of_all_ne
#print axioms ConstitutiveSearch.NPAndOrP.initialThreadedConstitutiveState
#print axioms ConstitutiveSearch.NPAndOrP.structuralDecisionsAvoid_of_all_lt
#print axioms ConstitutiveSearch.NPAndOrP.ThreadedConstitutiveState.decisionsAvoidNext
#print axioms ConstitutiveSearch.NPAndOrP.runFeedbackDiscoveryFromData
#print axioms ConstitutiveSearch.NPAndOrP.runThreadedNextDiscovery
#print axioms ConstitutiveSearch.NPAndOrP.runThreadedNextDiscovery_exact
#print axioms ConstitutiveSearch.NPAndOrP.appendProvenanceMeasured
#print axioms ConstitutiveSearch.NPAndOrP.prependProvenanceMeasured
#print axioms ConstitutiveSearch.NPAndOrP.structuralDecisionsHold_transport
#print axioms ConstitutiveSearch.NPAndOrP.stageNext_preserves_threadedDecisions
#print axioms ConstitutiveSearch.NPAndOrP.realizeNextOperationalState
#print axioms ConstitutiveSearch.NPAndOrP.executeThreadedConstitutiveStage
#print axioms ConstitutiveSearch.NPAndOrP.executeConstitutiveExecutionHistory
#print axioms ConstitutiveSearch.NPAndOrP.threadConstitutiveExecutionHistory
#print axioms ConstitutiveSearch.NPAndOrP.ConstitutiveExecutionHistory.decisionAccumulations_eq_count
#print axioms ConstitutiveSearch.NPAndOrP.ConstitutiveExecutionHistory.provenanceVisits_eq_count
#print axioms ConstitutiveSearch.NPAndOrP.ConstitutiveExecutionHistory.inspections_bound
#print axioms ConstitutiveSearch.NPAndOrP.executedFeedbackHistory_provenanceVisits
#print axioms ConstitutiveSearch.NPAndOrP.executedFeedbackHistory_inspections_bound
#print axioms ConstitutiveSearch.NPAndOrP.roleStage_output_constitutes_nextOperationalState
#print axioms ConstitutiveSearch.NPAndOrP.buildThreadedConstitutiveRoleHistory
#print axioms ConstitutiveSearch.NPAndOrP.nextDiscovery_retained_found
#print axioms ConstitutiveSearch.NPAndOrP.nextDiscoveryConstitution
#print axioms ConstitutiveSearch.NPAndOrP.nextDiscovery_predecided_none
#print axioms ConstitutiveSearch.NPAndOrP.nextDiscovery_outcome_different
#print axioms ConstitutiveSearch.NPAndOrP.nextDiscovery_not_factors
#print axioms ConstitutiveSearch.NPAndOrP.feedbackFailureArtifacts_exact
/- AXIOM_AUDIT_END -/
