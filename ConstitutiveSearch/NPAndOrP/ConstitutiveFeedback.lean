import ConstitutiveSearch.NPAndOrP.ConstitutiveFullStep
import ConstitutiveSearch.NPAndOrP.GeneratedHistoryExecution

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

theorem inspectTransmittedDecisions_head_selected
    (selected : Var) (value : Bool) (rest : List StructuralBranchDecision) :
    (inspectTransmittedDecisions selected
      (⟨selected, value⟩ :: rest)).available = false := by
  dsimp only [inspectTransmittedDecisions]
  rw [structuralDecisionsAvoidCheck]
  rw [if_pos rfl]

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

theorem structuralDecisionsAvoid_of_check_true
    (selected : Var) (decisions : List StructuralBranchDecision)
    (checked : structuralDecisionsAvoidCheck selected decisions = true) :
    StructuralDecisionsAvoid selected decisions := by
  induction decisions with
  | nil => exact True.intro
  | cons decision rest inductionHypothesis =>
      rw [structuralDecisionsAvoidCheck] at checked
      split at checked
      · contradiction
      · constructor
        · assumption
        · exact inductionHypothesis checked

theorem structuralDecisionsAvoid_member_ne
    (selected : Var) (decisions : List StructuralBranchDecision)
    (avoid : StructuralDecisionsAvoid selected decisions)
    (decision : StructuralBranchDecision)
    (member : decision ∈ decisions) : decision.var ≠ selected := by
  induction decisions with
  | nil => cases member
  | cons head tail inductionHypothesis =>
      cases member with
      | head => exact avoid.1
      | tail _ prior => exact inductionHypothesis avoid.2 prior

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

/-- Freshness is a success invariant of the canonical family, not part of the
general validity of a transmitted state.  Separating it permits valid states
whose history has already determined the next variable. -/
def ThreadedStateFreshForNext {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) : Prop :=
  ∀ decision, decision ∈ state.decisions →
    decision.var < stageSelectedVar (depth + 1)

def initialThreadedConstitutiveState (depth : Nat) :
    ThreadedConstitutiveState depth (initialSequentialAssignment depth) :=
  { threadedAssignment := initialSequentialAssignment depth
    threadedAssignmentExact := rfl
    generation := generateCanonicalStage depth
    decisions := []
    provenance := []
    provenanceExact := rfl
    decisionsHold := True.intro }

theorem initialThreadedConstitutiveState_fresh (depth : Nat) :
    ThreadedStateFreshForNext (initialThreadedConstitutiveState depth) := by
  intro _ impossible
  cases impossible

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
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state) :
    StructuralDecisionsAvoid (stageSelectedVar (depth + 1)) state.decisions := by
  exact structuralDecisionsAvoid_of_all_lt _ _ fresh

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
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state) :
    (runThreadedNextDiscovery state).asRecorded =
      stageRecordedDiscoveryRun (depth + 1) := by
  have available := inspectTransmittedDecisions_available_of_all_lt
    (stageSelectedVar (depth + 1)) state.decisions
    fresh
  unfold ThreadedNextDiscoveryRun.asRecorded runThreadedNextDiscovery
    runFeedbackDiscoveryFromData
  dsimp only
  rw [available]
  rw [(measuredGeneratedDiscovery state.generation).recordedExact]
  rfl

theorem runThreadedNextDiscovery_found {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state) :
    (runThreadedNextDiscovery state).outcome.discovered? ≠ none := by
  have exactRun := runThreadedNextDiscovery_exact state fresh
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
    (stage : SequentialStageRun depth assignment)
    (avoid : StructuralDecisionsAvoid
      (stageSelectedVar (depth + 1)) state.decisions) :
    StructuralDecisionsHold stage.next.assignment state.decisions := by
  apply structuralDecisionsHold_transport
    assignment.assignment stage.next.assignment state.decisions state.decisionsHold
  intro decision member
  have different : decision.var ≠ stageSelectedVar (depth + 1) :=
    structuralDecisionsAvoid_member_ne _ _ avoid decision member
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
    (stage : SequentialStageRun depth assignment)
    (avoid : StructuralDecisionsAvoid
      (stageSelectedVar (depth + 1)) state.decisions) :
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
    stageNext_preserves_threadedDecisions state stage avoid
  let next : ThreadedConstitutiveState (depth + 1) stage.next :=
    { threadedAssignment := stage.next
      threadedAssignmentExact := rfl
      generation := nextGeneration
      decisions := ⟨selected, true⟩ :: state.decisions
      provenance := provenanceRun.output
      provenanceExact := by
        rw [provenanceRun.outputExact, state.provenanceExact]
        rfl
      decisionsHold := ⟨selectedTrue, oldHold⟩ }
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

/-- A successful discovery proves that the transmitted decisions avoid the
selected variable.  This fact is obtained from the executed inspection, not
from a freshness assumption supplied to the stage builder. -/
theorem ThreadedNextDiscoveryRun.decisionsAvoid_of_found {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ThreadedNextDiscoveryRun depth state)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (found : run.outcome.discovered? = some discovery) :
    StructuralDecisionsAvoid (stageSelectedVar (depth + 1)) state.decisions := by
  have available : run.inspection.available = true := by
    cases availableExact : run.inspection.available with
    | false =>
        have candidatesEmpty : run.candidates = [] := by
          rw [run.candidatesExact]
          rw [run.inspectionExact] at availableExact ⊢
          rw [if_neg]
          intro impossible
          exact Bool.noConfusion (Eq.trans availableExact.symm impossible)
        have outcomeEmpty : run.outcome.discovered? = none := by
          rw [run.outcomeExact, candidatesEmpty]
          rfl
        rw [outcomeEmpty] at found
        contradiction
    | true => rfl
  apply structuralDecisionsAvoid_of_check_true
  change
    (inspectTransmittedDecisions
      (stageSelectedVar (depth + 1)) state.decisions).available = true
  rw [← run.inspectionExact]
  exact available

theorem ThreadedNextDiscoveryRun.recordedExact_of_found {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ThreadedNextDiscoveryRun depth state)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (found : run.outcome.discovered? = some discovery) :
    run.asRecorded = stageRecordedDiscoveryRun (depth + 1) := by
  have avoid := run.decisionsAvoid_of_found discovery found
  have available := structuralDecisionsAvoidCheck_true_of_avoid
    (stageSelectedVar (depth + 1)) state.decisions avoid
  have availableInspection :
      (inspectTransmittedDecisions
        (stageSelectedVar (depth + 1)) state.decisions).available = true := by
    exact available
  unfold ThreadedNextDiscoveryRun.asRecorded
  have candidatesExact := run.candidatesExact
  rw [run.inspectionExact] at candidatesExact
  rw [if_pos availableInspection] at candidatesExact
  rw [run.outcomeExact, candidatesExact, run.generatedExact,
    (measuredGeneratedDiscovery state.generation).recordedExact]
  rfl

/-- One stage built only after the discovery stored here has returned `some`.
The builder receives no preconstructed `SequentialStageRun`. -/
structure ThreadedConstitutiveStageRun {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (stage : SequentialStageRun depth assignment) where
  discoveryRun : ThreadedNextDiscoveryRun depth state
  discoveryRunExact : discoveryRun = runThreadedNextDiscovery state
  discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot
  discoveryFound : discoveryRun.outcome.discovered? = some discovery
  recordedDiscoveryFound : discoveryRun.asRecorded.outcome.discovered? = some discovery
  stageFromDiscovery :
    stage = executeSequentialStageFromRecorded depth assignment state.generation
      discoveryRun.asRecorded
      (discoveryRun.recordedExact_of_found discovery discoveryFound)
      discovery recordedDiscoveryFound
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

structure ConstructedThreadedStageRun {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) where
  stage : SequentialStageRun depth assignment
  run : ThreadedConstitutiveStageRun state stage

def buildThreadedConstitutiveStage {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (discoveryRun : ThreadedNextDiscoveryRun depth state)
    (discoveryRunExact : discoveryRun = runThreadedNextDiscovery state)
    (discovery : EndogenousFlipDiscovery (constructStage (depth + 1)).operationalRoot)
    (found : discoveryRun.outcome.discovered? = some discovery) :
    ConstructedThreadedStageRun state := by
  have recordedFound :
      discoveryRun.asRecorded.outcome.discovered? = some discovery := found
  let stage := executeSequentialStageFromRecorded depth assignment state.generation
    discoveryRun.asRecorded
    (discoveryRun.recordedExact_of_found discovery found) discovery recordedFound
  let avoid := discoveryRun.decisionsAvoid_of_found discovery found
  exact
    { stage := stage
      run :=
        { discoveryRun := discoveryRun
          discoveryRunExact := discoveryRunExact
          discovery := discovery
          discoveryFound := found
          recordedDiscoveryFound := recordedFound
          stageFromDiscovery := rfl
          relationFromTransmittedState := by
            change discoveryRun.asRecorded.outcome.discovered? = some stage.discovery
            rw [discoveryRun.recordedExact_of_found discovery found]
            exact stage.discoveryExact
          returnedCodeFromThatRelation := executedDiscoverySchedule_code stage.execution
          executedOutputFromThatCode := stage.application.outputExact
          nextRun := realizeNextOperationalState state stage avoid } }

/-- Failure-aware active stage builder.  The `none` branch constructs no
stage, code, or next state. -/
def executeThreadedConstitutiveStage {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) :
    Option (ConstructedThreadedStageRun state) := by
  let discoveryRun := runThreadedNextDiscovery state
  exact match found : discoveryRun.outcome.discovered? with
  | none => none
  | some discovery =>
      some (buildThreadedConstitutiveStage state discoveryRun rfl discovery found)

theorem NextOperationalStateRun.fresh {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : NextOperationalStateRun state stage)
    (fresh : ThreadedStateFreshForNext state) :
    ThreadedStateFreshForNext run.next := by
  intro decision member
  rw [run.decisionsFromExecution] at member
  cases member with
  | head =>
      rw [stageSelectedVar_succ]
      exact Nat.lt_add_of_pos_right (by decide)
  | tail _ prior =>
      exact Nat.lt_trans (fresh decision prior)
        (by rw [stageSelectedVar_succ]; exact Nat.lt_add_of_pos_right (by decide))

theorem NextOperationalStateRun.generationCanonical {depth : Nat}
    {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    {stage : SequentialStageRun depth assignment}
    (run : NextOperationalStateRun state stage) :
    run.next.generation = generateCanonicalStage (depth + 1) := by
  rw [run.generationFromProducedTarget]
  exact generateCanonicalStageFromSource_exact _ _

/-- The active history is produced directly from the current state.  Its tail
is indexed by exactly the state produced by its head. -/
inductive ConstitutiveExecutionHistory :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      (state : ThreadedConstitutiveState depth assignment) → Type 2 where
  | nil {depth : Nat} {assignment : SequentialAssignment depth}
      (state : ThreadedConstitutiveState depth assignment) :
      ConstitutiveExecutionHistory (count := 0) state
  | step {depth count : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      (head : SequentialStageRun depth assignment)
      (headRun : ThreadedConstitutiveStageRun state head)
      (tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next) :
      ConstitutiveExecutionHistory (count := count + 1) state

def ConstitutiveExecutionHistory.toSequentialHistory :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      ConstitutiveExecutionHistory (count := count) state →
      SequentialHistory depth assignment count
  | _, _, _, _, .nil _ => .nil _ _
  | _, _, _, _, .step head headRun tailRun =>
      .step head tailRun.toSequentialHistory

def executeConstitutiveExecutionHistory
    (count : Nat) : {depth : Nat} → {assignment : SequentialAssignment depth} →
      (state : ThreadedConstitutiveState depth assignment) →
      ThreadedStateFreshForNext state →
      ConstitutiveExecutionHistory (count := count) state
  | _, _, state, fresh => match count with
    | 0 => .nil state
    | count + 1 =>
        let discoveryRun := runThreadedNextDiscovery state
        match found : discoveryRun.outcome.discovered? with
        | none => False.elim ((runThreadedNextDiscovery_found state fresh) found)
        | some discovery =>
            let built := buildThreadedConstitutiveStage state discoveryRun rfl discovery found
            .step built.stage built.run
              (executeConstitutiveExecutionHistory count built.run.nextRun.next
                (built.run.nextRun.fresh fresh))

theorem ConstitutiveExecutionHistory.toSequentialHistory_eq_reference
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state)
    (generationCanonical : state.generation = generateCanonicalStage depth) :
    run.toSequentialHistory = executeSequentialHistory depth count assignment := by
  induction run with
  | nil => rfl
  | @step depth count assignment state head headRun tailRun inductionHypothesis =>
      have headExact : head = executeSequentialStage depth assignment := by
        rw [headRun.stageFromDiscovery]
        rw [executeRecorded_eq_reference]
        rw [generationCanonical]
        rfl
      have tailExact := inductionHypothesis headRun.nextRun.generationCanonical
      cases headExact
      exact congrArg (SequentialHistory.step (executeSequentialStage depth assignment)) tailExact

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
      ConstitutiveExecutionHistory (count := count) state → ConstitutiveFeedbackStats
  | _, _, _, _, .nil _ => .zero
  | _, _, _, _, .step _ headRun tailRun =>
      tailRun.feedbackStats.addStage headRun

theorem ConstitutiveExecutionHistory.decisionAccumulations_eq_count
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state) :
    run.feedbackStats.decisionAccumulations = count := by
  induction run with
  | nil => rfl
  | step head headRun tailRun inductionHypothesis =>
      dsimp only [ConstitutiveExecutionHistory.feedbackStats,
        ConstitutiveFeedbackStats.addStage]
      rw [inductionHypothesis, headRun.nextRun.decisionAccumulationWorkExact]

theorem ConstitutiveExecutionHistory.provenanceVisits_eq_count
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state) :
    run.feedbackStats.provenanceVisits = count := by
  induction run with
  | nil => rfl
  | step head headRun tailRun inductionHypothesis =>
      dsimp only [ConstitutiveExecutionHistory.feedbackStats,
        ConstitutiveFeedbackStats.addStage]
      rw [inductionHypothesis, headRun.nextRun.provenanceWorkExact,
        headRun.nextRun.provenanceRun.visitsExact]

theorem ConstitutiveExecutionHistory.inspections_bound
    {depth count : Nat} {assignment : SequentialAssignment depth}
    {state : ThreadedConstitutiveState depth assignment}
    (run : ConstitutiveExecutionHistory (count := count) state) :
    run.feedbackStats.transmittedStateInspections ≤
      count * (state.decisions.length + count) := by
  induction run with
  | nil => exact Nat.zero_le _
  | @step depth count assignment state head headRun tailRun inductionHypothesis =>
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
    (count : Nat) {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state) :
    (executeConstitutiveExecutionHistory count state fresh).feedbackStats.decisionAccumulations =
      count := by
  exact (executeConstitutiveExecutionHistory count state fresh).decisionAccumulations_eq_count

theorem executedFeedbackHistory_provenanceVisits
    (count : Nat) {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state) :
    (executeConstitutiveExecutionHistory count state fresh).feedbackStats.provenanceVisits =
      count := by
  exact (executeConstitutiveExecutionHistory count state fresh).provenanceVisits_eq_count

theorem executedFeedbackHistory_inspections_bound
    (count : Nat) {depth : Nat} {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment)
    (fresh : ThreadedStateFreshForNext state) :
    (executeConstitutiveExecutionHistory count state fresh).feedbackStats.transmittedStateInspections ≤
      count * (state.decisions.length + count) := by
  exact (executeConstitutiveExecutionHistory count state fresh).inspections_bound

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
      (run : ConstitutiveExecutionHistory (count := count) state) → Type 2 where
  | nil {depth : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment} :
      ThreadedConstitutiveRoleHistory (ConstitutiveExecutionHistory.nil state)
  | step {depth count : Nat} {assignment : SequentialAssignment depth}
      {state : ThreadedConstitutiveState depth assignment}
      {head : SequentialStageRun depth assignment}
      {headRun : ThreadedConstitutiveStageRun state head}
      {tailRun : ConstitutiveExecutionHistory (count := count) headRun.nextRun.next}
      (headRole : ThreadedConstitutiveRoleStage headRun)
      (tailRoles : ThreadedConstitutiveRoleHistory tailRun) :
      ThreadedConstitutiveRoleHistory
        (ConstitutiveExecutionHistory.step head headRun tailRun)

def buildThreadedConstitutiveRoleHistory :
    {depth count : Nat} → {assignment : SequentialAssignment depth} →
      {state : ThreadedConstitutiveState depth assignment} →
      (run : ConstitutiveExecutionHistory (count := count) state) →
      ThreadedConstitutiveRoleHistory run
  | _, _, _, _, .nil _ => .nil
  | _, _, _, _, .step _ headRun tailRun =>
      .step (threadedConstitutiveRoleStage headRun)
        (buildThreadedConstitutiveRoleHistory tailRun)

/-- The common executed origin used by both sides of the separator.  Its stage
is built from the returned discovery by the same active builder as the public
recursion. -/
def nextDiscoveryCommonOrigin (depth : Nat) :
    ConstructedThreadedStageRun (initialThreadedConstitutiveState depth) := by
  let state := initialThreadedConstitutiveState depth
  let discoveryRun := runThreadedNextDiscovery state
  let discovery := canonicalStageDiscovery (depth + 1)
  have found : discoveryRun.outcome.discovered? = some discovery := by
    change discoveryRun.asRecorded.outcome.discovered? = some discovery
    rw [runThreadedNextDiscovery_exact state
      (initialThreadedConstitutiveState_fresh depth)]
    exact canonicalStageDiscovery_found (depth + 1)
  exact buildThreadedConstitutiveStage state discoveryRun rfl discovery found

/-- Extend a valid executed state with a determination already held by its
assignment.  This producer is independent of the separator instance. -/
def predecideNextVariable {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) :
    ThreadedConstitutiveState depth assignment :=
  { threadedAssignment := state.threadedAssignment
    threadedAssignmentExact := state.threadedAssignmentExact
    generation := state.generation
    decisions :=
      ⟨stageSelectedVar (depth + 1),
        assignment.assignment (stageSelectedVar (depth + 1))⟩ :: state.decisions
    provenance := stageSelectedVar (depth + 1) :: state.provenance
    provenanceExact := by rw [state.provenanceExact]; rfl
    decisionsHold := ⟨rfl, state.decisionsHold⟩ }

theorem predecideNextVariable_decisions {depth : Nat}
    {assignment : SequentialAssignment depth}
    (state : ThreadedConstitutiveState depth assignment) :
    (predecideNextVariable state).decisions =
      ⟨stageSelectedVar (depth + 1),
        assignment.assignment (stageSelectedVar (depth + 1))⟩ :: state.decisions :=
  rfl

/-- Existentially package the assignment index with a complete valid state. -/
structure PackedThreadedConstitutiveState (depth : Nat) where
  assignment : SequentialAssignment depth
  state : ThreadedConstitutiveState depth assignment

def retainedNextDiscoveryState (depth : Nat) :
    PackedThreadedConstitutiveState (depth + 1) :=
  let origin := nextDiscoveryCommonOrigin depth
  ⟨origin.stage.next, origin.run.nextRun.next⟩

theorem retainedNextDiscoveryState_fresh (depth : Nat) :
    ThreadedStateFreshForNext (retainedNextDiscoveryState depth).state :=
  (nextDiscoveryCommonOrigin depth).run.nextRun.fresh
    (initialThreadedConstitutiveState_fresh depth)

def predecidedNextDiscoveryState (depth : Nat) :
    PackedThreadedConstitutiveState (depth + 1) :=
  let retained := retainedNextDiscoveryState depth
  ⟨retained.assignment, predecideNextVariable retained.state⟩

/-- Two reachable organizations produced from one executed origin. -/
inductive NextDiscoveryOrganization where
  | retained
  | predecided
  deriving DecidableEq

structure NextDiscoveryConstitution (depth : Nat) where
  organization : NextDiscoveryOrganization
  packed : PackedThreadedConstitutiveState (depth + 1)
  stateExact : packed = match organization with
    | .retained => retainedNextDiscoveryState depth
    | .predecided => predecidedNextDiscoveryState depth

def nextDiscoveryConstitution (depth : Nat)
    (organization : NextDiscoveryOrganization) : NextDiscoveryConstitution depth :=
  match organization with
  | .retained => ⟨.retained, retainedNextDiscoveryState depth, rfl⟩
  | .predecided => ⟨.predecided, predecidedNextDiscoveryState depth, rfl⟩

def nextDiscoveryProjection {depth : Nat} (_ : NextDiscoveryConstitution depth) : Nat × Cnf :=
  (depth + 1, (constructStage ((depth + 1) + 1)).operationalRoot.context.formula)

def nextDiscoveryOutcome {depth : Nat} (state : NextDiscoveryConstitution depth) :=
  (runThreadedNextDiscovery state.packed.state).outcome.discovered?

theorem nextDiscovery_retained_found (depth : Nat) :
    nextDiscoveryOutcome (nextDiscoveryConstitution depth .retained) ≠ none := by
  exact runThreadedNextDiscovery_found (retainedNextDiscoveryState depth).state
    (retainedNextDiscoveryState_fresh depth)

theorem nextDiscovery_predecided_none (depth : Nat) :
    nextDiscoveryOutcome (nextDiscoveryConstitution depth .predecided) = none := by
  have unavailable :
      (inspectTransmittedDecisions (stageSelectedVar ((depth + 1) + 1))
        (predecidedNextDiscoveryState depth).state.decisions).available = false := by
    change
      (inspectTransmittedDecisions (stageSelectedVar ((depth + 1) + 1))
        (predecideNextVariable (retainedNextDiscoveryState depth).state).decisions).available = false
    rw [predecideNextVariable_decisions]
    exact inspectTransmittedDecisions_head_selected _ _ _
  unfold nextDiscoveryOutcome nextDiscoveryConstitution runThreadedNextDiscovery
    runFeedbackDiscoveryFromData
  dsimp only
  rw [unavailable]
  rfl

theorem predecided_discovery_constructs_no_stage (depth : Nat) :
    executeThreadedConstitutiveStage
      (predecidedNextDiscoveryState depth).state = none := by
  have failed :
      (runThreadedNextDiscovery
        (predecidedNextDiscoveryState depth).state).outcome.discovered? = none :=
    nextDiscovery_predecided_none depth
  unfold executeThreadedConstitutiveStage
  dsimp only
  split
  · rfl
  · rename_i discovery found
    have impossible : some discovery = none := Eq.trans found.symm failed
    cases impossible

theorem nextDiscovery_states_share_executed_origin (depth : Nat) :
    (nextDiscoveryConstitution depth .retained).packed.assignment =
        (nextDiscoveryCommonOrigin depth).stage.next ∧
      (nextDiscoveryConstitution depth .predecided).packed.assignment =
        (nextDiscoveryCommonOrigin depth).stage.next := by
  exact ⟨rfl, rfl⟩

theorem nextDiscovery_history_lengths_distinct (depth : Nat) :
    (nextDiscoveryConstitution depth .retained).packed.state.decisions.length ≠
      (nextDiscoveryConstitution depth .predecided).packed.state.decisions.length := by
  intro lengthsEqual
  have zeroEqOne : 0 = 1 := Nat.succ.inj lengthsEqual
  exact Nat.noConfusion zeroEqOne

theorem nextDiscovery_histories_distinct (depth : Nat) :
    (nextDiscoveryConstitution depth .retained).packed.state.decisions ≠
      (nextDiscoveryConstitution depth .predecided).packed.state.decisions := by
  intro decisionsEqual
  exact nextDiscovery_history_lengths_distinct depth
    (congrArg List.length decisionsEqual)

theorem nextDiscovery_constitutions_distinct (depth : Nat) :
    nextDiscoveryConstitution depth .retained ≠
      nextDiscoveryConstitution depth .predecided := by
  intro impossible
  have organizationsEqual := congrArg NextDiscoveryConstitution.organization impossible
  cases organizationsEqual

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
#print axioms ConstitutiveSearch.NPAndOrP.inspectTransmittedDecisions_head_selected
#print axioms ConstitutiveSearch.NPAndOrP.structuralDecisionsAvoidCheck_true_of_avoid
#print axioms ConstitutiveSearch.NPAndOrP.inspectTransmittedDecisions_available_of_all_lt
#print axioms ConstitutiveSearch.NPAndOrP.inspectTransmittedDecisions_visits_of_all_ne
#print axioms ConstitutiveSearch.NPAndOrP.initialThreadedConstitutiveState
#print axioms ConstitutiveSearch.NPAndOrP.initialThreadedConstitutiveState_fresh
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
#print axioms ConstitutiveSearch.NPAndOrP.NextOperationalStateRun.fresh
#print axioms ConstitutiveSearch.NPAndOrP.NextOperationalStateRun.generationCanonical
#print axioms ConstitutiveSearch.NPAndOrP.buildThreadedConstitutiveStage
#print axioms ConstitutiveSearch.NPAndOrP.executeThreadedConstitutiveStage
#print axioms ConstitutiveSearch.NPAndOrP.executeConstitutiveExecutionHistory
#print axioms ConstitutiveSearch.NPAndOrP.ConstitutiveExecutionHistory.toSequentialHistory
#print axioms ConstitutiveSearch.NPAndOrP.ConstitutiveExecutionHistory.toSequentialHistory_eq_reference
#print axioms ConstitutiveSearch.NPAndOrP.ConstitutiveExecutionHistory.decisionAccumulations_eq_count
#print axioms ConstitutiveSearch.NPAndOrP.ConstitutiveExecutionHistory.provenanceVisits_eq_count
#print axioms ConstitutiveSearch.NPAndOrP.ConstitutiveExecutionHistory.inspections_bound
#print axioms ConstitutiveSearch.NPAndOrP.executedFeedbackHistory_provenanceVisits
#print axioms ConstitutiveSearch.NPAndOrP.executedFeedbackHistory_inspections_bound
#print axioms ConstitutiveSearch.NPAndOrP.roleStage_output_constitutes_nextOperationalState
#print axioms ConstitutiveSearch.NPAndOrP.buildThreadedConstitutiveRoleHistory
#print axioms ConstitutiveSearch.NPAndOrP.nextDiscoveryCommonOrigin
#print axioms ConstitutiveSearch.NPAndOrP.predecideNextVariable
#print axioms ConstitutiveSearch.NPAndOrP.retainedNextDiscoveryState
#print axioms ConstitutiveSearch.NPAndOrP.predecidedNextDiscoveryState
#print axioms ConstitutiveSearch.NPAndOrP.nextDiscovery_retained_found
#print axioms ConstitutiveSearch.NPAndOrP.nextDiscoveryConstitution
#print axioms ConstitutiveSearch.NPAndOrP.nextDiscovery_predecided_none
#print axioms ConstitutiveSearch.NPAndOrP.predecided_discovery_constructs_no_stage
#print axioms ConstitutiveSearch.NPAndOrP.nextDiscovery_states_share_executed_origin
#print axioms ConstitutiveSearch.NPAndOrP.nextDiscovery_history_lengths_distinct
#print axioms ConstitutiveSearch.NPAndOrP.nextDiscovery_histories_distinct
#print axioms ConstitutiveSearch.NPAndOrP.nextDiscovery_outcome_different
#print axioms ConstitutiveSearch.NPAndOrP.nextDiscovery_not_factors
#print axioms ConstitutiveSearch.NPAndOrP.feedbackFailureArtifacts_exact
/- AXIOM_AUDIT_END -/
