import ConstitutiveSearch.SAT.TrajectoryConstitutedLocalSchedule
import ConstitutiveSearch.SAT.ParametricSymmetricFamily

/-!
# Second-audit causal decision benchmark

This module repairs the two causal gaps left by the earlier benchmark.

Discovery is endogenous: candidate variables are extracted from the current
residual formula, freshness is checked executably, candidates are explored in
order, and every attempted candidate is charged by the recursive search run.

The successful pipeline is indexed phase by phase:

`EndogenousFlipDiscovery -> DiscoverySchedule -> ValidatedDiscoverySchedule
  -> ExecutedDiscoverySchedule -> ExecutedTerminalArtifact -> Bool`.

The terminal constructor receives an execution object, not the original input.
Its scan can only inspect the state produced at the endpoint of that execution.
This is an API-level causal claim about this procedure; it is not a claim that
no other mathematical algorithm could decide the same extensional language.
-/

namespace ConstitutiveSearch
namespace SAT

namespace Literal

/-- Variable named by one literal. -/
def candidateVariable : Literal -> Var
  | .positive var => var
  | .negative var => var

end Literal

namespace Clause

/-- Candidate variables extracted by structural traversal of one clause. -/
def candidateVariables : Clause -> List Var
  | [] => []
  | literal :: rest =>
      literal.candidateVariable :: candidateVariables rest

end Clause

namespace Cnf

/-- Candidate variables extracted by structural traversal of a CNF. -/
def candidateVariables : Cnf -> List Var
  | [] => []
  | clause :: rest =>
      clause.candidateVariables ++ candidateVariables rest

end Cnf

/-- Candidate extraction reads the current generated state itself. -/
def extractStructuralCandidates
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    List Var :=
  state.context.formula.candidateVariables

/--
Successful endogenous discovery at one current state.  The selected variable,
freshness witness, sibling endpoints and structural relation are one dependent
piece of data.
-/
structure CandidateFlipDiscovery
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (candidate : Var) where
  fresh :
    StructuralDecisionsAvoid
      candidate
      state.context.decisions
  relation :
    GeneratedStructuralFlipAtRelation
      candidate
      (GeneratedStructuralBranchContext.child
        state candidate false fresh)
      (GeneratedStructuralBranchContext.child
        state candidate true fresh)

/-- Selected variable together with the evidence produced while trying it. -/
abbrev EndogenousFlipDiscovery
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :=
  Sigma (CandidateFlipDiscovery state)

namespace EndogenousFlipDiscovery

def var
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    (discovery : EndogenousFlipDiscovery state) : Var :=
  discovery.1

def fresh
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    (discovery : EndogenousFlipDiscovery state) :
    StructuralDecisionsAvoid
      discovery.var
      state.context.decisions :=
  discovery.2.fresh

def relation
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    (discovery : EndogenousFlipDiscovery state) :
    GeneratedStructuralFlipAtRelation
      discovery.var
      (GeneratedStructuralBranchContext.child
        state discovery.var false discovery.fresh)
      (GeneratedStructuralBranchContext.child
        state discovery.var true discovery.fresh) :=
  discovery.2.relation

end EndogenousFlipDiscovery

/-- Try one extracted variable, including executable freshness checking. -/
def tryEndogenousFlipCandidate
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (candidate : Var) :
    Option (CandidateFlipDiscovery state candidate) :=
  match freshness :
      structuralDecisionsAvoidCheck
        candidate
        state.context.decisions with
  | false => none
  | true =>
      let fresh :=
        structuralDecisionsAvoid_of_check_true
          candidate
          state.context.decisions
          freshness
      match
        (generatedStructuralFlipAtSearch
          rootFormula
          candidate).find
            (GeneratedStructuralBranchContext.child
              state candidate false fresh)
            (GeneratedStructuralBranchContext.child
              state candidate true fresh) with
      | none => none
      | some relation =>
          some
            { fresh := fresh
              relation := relation }

/-- A supplied positive relation certifies success of the executable attempt. -/
theorem tryEndogenousFlipCandidate_found_of_relation
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (candidate : Var)
    (freshness :
      structuralDecisionsAvoidCheck
          candidate
          state.context.decisions =
        true)
    (relation :
      let fresh :=
        structuralDecisionsAvoid_of_check_true
          candidate
          state.context.decisions
          freshness
      GeneratedStructuralFlipAtRelation
        candidate
        (GeneratedStructuralBranchContext.child
          state candidate false fresh)
        (GeneratedStructuralBranchContext.child
          state candidate true fresh)) :
    tryEndogenousFlipCandidate state candidate ≠ none := by
  unfold tryEndogenousFlipCandidate
  split
  · rename_i checkFalse
    rw [checkFalse] at freshness
    cases freshness
  · rename_i checkTrue
    have proofExact : checkTrue = freshness :=
      Subsingleton.elim _ _
    cases proofExact
    dsimp [generatedStructuralFlipAtSearch]
    rw [
      dif_pos relation.formulaExact,
      dif_pos relation.decisionsExact
    ]
    intro impossible
    cases impossible

/-- Outcome and actual number of attempted candidates. -/
structure EndogenousDiscoveryOutcome
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) where
  discovered? : Option (EndogenousFlipDiscovery state)
  attempts : Nat

/-- Structurally recursive exploration charging one unit per attempted head. -/
def exploreStructuralCandidates
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    List Var -> EndogenousDiscoveryOutcome state
  | [] =>
      { discovered? := none
        attempts := 0 }
  | candidate :: rest =>
      match tryEndogenousFlipCandidate state candidate with
      | some candidateDiscovery =>
          { discovered? :=
              some ⟨candidate, candidateDiscovery⟩
            attempts := 1 }
      | none =>
          let tail :=
            exploreStructuralCandidates state rest
          { discovered? := tail.discovered?
            attempts := tail.attempts + 1 }

/-- Full discovery run records both extracted candidates and exploration. -/
structure EndogenousDiscoveryRun
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) where
  candidates : List Var
  outcome : EndogenousDiscoveryOutcome state

/-- Current state -> extraction -> exploration. -/
def runEndogenousFlipDiscovery
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    EndogenousDiscoveryRun state :=
  let candidates :=
    extractStructuralCandidates state
  { candidates := candidates
    outcome :=
      exploreStructuralCandidates
        state
        candidates }

/-- A schedule indexed by, and containing no data beyond, its discovery. -/
inductive DiscoverySchedule
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    (discovery : EndogenousFlipDiscovery state) : Type where
  | fromDiscovery : DiscoverySchedule discovery

/-- Canonical schedule production from discovered data only. -/
def scheduleFromDiscovery
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    (discovery : EndogenousFlipDiscovery state) :
    DiscoverySchedule discovery :=
  .fromDiscovery

namespace DiscoverySchedule

/-- The unique local schedule entry is reconstructed from the discovery index. -/
def entry
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    (_schedule : DiscoverySchedule discovery) :
    ConstitutedLocalWitness rootFormula :=
  { var := discovery.1
    source :=
      GeneratedStructuralBranchContext.child
        state
        discovery.1
        false
        discovery.2.fresh
    target :=
      GeneratedStructuralBranchContext.child
        state
        discovery.1
        true
        discovery.2.fresh
    relation := discovery.2.relation }

end DiscoverySchedule

/-- Execute the validator for the unique discovered schedule atom. -/
def runDiscoveryScheduleValidation
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    (schedule : DiscoverySchedule discovery) :
    SearchableCodeValidationRun :=
  match
    (generatedStructuralFlipAtSearch
      rootFormula
      schedule.entry.var).find
        schedule.entry.source
        schedule.entry.target with
  | some _ =>
      { success := true
        primitiveQueries := 1 }
  | none =>
      { success := false
        primitiveQueries := 1 }

/-- Validation cost is read from the validator run and is exactly one query. -/
theorem runDiscoveryScheduleValidation_queries
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    (schedule : DiscoverySchedule discovery) :
    (runDiscoveryScheduleValidation schedule).primitiveQueries = 1 := by
  unfold runDiscoveryScheduleValidation
  split <;> rfl

/-- Validation data is indexed by the exact schedule it validates. -/
structure ValidatedDiscoverySchedule
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    (schedule : DiscoverySchedule discovery) where
  run : SearchableCodeValidationRun
  runExact :
    run = runDiscoveryScheduleValidation schedule
  success : run.success = true

/-- Execute validation and retain the exact run that established success. -/
def validateDiscoverySchedule
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    (schedule : DiscoverySchedule discovery) :
    ValidatedDiscoverySchedule schedule :=
  { run :=
      runDiscoveryScheduleValidation schedule
    runExact := rfl
    success := by
      cases schedule
      change
        (runDiscoveryScheduleValidation
          (scheduleFromDiscovery discovery)).success = true
      unfold runDiscoveryScheduleValidation
      dsimp [
        scheduleFromDiscovery,
        DiscoverySchedule.entry
      ]
      dsimp [generatedStructuralFlipAtSearch]
      rw [
        dif_pos discovery.2.relation.formulaExact,
        dif_pos discovery.2.relation.decisionsExact
      ] }

/--
Local execution is indexed by the validated schedule.  A value of this type
contains the actual closure-search run and positive evidence that it found a
code for the schedule endpoints.  It also stores that returned code and the
state produced at its indexed target as data for the next phase.
-/
structure ExecutedDiscoverySchedule
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    (validated : ValidatedDiscoverySchedule schedule) where
  run :
    ClosureSearchRun
      (GeneratedStructuralFlipAtRelation
        (rootFormula := rootFormula)
        schedule.entry.var)
      schedule.entry.source
      schedule.entry.target
  runExact : run = schedule.entry.executionRun
  code :
    TransportClosure
      (GeneratedStructuralFlipAtRelation
        (rootFormula := rootFormula)
        schedule.entry.var)
      schedule.entry.source
      schedule.entry.target
  codeExact : run.code? = some code
  producedState : GeneratedStructuralBranchContext rootFormula
  producedStateExact : producedState = schedule.entry.target

/-- Execute the validated local schedule. -/
def executeValidatedDiscoverySchedule
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    (validated : ValidatedDiscoverySchedule schedule) :
    ExecutedDiscoverySchedule validated :=
  let run := schedule.entry.executionRun
  match exactCode : run.code? with
  | none =>
      False.elim
        (schedule.entry.executionRun_found exactCode)
  | some code =>
      { run := run
        runExact := rfl
        code := code
        codeExact := exactCode
        producedState := schedule.entry.target
        producedStateExact := rfl }

/-- The actual one-atom execution run reports one query and no composition. -/
theorem executeValidatedDiscoverySchedule_stats
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    (validated : ValidatedDiscoverySchedule schedule) :
    (executeValidatedDiscoverySchedule
        validated).run.stats.primitiveQueries = 1 /\
      (executeValidatedDiscoverySchedule
        validated).run.stats.compositionCandidates = 0 := by
  have runExact :=
    (executeValidatedDiscoverySchedule validated).runExact
  rw [runExact]
  cases schedule
  change
    (searchTransportClosureBounded
        (generatedStructuralFlipAtSearch
          rootFormula
          discovery.1)
        []
        1
        (GeneratedStructuralBranchContext.child
          state discovery.1 false discovery.2.fresh)
        (GeneratedStructuralBranchContext.child
          state discovery.1 true discovery.2.fresh)).stats.primitiveQueries = 1 /\
      (searchTransportClosureBounded
        (generatedStructuralFlipAtSearch
          rootFormula
          discovery.1)
        []
        1
        (GeneratedStructuralBranchContext.child
          state discovery.1 false discovery.2.fresh)
        (GeneratedStructuralBranchContext.child
          state discovery.1 true discovery.2.fresh)).stats.compositionCandidates = 0
  unfold searchTransportClosureBounded
  dsimp [generatedStructuralFlipAtSearch]
  rw [
    dif_pos discovery.2.relation.formulaExact,
    dif_pos discovery.2.relation.decisionsExact
  ]
  exact ⟨rfl, rfl⟩

/-- The execution-produced state is exactly the target indexed by its returned code. -/
theorem ExecutedDiscoverySchedule.producedState_eq_target
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    {validated : ValidatedDiscoverySchedule schedule}
    (execution : ExecutedDiscoverySchedule validated) :
    execution.producedState = schedule.entry.target :=
  execution.producedStateExact

/-- Statistics produced by an executable scan of an executed terminal CNF. -/
structure ExecutedTerminalScan where
  containsEmpty : Bool
  clauseChecks : Nat

/-- Terminal scan with cost generated by its structural recursion. -/
def scanExecutedTerminal : Cnf -> ExecutedTerminalScan
  | [] =>
      { containsEmpty := false
        clauseChecks := 0 }
  | clause :: rest =>
      if clause = [] then
        { containsEmpty := true
          clauseChecks := 1 }
      else
        let tail := scanExecutedTerminal rest
        { containsEmpty := tail.containsEmpty
          clauseChecks := tail.clauseChecks + 1 }

/--
Terminal artifact indexed by the execution that produced its state.  There is
no input or independently supplied state in this interface.
-/
structure ExecutedTerminalArtifact
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    {validated : ValidatedDiscoverySchedule schedule}
    (execution : ExecutedDiscoverySchedule validated) where
  scan : ExecutedTerminalScan
  scanExact :
    scan =
      scanExecutedTerminal
        execution.producedState.context.formula

/-- Construct the terminal only from the completed execution. -/
def terminalFromExecution
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    {validated : ValidatedDiscoverySchedule schedule}
    (execution : ExecutedDiscoverySchedule validated) :
    ExecutedTerminalArtifact execution :=
  { scan :=
      scanExecutedTerminal
        execution.producedState.context.formula
    scanExact := rfl }

/-- Positive provenance equation carried by every terminal artifact. -/
theorem ExecutedTerminalArtifact.scan_from_execution
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
  terminal.scanExact

/-- The decision reads only the executed terminal artifact. -/
def decideExecutedTerminal
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    {discovery : EndogenousFlipDiscovery state}
    {schedule : DiscoverySchedule discovery}
    {validated : ValidatedDiscoverySchedule schedule}
    {execution : ExecutedDiscoverySchedule validated}
    (terminal : ExecutedTerminalArtifact execution) : Bool :=
  !terminal.scan.containsEmpty

/-! ## Concrete nonconstant family using the generic causal pipeline -/

/-- The useful split variable changes with the input. -/
def causalDecisionSplitVar (input : Nat) : Var :=
  input + 2

/-- A distinct anchor derived from the useful split variable. -/
def causalDecisionAnchorVar (input : Nat) : Var :=
  causalDecisionSplitVar input + 1

/-- YES at zero and an empty-clause obstruction at every nonzero input. -/
def causalDecisionBackground (input : Nat) : Cnf :=
  if input = 0 then [] else [[]]

/-- Presented formula; the procedure is not separately given its split variable. -/
def causalDecisionFormula (input : Nat) : Cnf :=
  symmetricBlockFamily
    (causalDecisionSplitVar input)
    (causalDecisionAnchorVar input)
    (causalDecisionBackground input)

/-- Current root state from which candidate extraction begins. -/
def causalDecisionRoot
    (input : Nat) :
    GeneratedStructuralBranchContext
      (causalDecisionFormula input) :=
  GeneratedStructuralBranchContext.root
    (causalDecisionFormula input)

/-- Every variable is fresh at a generated root. -/
theorem causalDecisionRootFresh
    (input : Nat)
    (var : Var) :
    StructuralDecisionsAvoid
      var
      (causalDecisionRoot input).context.decisions :=
  True.intro

/-- Freshness witness produced by the executable root check. -/
def causalDecisionCheckedFresh
    (input : Nat) :
    StructuralDecisionsAvoid
      (causalDecisionSplitVar input)
      (causalDecisionRoot input).context.decisions :=
  structuralDecisionsAvoid_of_check_true
    (causalDecisionSplitVar input)
    (causalDecisionRoot input).context.decisions
    rfl

/-- The derived anchor is distinct from the derived split variable. -/
theorem causalDecisionAnchor_ne_split
    (input : Nat) :
    causalDecisionAnchorVar input ≠
      causalDecisionSplitVar input := by
  unfold causalDecisionAnchorVar
  exact Nat.ne_of_gt (Nat.lt_succ_self _)

/-- The benchmark background contains no literal at all. -/
theorem causalDecisionBackground_avoids
    (input : Nat) :
    Cnf.AvoidsVar
      (causalDecisionSplitVar input)
      (causalDecisionBackground input) := by
  unfold causalDecisionBackground
  by_cases inputZero : input = 0
  · rw [if_pos inputZero]
    exact True.intro
  · rw [if_neg inputZero]
    exact ⟨True.intro, True.intro⟩

/-- The useful sibling relation exists for the candidate encoded in the formula. -/
theorem causalDecision_flipSymmetric
    (input : Nat) :
    FlipSymmetricAt
      (causalDecisionFormula input)
      (causalDecisionSplitVar input) := by
  unfold causalDecisionFormula
  apply symmetricBlockFamily_flipSymmetric
  · exact causalDecisionAnchor_ne_split input
  · exact causalDecisionBackground_avoids input

/-- Exact witness used only to prove completeness of executable discovery. -/
def causalDecisionExpectedRelation
    (input : Nat) :
    GeneratedStructuralFlipAtRelation
      (causalDecisionSplitVar input)
      (GeneratedStructuralBranchContext.child
        (causalDecisionRoot input)
        (causalDecisionSplitVar input)
        false
        (causalDecisionCheckedFresh input))
      (GeneratedStructuralBranchContext.child
        (causalDecisionRoot input)
        (causalDecisionSplitVar input)
        true
        (causalDecisionCheckedFresh input)) :=
  flipSymmetricSiblingRelation
    (causalDecisionRoot input)
    (causalDecisionSplitVar input)
    (causalDecisionCheckedFresh input)
    (causalDecision_flipSymmetric input)

/-- The first candidate is extracted from syntax rather than passed separately. -/
theorem causalDecision_firstCandidate
    (input : Nat) :
    exists rest,
      extractStructuralCandidates
          (causalDecisionRoot input) =
        causalDecisionSplitVar input :: rest := by
  refine
    ⟨[causalDecisionAnchorVar input,
        causalDecisionSplitVar input,
        causalDecisionAnchorVar input] ++
        (causalDecisionBackground input).candidateVariables,
      ?_⟩
  rfl

/-- The syntactically extracted useful candidate succeeds when tried. -/
theorem causalDecision_candidate_found
    (input : Nat) :
    tryEndogenousFlipCandidate
        (causalDecisionRoot input)
        (causalDecisionSplitVar input) ≠
      none := by
  exact
    tryEndogenousFlipCandidate_found_of_relation
      (causalDecisionRoot input)
      (causalDecisionSplitVar input)
      rfl
      (causalDecisionExpectedRelation input)

/-- Endogenous discovery succeeds after exactly one actually attempted candidate. -/
theorem causalDecision_discovery_found
    (input : Nat) :
    exists discovery,
      (runEndogenousFlipDiscovery
        (causalDecisionRoot input)).outcome.discovered? =
          some discovery /\
      discovery.var = causalDecisionSplitVar input /\
      (runEndogenousFlipDiscovery
        (causalDecisionRoot input)).outcome.attempts = 1 := by
  rcases causalDecision_firstCandidate input with
    ⟨rest, candidatesExact⟩
  cases found :
      tryEndogenousFlipCandidate
        (causalDecisionRoot input)
        (causalDecisionSplitVar input) with
  | none =>
      exact False.elim ((causalDecision_candidate_found input) found)
  | some candidateDiscovery =>
      let discovery : EndogenousFlipDiscovery (causalDecisionRoot input) :=
        ⟨causalDecisionSplitVar input, candidateDiscovery⟩
      refine ⟨discovery, ?_, rfl, ?_⟩
      · change
          (exploreStructuralCandidates
            (causalDecisionRoot input)
            (extractStructuralCandidates
              (causalDecisionRoot input))).discovered? =
            some discovery
        rw [candidatesExact]
        unfold exploreStructuralCandidates
        rw [found]
      · change
          (exploreStructuralCandidates
            (causalDecisionRoot input)
            (extractStructuralCandidates
              (causalDecisionRoot input))).attempts = 1
        rw [candidatesExact]
        unfold exploreStructuralCandidates
        rw [found]

/-- Any witness returned by the benchmark run carries the extracted split variable. -/
theorem causalDecision_discovered_var
    (input : Nat)
    (discovery : EndogenousFlipDiscovery (causalDecisionRoot input))
    (found :
      (runEndogenousFlipDiscovery
        (causalDecisionRoot input)).outcome.discovered? =
          some discovery) :
    discovery.var = causalDecisionSplitVar input := by
  rcases causalDecision_discovery_found input with
    ⟨expected, expectedFound, expectedVar, _attempts⟩
  rw [found] at expectedFound
  have same : discovery = expected :=
    Option.some.inj expectedFound
  rw [same]
  exact expectedVar

/-- Exact retained residual for a true child at the derived split variable. -/
theorem causalDecision_trueChild_formula
    (input : Nat)
    (fresh :
      StructuralDecisionsAvoid
        (causalDecisionSplitVar input)
        (causalDecisionRoot input).context.decisions) :
    (GeneratedStructuralBranchContext.child
      (causalDecisionRoot input)
      (causalDecisionSplitVar input)
      true
      fresh).context.formula =
        symmetricNegativeClause
            (causalDecisionSplitVar input)
            (causalDecisionAnchorVar input) ::
          causalDecisionBackground input := by
  change
    branchResidual
        (causalDecisionFormula input)
        (causalDecisionSplitVar input)
        true =
      symmetricNegativeClause
          (causalDecisionSplitVar input)
          (causalDecisionAnchorVar input) ::
        causalDecisionBackground input
  unfold causalDecisionFormula
  unfold symmetricBlockFamily
  have positiveHit :
      Clause.containsLiteral
          (Literal.forValue
            (causalDecisionSplitVar input)
            true)
          (symmetricPositiveClause
            (causalDecisionSplitVar input)
            (causalDecisionAnchorVar input)) =
        true := by
    unfold symmetricPositiveClause
    dsimp [Literal.forValue]
    rw [Clause.containsLiteral, if_pos rfl]
  have negativeMiss :
      Clause.containsLiteral
          (Literal.forValue
            (causalDecisionSplitVar input)
            true)
          (symmetricNegativeClause
            (causalDecisionSplitVar input)
            (causalDecisionAnchorVar input)) =
        false := by
    unfold symmetricNegativeClause
    dsimp [Literal.forValue]
    have firstDifferent :
        Literal.negative (causalDecisionSplitVar input) ≠
          Literal.positive (causalDecisionSplitVar input) := by
      intro impossible
      cases impossible
    have secondDifferent :
        Literal.positive (causalDecisionAnchorVar input) ≠
          Literal.positive (causalDecisionSplitVar input) := by
      intro impossible
      have sameVar :
          causalDecisionAnchorVar input =
            causalDecisionSplitVar input :=
        Literal.positive.inj impossible
      exact (causalDecisionAnchor_ne_split input) sameVar
    rw [Clause.containsLiteral, if_neg firstDifferent]
    rw [Clause.containsLiteral, if_neg secondDifferent]
    rfl
  rw [
    branchResidual_cons_hit
      (symmetricPositiveClause
        (causalDecisionSplitVar input)
        (causalDecisionAnchorVar input))
      (symmetricNegativeClause
          (causalDecisionSplitVar input)
          (causalDecisionAnchorVar input) ::
        causalDecisionBackground input)
      (causalDecisionSplitVar input)
      true
      positiveHit
  ]
  rw [
    branchResidual_cons_miss
      (symmetricNegativeClause
        (causalDecisionSplitVar input)
        (causalDecisionAnchorVar input))
      (causalDecisionBackground input)
      (causalDecisionSplitVar input)
      true
      negativeMiss
  ]
  rw [
    Cnf.branchResidual_eq_self
      (causalDecisionBackground_avoids input)
      true
  ]

/-- Full typed tail of the procedure after successful endogenous discovery. -/
def causalTerminalAfterDiscovery
    (input : Nat)
    (discovery : EndogenousFlipDiscovery (causalDecisionRoot input)) :=
  terminalFromExecution
    (executeValidatedDiscoverySchedule
      (validateDiscoverySchedule
        (scheduleFromDiscovery discovery)))

/-- The post-discovery decision is a function of the executed terminal only. -/
def causalDecisionAfterDiscovery
    (input : Nat)
    (discovery : EndogenousFlipDiscovery (causalDecisionRoot input)) : Bool :=
  decideExecutedTerminal
    (causalTerminalAfterDiscovery input discovery)

/-- The successful terminal is exactly the state indexed by the discovered execution. -/
theorem causalDecisionAfterDiscovery_terminal_formula
    (input : Nat)
    (discovery : EndogenousFlipDiscovery (causalDecisionRoot input))
    (selected :
      discovery.var = causalDecisionSplitVar input) :
    (causalTerminalAfterDiscovery
      input
      discovery).scan =
      scanExecutedTerminal
        (symmetricNegativeClause
            (causalDecisionSplitVar input)
            (causalDecisionAnchorVar input) ::
          causalDecisionBackground input) := by
  cases discovery with
  | mk candidate evidence =>
      change candidate = causalDecisionSplitVar input at selected
      subst candidate
      unfold causalTerminalAfterDiscovery
      rw [ExecutedTerminalArtifact.scan_from_execution]
      rw [ExecutedDiscoverySchedule.producedState_eq_target]
      change
        scanExecutedTerminal
            ((GeneratedStructuralBranchContext.child
              (causalDecisionRoot input)
              (causalDecisionSplitVar input)
              true
              evidence.fresh).context.formula) =
          scanExecutedTerminal
            (symmetricNegativeClause
                (causalDecisionSplitVar input)
                (causalDecisionAnchorVar input) ::
              causalDecisionBackground input)
      rw [causalDecision_trueChild_formula input evidence.fresh]

/-- Extensional SAT acceptance of the presented benchmark formula. -/
def CausalDecisionAccept (input : Nat) : Prop :=
  exists assignment : Assignment,
    Satisfies assignment (causalDecisionFormula input)

/-- Concrete satisfying assignment for the YES instance. -/
def causalDecisionYesAssignment : Assignment
  | _ => true

/-- Zero is a genuine YES instance. -/
theorem causalDecision_zero_accepts :
    CausalDecisionAccept 0 := by
  exact
    ⟨causalDecisionYesAssignment,
      .cons rfl (.cons rfl .nil)⟩

/-- Every nonzero instance contains the explicit empty-clause obstruction. -/
theorem causalDecision_nonzero_rejects
    {input : Nat}
    (inputNonzero : input ≠ 0) :
    ¬ CausalDecisionAccept input := by
  intro accepted
  rcases accepted with ⟨assignment, satisfaction⟩
  unfold causalDecisionFormula at satisfaction
  unfold causalDecisionBackground at satisfaction
  rw [if_neg inputNonzero] at satisfaction
  cases satisfaction with
  | cons firstSatisfied restSatisfied =>
      cases restSatisfied with
      | cons secondSatisfied finalSatisfied =>
          cases finalSatisfied with
          | cons emptySatisfied tailSatisfied =>
              change false = true at emptySatisfied
              cases emptySatisfied

/-- The extensional language has both a YES and a NO instance. -/
theorem causalDecision_accept_iff_zero
    (input : Nat) :
    CausalDecisionAccept input <-> input = 0 := by
  constructor
  · intro accepted
    by_cases inputZero : input = 0
    · exact inputZero
    · exact False.elim ((causalDecision_nonzero_rejects inputZero) accepted)
  · intro inputZero
    subst input
    exact causalDecision_zero_accepts

/-- The terminal-only readout is correct once discovery has selected its result. -/
theorem causalDecisionAfterDiscovery_correct
    (input : Nat)
    (discovery : EndogenousFlipDiscovery (causalDecisionRoot input))
    (selected :
      discovery.var = causalDecisionSplitVar input) :
    causalDecisionAfterDiscovery input discovery = true <->
      CausalDecisionAccept input := by
  unfold causalDecisionAfterDiscovery
  unfold decideExecutedTerminal
  rw [
    causalDecisionAfterDiscovery_terminal_formula
      input
      discovery
      selected
  ]
  by_cases inputZero : input = 0
  · subst input
    change true = true <-> CausalDecisionAccept 0
    exact
      ⟨fun _accepted => causalDecision_zero_accepts,
        fun _witness => rfl⟩
  · unfold causalDecisionBackground
    rw [if_neg inputZero]
    change false = true <-> CausalDecisionAccept input
    exact
      ⟨fun impossible => Bool.noConfusion impossible,
        fun accepted =>
          False.elim
            ((causalDecision_nonzero_rejects inputZero)
              accepted)⟩

/-- Separate costs, each read from the run that produced that phase. -/
structure CausalDecisionProcedureStats where
  extractedCandidates : Nat
  discoveryAttempts : Nat
  scheduleAtoms : Nat
  validationQueries : Nat
  executionPrimitiveQueries : Nat
  executionCompositionCandidates : Nat
  terminalChecks : Nat

namespace CausalDecisionProcedureStats

def total (stats : CausalDecisionProcedureStats) : Nat :=
  stats.extractedCandidates +
    stats.discoveryAttempts +
    stats.scheduleAtoms +
    stats.validationQueries +
    stats.executionPrimitiveQueries +
    stats.executionCompositionCandidates +
    stats.terminalChecks

end CausalDecisionProcedureStats

/-- Observable result and phase-local costs of the complete procedure. -/
structure CausalDecisionProcedureRun where
  result : Bool
  terminalProduced : Bool
  stats : CausalDecisionProcedureStats

/--
Complete executable pipeline.  In the success branch every local name consumes
the previous phase's typed output; terminal construction receives no input.
-/
def executeCausalDecision
    (input : Nat) : CausalDecisionProcedureRun :=
  let discoveryRun :=
    runEndogenousFlipDiscovery (causalDecisionRoot input)
  match discoveryRun.outcome.discovered? with
  | none =>
      { result := false
        terminalProduced := false
        stats :=
          { extractedCandidates := discoveryRun.candidates.length
            discoveryAttempts := discoveryRun.outcome.attempts
            scheduleAtoms := 0
            validationQueries := 0
            executionPrimitiveQueries := 0
            executionCompositionCandidates := 0
            terminalChecks := 0 } }
  | some discovery =>
      let schedule := scheduleFromDiscovery discovery
      let validated := validateDiscoverySchedule schedule
      let execution := executeValidatedDiscoverySchedule validated
      let terminal := terminalFromExecution execution
      { result := decideExecutedTerminal terminal
        terminalProduced := true
        stats :=
          { extractedCandidates := discoveryRun.candidates.length
            discoveryAttempts := discoveryRun.outcome.attempts
            scheduleAtoms := schedule.entry.code.size
            validationQueries := validated.run.primitiveQueries
            executionPrimitiveQueries :=
              execution.run.stats.primitiveQueries
            executionCompositionCandidates :=
              execution.run.stats.compositionCandidates
            terminalChecks := terminal.scan.clauseChecks } }

/-- The complete run always reaches the typed success branch. -/
theorem executeCausalDecision_success_branch
    (input : Nat) :
    exists discovery,
      (runEndogenousFlipDiscovery
        (causalDecisionRoot input)).outcome.discovered? =
          some discovery := by
  rcases causalDecision_discovery_found input with
    ⟨discovery, found, _selected, _attempts⟩
  exact ⟨discovery, found⟩

/-- The complete decision is caused by, and agrees with, its terminal readout. -/
theorem executeCausalDecision_correct
    (input : Nat) :
    (executeCausalDecision input).result = true <->
      CausalDecisionAccept input := by
  rcases executeCausalDecision_success_branch input with
    ⟨discovery, found⟩
  have selected :=
    causalDecision_discovered_var input discovery found
  unfold executeCausalDecision
  dsimp only
  rw [found]
  exact
    causalDecisionAfterDiscovery_correct
      input
      discovery
      selected

/-- A successful complete run certifies that an execution-indexed terminal exists. -/
theorem executeCausalDecision_terminalProduced
    (input : Nat) :
    (executeCausalDecision input).terminalProduced = true := by
  rcases executeCausalDecision_success_branch input with
    ⟨discovery, found⟩
  unfold executeCausalDecision
  dsimp only
  rw [found]

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.extractStructuralCandidates
#print axioms ConstitutiveSearch.SAT.tryEndogenousFlipCandidate
#print axioms ConstitutiveSearch.SAT.exploreStructuralCandidates
#print axioms ConstitutiveSearch.SAT.runEndogenousFlipDiscovery
#print axioms ConstitutiveSearch.SAT.DiscoverySchedule
#print axioms ConstitutiveSearch.SAT.runDiscoveryScheduleValidation_queries
#print axioms ConstitutiveSearch.SAT.validateDiscoverySchedule
#print axioms ConstitutiveSearch.SAT.executeValidatedDiscoverySchedule
#print axioms ConstitutiveSearch.SAT.executeValidatedDiscoverySchedule_stats
#print axioms ConstitutiveSearch.SAT.ExecutedDiscoverySchedule.producedState
#print axioms ConstitutiveSearch.SAT.ExecutedDiscoverySchedule.producedState_eq_target
#print axioms ConstitutiveSearch.SAT.terminalFromExecution
#print axioms ConstitutiveSearch.SAT.ExecutedTerminalArtifact.scan_from_execution
#print axioms ConstitutiveSearch.SAT.decideExecutedTerminal
#print axioms ConstitutiveSearch.SAT.causalDecision_discovery_found
#print axioms ConstitutiveSearch.SAT.causalDecisionAfterDiscovery_terminal_formula
#print axioms ConstitutiveSearch.SAT.causalDecision_accept_iff_zero
#print axioms ConstitutiveSearch.SAT.causalDecisionAfterDiscovery_correct
#print axioms ConstitutiveSearch.SAT.executeCausalDecision
#print axioms ConstitutiveSearch.SAT.executeCausalDecision_correct
#print axioms ConstitutiveSearch.SAT.executeCausalDecision_terminalProduced
/- AXIOM_AUDIT_END -/
