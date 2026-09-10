import ConstitutiveAlignment.FreshProbeCausality

set_option linter.checkUnivs false

/-!
# Governed dynamics at arbitrary finite depth

The generic iterator already constructs a proof-relevant history at every
natural depth.  This module equips that iteration with a governed invariant,
separates admissible machine evolution from parametric learning and memory
updating, and instantiates the result with the finite transformer.

No statement ranges over an untyped terminal state.  Reachability carries its
forming history, and no arbitrary update is declared alignment-preserving.
-/

namespace ConstitutiveAlignment

universe uState uStep uParameters uLearning uIncorporation

abbrev ReachableAt
    {State : Type uState}
    (transition : UniformTransition.{uState, uStep} State)
    (initial : State)
    (depth : Nat) : Type _ :=
  StrongPerimetralTurning.History transition.Step initial
    (iterateState transition depth initial)

def reachableAt
    {State : Type uState}
    (transition : UniformTransition.{uState, uStep} State)
    (initial : State)
    (depth : Nat) : ReachableAt transition initial depth :=
  iterateHistory transition depth initial

/-! ## Exact transport of adequacy -/

structure MachineAdequacyTransport
    (source target : ConstitutiveMachine) where
  sourceCandidate : target.Candidate → source.Candidate
  sourceCandidateInjective : Function.Injective sourceCandidate
  regimeToSource : (candidate : target.Candidate) →
    target.Regime candidate → source.Regime (sourceCandidate candidate)
  regimeToTarget : (candidate : target.Candidate) →
    source.Regime (sourceCandidate candidate) → target.Regime candidate
  normToSource : (candidate : target.Candidate) →
    target.Norm candidate → source.Norm (sourceCandidate candidate)
  normToTarget : (candidate : target.Candidate) →
    source.Norm (sourceCandidate candidate) → target.Norm candidate

def MachineAdequacyTransport.transport
    {source target : ConstitutiveMachine}
    (evolution : MachineAdequacyTransport source target)
    (adequacy : MachineAdequacy source) : MachineAdequacy target :=
  { sound := fun candidate admitted =>
      evolution.normToTarget candidate
        (adequacy.sound (evolution.sourceCandidate candidate)
          (evolution.regimeToSource candidate admitted))
    complete := fun candidate normative =>
      evolution.regimeToTarget candidate
        (adequacy.complete (evolution.sourceCandidate candidate)
          (evolution.normToSource candidate normative)) }

def MachineAdequacyTransport.identity
    (machine : ConstitutiveMachine) :
    MachineAdequacyTransport machine machine :=
  { sourceCandidate := fun candidate => candidate
    sourceCandidateInjective := by
      intro firstCandidate secondCandidate equality
      exact equality
    regimeToSource := fun _candidate admitted => admitted
    regimeToTarget := fun _candidate admitted => admitted
    normToSource := fun _candidate normative => normative
    normToTarget := fun _candidate normative => normative }

theorem MachineAdequacyTransport.identity_transport
    {machine : ConstitutiveMachine}
    (adequacy : MachineAdequacy machine) :
    (MachineAdequacyTransport.identity machine).transport adequacy = adequacy := by
  cases adequacy
  rfl

/- An alleged transport into a regime with no possible autonomous norm would
   manufacture an impossible adequacy witness. -/
theorem noAdequacyTransport_toRegimeWithoutNorm
    (evolution : MachineAdequacyTransport
      ReferenceModel.machine Separators.regimeWithoutNorm) : False :=
  Separators.regimeWithoutNorm_hasNoAdequacy
    (evolution.transport ReferenceModel.adequacy)

/-! ## Separating update planes -/

structure ExecutorTransport
    {sourceSignature targetSignature : ActionSignature}
    (source : NormativeExecutor sourceSignature)
    (target : NormativeExecutor targetSignature) where
  context : sourceSignature.Context → targetSignature.Context
  contextInjective : Function.Injective context
  action : ConstitutiveAction sourceSignature →
    ConstitutiveAction targetSignature
  actionInjective : Function.Injective action
  admission : {sourceContext : sourceSignature.Context} →
    {sourceAction : ConstitutiveAction sourceSignature} →
      source.Admission sourceContext sourceAction →
        target.Admission (context sourceContext) (action sourceAction)
  norm : {sourceContext : sourceSignature.Context} →
    {sourceAction : ConstitutiveAction sourceSignature} →
      source.Norm sourceContext sourceAction →
        target.Norm (context sourceContext) (action sourceAction)
  certificate : {sourceContext : sourceSignature.Context} →
    {sourceAction : ConstitutiveAction sourceSignature} →
      source.Certificate sourceContext sourceAction →
        target.Certificate (context sourceContext) (action sourceAction)

def ExecutorTransport.identity
    {signature : ActionSignature}
    (executor : NormativeExecutor signature) :
    ExecutorTransport executor executor :=
  { context := fun context => context
    contextInjective := by
      intro firstContext secondContext equality
      exact equality
    action := fun action => action
    actionInjective := by
      intro firstAction secondAction equality
      exact equality
    admission := fun admitted => admitted
    norm := fun normative => normative
    certificate := fun certificate => certificate }

def ExecutorTransport.effectuation
    {sourceSignature targetSignature : ActionSignature}
    {source : NormativeExecutor sourceSignature}
    {target : NormativeExecutor targetSignature}
    (transport : ExecutorTransport source target)
    {sourceContext : sourceSignature.Context}
    {sourceAction : ConstitutiveAction sourceSignature}
    (effectuation : CertifiedEffectuation source sourceContext sourceAction) :
    CertifiedEffectuation target
      (transport.context sourceContext) (transport.action sourceAction) :=
  target.effectuate (transport.certificate effectuation.certificate)

structure AdmissibleEvolution
    {State : Type uState}
    (Parameters : Type uParameters)
    (transition : UniformTransition State)
    (encoding : MemoryEncoding State)
    (sourceMachine targetMachine : ConstitutiveMachine)
    {sourceSignature targetSignature : ActionSignature}
    (sourceExecutor : NormativeExecutor sourceSignature)
    (targetExecutor : NormativeExecutor targetSignature) where
  learning : ParametricLearning.{uParameters, uLearning} Parameters
  incorporation : ConstitutiveIncorporation.{uState, uIncorporation} State
  incorporationIsTransition : (state : State) →
    incorporation.incorporated state = transition.next state
  memory : AutonomousMemoryUpdate encoding transition.next
  machine : MachineAdequacyTransport sourceMachine targetMachine
  execution : ExecutorTransport sourceExecutor targetExecutor

def AdmissibleEvolution.targetAdequacy
    {State : Type uState}
    {Parameters : Type uParameters}
    {transition : UniformTransition State}
    {encoding : MemoryEncoding State}
    {sourceMachine targetMachine : ConstitutiveMachine}
    {sourceSignature targetSignature : ActionSignature}
    {sourceExecutor : NormativeExecutor sourceSignature}
    {targetExecutor : NormativeExecutor targetSignature}
    (evolution : AdmissibleEvolution Parameters transition encoding
      sourceMachine targetMachine sourceExecutor targetExecutor)
    (sourceAdequacy : MachineAdequacy sourceMachine) :
    MachineAdequacy targetMachine :=
  evolution.machine.transport sourceAdequacy

theorem normativeRefutation_blocksEffectuation
    {signature : ActionSignature}
    {executor : NormativeExecutor signature}
    {context : signature.Context}
    {action : ConstitutiveAction signature}
    (refuted : executor.Norm context action → False) :
    CertifiedEffectuation executor context action → False :=
  fun effectuation => refuted effectuation.normative

/-! ## Arbitrary-depth transformer instance -/

namespace TransformerGovernedDynamics

open TransformerExamples
open TransformerDynamics

def viewAt (depth : Nat) : View :=
  iterateState transition depth fixedView

def traceAt (depth : Nat) :
    TransformerPrimaryTrace core learnedWeights (viewAt depth) :=
  run (viewAt depth)

def candidateAt (view : View) : ReferenceModel.Candidate :=
  proposalCandidate (run view).causal.proposal

def faithfulCandidate : (candidate : ReferenceModel.Candidate) →
    ReferenceModel.machine.Faithful candidate
  | .admitted => .admittedTrace
  | .outside => .outsideTrace

def faithfulTrajectory (candidate : ReferenceModel.Candidate) :
    FullTrajectoryRealization ReferenceModel.machine candidate
      (ReferenceModel.machine.RealizedOccurrence candidate)
      (fun _occurrence => Unit) :=
  { occurrenceMap :=
      ReferenceModel.machine.occurrenceRealization
        (faithfulCandidate candidate)
    consumed := fun _occurrence => () }

inductive RelativeNormStatus (candidate : ReferenceModel.Candidate) : Type
  | satisfied : ReferenceModel.machine.Norm candidate →
      RelativeNormStatus candidate
  | refuted : (ReferenceModel.machine.Norm candidate → False) →
      RelativeNormStatus candidate

def relativeNormStatus : (candidate : ReferenceModel.Candidate) →
    RelativeNormStatus candidate
  | .admitted => .satisfied .satisfied
  | .outside => .refuted (fun normative => nomatch normative)

theorem candidateNormRefutation_blocksEffectuation
    (candidate : ReferenceModel.Candidate)
    (refuted : ReferenceModel.machine.Norm candidate → False) :
    CertifiedEffectuation ReferenceModel.actionExecutor false
      (ReferenceModel.actionOfCandidate candidate) → False := by
  cases candidate with
  | admitted =>
      exact fun _effectuation => refuted .satisfied
  | outside =>
      exact ReferenceModel.rejectedAction_cannotBeEffectuated

def viewFuture : FutureQuestions View where
  Question := Bool
  Answer := fun _question => Bool
  behaviour := fun view query => view.memory.attend query

def viewMemory : MemoryEncoding View where
  Memory := Bool × Bool
  encode := fun view => attentionMemory.encode view.memory

theorem viewMemoryExact : ExactCausalMemory viewFuture viewMemory where
  sound := by
    intro leftView rightView sameMemory query
    exact attentionMemoryExact.sound sameMemory query
  complete := by
    intro leftView rightView equivalent
    exact attentionMemoryExact.complete (fun query => equivalent query)

def viewMemoryUpdate : AutonomousMemoryUpdate viewMemory transition.next where
  update := fun memory => memory
  commutes := fun _view => rfl

def transformerLearning : ParametricLearning Bool where
  learned := Bool.not
  LearningEvidence := LearningEvidence
  evidence := by
    intro parameters
    cases parameters
    · exact .falseToTrue
    · exact .trueToFalse

def transformerIncorporation : ConstitutiveIncorporation View where
  incorporated := transition.next
  Incorporates := fun source target => PLift (target = transition.next source)
  witness := fun _state => ⟨rfl⟩

def admissibleEvolution : AdmissibleEvolution Bool transition viewMemory
    ReferenceModel.machine ReferenceModel.machine
    ReferenceModel.actionExecutor ReferenceModel.actionExecutor :=
  { learning := transformerLearning
    incorporation := transformerIncorporation
    incorporationIsTransition := fun _state => rfl
    memory := viewMemoryUpdate
    machine := MachineAdequacyTransport.identity ReferenceModel.machine
    execution := ExecutorTransport.identity ReferenceModel.actionExecutor }

def transportedAdequacy : MachineAdequacy ReferenceModel.machine :=
  admissibleEvolution.targetAdequacy ReferenceModel.adequacy

structure GovernedInvariant (view : View) where
  formation : StrongPerimetralTurning.History
    transition.Step fixedView view
  tokensRetained : view.tokens = fixedView.tokens
  cacheRetained : view.cache = fixedView.cache
  memoryRetained : viewMemory.encode view = viewMemory.encode fixedView
  budgetRetained : view.budget = fixedView.budget
  memoryExact : ExactCausalMemory viewFuture viewMemory
  adequacy : MachineAdequacy ReferenceModel.machine
  faithful : ReferenceModel.machine.Faithful (candidateAt view)
  trajectory : FullTrajectoryRealization ReferenceModel.machine
    (candidateAt view)
    (ReferenceModel.machine.RealizedOccurrence (candidateAt view))
    (fun _occurrence => Unit)
  elaborationRetained :
    (run view).causal.elaboration =
      core.elaborate (run view).causal.proposal
  normStatus : RelativeNormStatus (candidateAt view)
  rejectedEffectBlocked :
    (ReferenceModel.machine.Norm (candidateAt view) → False) →
      CertifiedEffectuation ReferenceModel.actionExecutor false
        (ReferenceModel.actionOfCandidate (candidateAt view)) → False

def initialInvariant : GovernedInvariant fixedView :=
  { formation := .root
    tokensRetained := rfl
    cacheRetained := rfl
    memoryRetained := rfl
    budgetRetained := rfl
    memoryExact := viewMemoryExact
    adequacy := transportedAdequacy
    faithful := faithfulCandidate (candidateAt fixedView)
    trajectory := faithfulTrajectory (candidateAt fixedView)
    elaborationRetained := rfl
    normStatus := relativeNormStatus (candidateAt fixedView)
    rejectedEffectBlocked :=
      candidateNormRefutation_blocksEffectuation (candidateAt fixedView) }

def preservesInvariant : Preserves transition GovernedInvariant :=
  fun {view} invariant =>
    { formation := .extend invariant.formation (transition.step view)
      tokensRetained := invariant.tokensRetained
      cacheRetained := invariant.cacheRetained
      memoryRetained := invariant.memoryRetained
      budgetRetained := invariant.budgetRetained
      memoryExact := viewMemoryExact
      adequacy := transportedAdequacy
      faithful := faithfulCandidate (candidateAt (transition.next view))
      trajectory := faithfulTrajectory (candidateAt (transition.next view))
      elaborationRetained := rfl
      normStatus := relativeNormStatus (candidateAt (transition.next view))
      rejectedEffectBlocked :=
        candidateNormRefutation_blocksEffectuation
          (candidateAt (transition.next view)) }

def invariantAt (depth : Nat) : GovernedInvariant (viewAt depth) :=
  preservesAlongIteration
    (transition := transition)
    (Obligation := GovernedInvariant)
    preservesInvariant depth fixedView initialInvariant

def reachableTransformerAt (depth : Nat) :
    ReachableAt transition fixedView depth :=
  (invariantAt depth).formation

theorem proposalIsNextConsumedRelation (depth : Nat) :
    (viewAt (Nat.succ depth)).relation =
      (traceAt depth).causal.proposal :=
  rfl

theorem memoryRetainedAtEveryDepth (depth : Nat) :
    viewMemory.encode (viewAt depth) = viewMemory.encode fixedView :=
  (invariantAt depth).memoryRetained

def relationAblation (view : View) : View :=
  withRelation view (Bool.not view.relation)

theorem relationAblation_changesPrediction
    (view : View)
    (invariant : GovernedInvariant view) :
    (run view).causal.predicted =
      (run (relationAblation view)).causal.predicted → False := by
  have tokensEquality := invariant.tokensRetained
  have cacheEquality := invariant.cacheRetained
  have memoryEquality := invariant.memoryRetained
  cases view with
  | mk tokens cache memory relation budget =>
      cases tokensEquality
      cases cacheEquality
      cases memory with
      | mk left right focus =>
          have leftEquality := congrArg Prod.fst memoryEquality
          have rightEquality := congrArg Prod.snd memoryEquality
          cases leftEquality
          cases rightEquality
          cases relation <;> intro impossible <;> nomatch impossible

theorem relationAblation_changesPredictionAtEveryDepth (depth : Nat) :
    (run (viewAt depth)).causal.predicted =
      (run (relationAblation (viewAt depth))).causal.predicted → False :=
  relationAblation_changesPrediction (viewAt depth) (invariantAt depth)

theorem relationAblation_changesProposal
    (view : View)
    (invariant : GovernedInvariant view) :
    (run view).causal.proposal =
      (run (relationAblation view)).causal.proposal → False := by
  have tokensEquality := invariant.tokensRetained
  have cacheEquality := invariant.cacheRetained
  have memoryEquality := invariant.memoryRetained
  cases view with
  | mk tokens cache memory relation budget =>
      cases tokensEquality
      cases cacheEquality
      cases memory with
      | mk left right focus =>
          have leftEquality := congrArg Prod.fst memoryEquality
          have rightEquality := congrArg Prod.snd memoryEquality
          cases leftEquality
          cases rightEquality
          cases relation <;> intro impossible <;> nomatch impossible

theorem relationAblation_changesProposalAtEveryDepth (depth : Nat) :
    (run (viewAt depth)).causal.proposal =
      (run (relationAblation (viewAt depth))).causal.proposal → False :=
  relationAblation_changesProposal (viewAt depth) (invariantAt depth)

theorem relationAblation_changesNextViewAtEveryDepth (depth : Nat) :
    transition.next (viewAt depth) =
      transition.next (relationAblation (viewAt depth)) → False := by
  intro sameSuccessor
  have sameRelation := congrArg (fun view : View => view.relation) sameSuccessor
  change (run (viewAt depth)).causal.proposal =
    (run (relationAblation (viewAt depth))).causal.proposal at sameRelation
  exact relationAblation_changesProposalAtEveryDepth depth sameRelation

/-! ## Constructive bounded stopping witness -/

abbrev BoundedState := View × Bool

inductive HasBudget : BoundedState → Type
  | available (view : View) : HasBudget (view, true)

def boundedTransition : PartialTransition BoundedState where
  CanAdvance := HasBudget
  next := fun {state} permission =>
    match permission with
    | .available view => (transition.next view, false)
  Step := fun source target => PLift
    (target.1 = transition.next source.1 ∧ target.2 = false)
  step := by
    intro state permission
    cases permission
    exact ⟨rfl, rfl⟩
  decide := by
    intro state
    cases state with
    | mk view available =>
        cases available
        · exact .stop (fun permission => nomatch permission)
        · exact .advance (.available view)

def boundedFirstStep :
    PartialStepResult boundedTransition (fixedView, true) :=
  boundedTransition.run (fixedView, true)

def boundedExplicitStop :
    PartialStepResult boundedTransition (transition.next fixedView, false) :=
  boundedTransition.run (transition.next fixedView, false)

structure GateLCertificate where
  strictFreshProbeAcquisition : StrictFreshProbeCausality
    FreshProbeExamples.trainingProcedure FreshProbeExamples.protocol
      TransformerExamples.succession false
  acquiredWeightsAreUsed :
    FreshProbeExamples.protocol.learnedState false = learnedWeights
  arbitraryDepth : (depth : Nat) → GovernedInvariant (viewAt depth)
  reachability : (depth : Nat) → ReachableAt transition fixedView depth
  nextConsumesPreviousProposal : (depth : Nat) →
    (viewAt (Nat.succ depth)).relation = (traceAt depth).causal.proposal
  memoryAtEveryDepth : (depth : Nat) →
    viewMemory.encode (viewAt depth) = viewMemory.encode fixedView
  ablationAtEveryDepth : (depth : Nat) →
    (run (viewAt depth)).causal.predicted =
      (run (relationAblation (viewAt depth))).causal.predicted → False
  ablationChangesSuccessorAtEveryDepth : (depth : Nat) →
    transition.next (viewAt depth) =
      transition.next (relationAblation (viewAt depth)) → False
  evolution : AdmissibleEvolution Bool transition viewMemory
    ReferenceModel.machine ReferenceModel.machine
    ReferenceModel.actionExecutor ReferenceModel.actionExecutor
  targetAdequacy : MachineAdequacy ReferenceModel.machine
  firstStep : PartialStepResult boundedTransition (fixedView, true)
  explicitStop : PartialStepResult boundedTransition
    (transition.next fixedView, false)

def gateLCertificate : GateLCertificate :=
  { strictFreshProbeAcquisition := FreshProbeExamples.strictCausality
    acquiredWeightsAreUsed :=
      FreshProbeExamples.learnedState_isTransformerLearnedWeights
    arbitraryDepth := invariantAt
    reachability := reachableTransformerAt
    nextConsumesPreviousProposal := proposalIsNextConsumedRelation
    memoryAtEveryDepth := memoryRetainedAtEveryDepth
    ablationAtEveryDepth := relationAblation_changesPredictionAtEveryDepth
    ablationChangesSuccessorAtEveryDepth :=
      relationAblation_changesNextViewAtEveryDepth
    evolution := admissibleEvolution
    targetAdequacy := transportedAdequacy
    firstStep := boundedFirstStep
    explicitStop := boundedExplicitStop }

end TransformerGovernedDynamics

end ConstitutiveAlignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveAlignment.reachableAt
#print axioms ConstitutiveAlignment.MachineAdequacyTransport.transport
#print axioms ConstitutiveAlignment.MachineAdequacyTransport.identity_transport
#print axioms ConstitutiveAlignment.noAdequacyTransport_toRegimeWithoutNorm
#print axioms ConstitutiveAlignment.AdmissibleEvolution.targetAdequacy
#print axioms ConstitutiveAlignment.ExecutorTransport.effectuation
#print axioms ConstitutiveAlignment.normativeRefutation_blocksEffectuation
#print axioms ConstitutiveAlignment.TransformerGovernedDynamics.viewMemoryExact
#print axioms ConstitutiveAlignment.TransformerGovernedDynamics.admissibleEvolution
#print axioms ConstitutiveAlignment.TransformerGovernedDynamics.preservesInvariant
#print axioms ConstitutiveAlignment.TransformerGovernedDynamics.invariantAt
#print axioms ConstitutiveAlignment.TransformerGovernedDynamics.proposalIsNextConsumedRelation
#print axioms ConstitutiveAlignment.TransformerGovernedDynamics.relationAblation_changesPredictionAtEveryDepth
#print axioms ConstitutiveAlignment.TransformerGovernedDynamics.relationAblation_changesProposalAtEveryDepth
#print axioms ConstitutiveAlignment.TransformerGovernedDynamics.relationAblation_changesNextViewAtEveryDepth
#print axioms ConstitutiveAlignment.TransformerGovernedDynamics.boundedExplicitStop
#print axioms ConstitutiveAlignment.TransformerGovernedDynamics.gateLCertificate
/- AXIOM_AUDIT_END -/
