import ConstitutiveAlignment.Machine

set_option linter.checkUnivs false

/-!
# Abstract neural realization

The neural plane receives an explicitly bounded view and may only propose a
discrete object.  Total elaboration either accepts that proposal or returns its
first localized error while preserving the rejected proposal.  Primary causal
values are recorded before a read-only deferred audit.
-/

namespace ConstitutiveAlignment

universe uProposal uCandidate uError

inductive ElaborationOutcome
    (Proposal : Type uProposal)
    (Candidate : Type uCandidate)
    (Error : Type uError)
    (proposal : Proposal) : Type _
  | accepted : Candidate → ElaborationOutcome Proposal Candidate Error proposal
  | rejected : Error → ElaborationOutcome Proposal Candidate Error proposal

universe uReason

structure LocalizedError (Reason : Type uReason) where
  position : Nat
  reason : Reason

universe uConstitutive uFormal uOperational uLearned uView uPrediction

/- The four plans remain visible as distinct carriers.  No proof, norm,
   certificate, future verdict, or audit output is a field of `AuthorizedView`. -/
structure NeuralProposalSystem where
  ConstitutiveState : Type uConstitutive
  FormalCandidate : Type uFormal
  OperationalObject : Type uOperational
  LearnedState : Type uLearned
  AuthorizedView : Type uView
  Prediction : Type uPrediction
  Proposal : Type uProposal
  Error : Type uError
  predict : LearnedState → AuthorizedView → Prediction
  propose : AuthorizedView → Prediction → Proposal
  elaborate : (proposal : Proposal) →
    ElaborationOutcome Proposal FormalCandidate Error proposal

/- The predicted value and the value consumed by proposition are both primary
   fields, tied by an equality rather than reconstructed from a digest. -/
structure NeuralCausalTrace
    (system : NeuralProposalSystem)
    (learnedState : system.LearnedState)
    (view : system.AuthorizedView) where
  predicted : system.Prediction
  predictedExact : predicted = system.predict learnedState view
  consumedPrediction : system.Prediction
  consumedExact : consumedPrediction = predicted
  proposal : system.Proposal
  proposalExact : proposal = system.propose view consumedPrediction
  elaboration :
    ElaborationOutcome system.Proposal system.FormalCandidate system.Error proposal

def NeuralProposalSystem.run
    (system : NeuralProposalSystem)
    (learnedState : system.LearnedState)
    (view : system.AuthorizedView) :
    NeuralCausalTrace system learnedState view :=
  { predicted := system.predict learnedState view
    predictedExact := rfl
    consumedPrediction := system.predict learnedState view
    consumedExact := rfl
    proposal := system.propose view (system.predict learnedState view)
    proposalExact := rfl
    elaboration :=
      system.elaborate
        (system.propose view (system.predict learnedState view)) }

structure NeuralIntervention
    (system : NeuralProposalSystem)
    (parent learned : system.LearnedState)
    (view : system.AuthorizedView) where
  parentTrace : NeuralCausalTrace system parent view
  learnedTrace : NeuralCausalTrace system learned view
  predictionChanges :
    parentTrace.predicted = learnedTrace.predicted → False
  proposalChanges : parentTrace.proposal = learnedTrace.proposal → False

universe uOperationalOccurrence uConsumed

/- Fidelity ranges over the whole occurrence carrier, not only a terminal
   neural output. -/
structure FullTrajectoryRealization
    (machine : ConstitutiveMachine)
    (candidate : machine.Candidate)
    (OperationalOccurrence : Type uOperationalOccurrence)
    (Consumed : OperationalOccurrence → Type uConsumed) where
  occurrenceMap :
    InjectiveMap (machine.Occurrence candidate) OperationalOccurrence
  consumed : (occurrence : machine.Occurrence candidate) →
    Consumed (occurrenceMap.toFun occurrence)

universe uTrace uReport

structure SealedTrace (Trace : Type uTrace) where
  primary : Trace

structure DeferredAudit
    (Trace : Type uTrace)
    (Report : Type uReport) where
  inspect : SealedTrace Trace → Report

def runDeferredAudit
    {Trace : Type uTrace}
    {Report : Type uReport}
    (audit : DeferredAudit Trace Report)
    (sealed : SealedTrace Trace) : SealedTrace Trace × Report :=
  ⟨sealed, audit.inspect sealed⟩

theorem deferredAudit_preservesPrimaryTrace
    {Trace : Type uTrace}
    {Report : Type uReport}
    (audit : DeferredAudit Trace Report)
    (sealed : SealedTrace Trace) :
    (runDeferredAudit audit sealed).1 = sealed :=
  rfl

/-! ## Finite neural separators -/

namespace NeuralExamples

inductive ErrorReason : Type
  | falseProposal

def system : NeuralProposalSystem where
  ConstitutiveState := Bool
  FormalCandidate := Bool
  OperationalObject := Bool
  LearnedState := Bool
  AuthorizedView := Unit
  Prediction := Bool
  Proposal := Bool
  Error := LocalizedError ErrorReason
  predict := fun learnedState _view => learnedState
  propose := fun _view prediction => prediction
  elaborate
    | false => .rejected ⟨0, .falseProposal⟩
    | true => .accepted true

def parentTrace : NeuralCausalTrace system false () :=
  system.run false ()

def learnedTrace : NeuralCausalTrace system true () :=
  system.run true ()

theorem neuralPredictionChanges :
    parentTrace.predicted = learnedTrace.predicted → False := by
  intro impossible
  nomatch impossible

theorem neuralProposalChanges :
    parentTrace.proposal = learnedTrace.proposal → False := by
  intro impossible
  nomatch impossible

def intervention : NeuralIntervention system false true () :=
  { parentTrace := parentTrace
    learnedTrace := learnedTrace
    predictionChanges := neuralPredictionChanges
    proposalChanges := neuralProposalChanges }

theorem rejectedProposal_isPreserved :
    parentTrace.elaboration =
      ElaborationOutcome.rejected ⟨0, .falseProposal⟩ :=
  rfl

def constantProposalSystem : NeuralProposalSystem where
  ConstitutiveState := Unit
  FormalCandidate := Unit
  OperationalObject := Unit
  LearnedState := Bool
  AuthorizedView := Unit
  Prediction := Bool
  Proposal := Unit
  Error := Unit
  predict := fun learnedState _view => learnedState
  propose := fun _view _prediction => ()
  elaborate := fun _proposal => .accepted ()

theorem constantProposalSystem_hasNoIntervention :
    NeuralIntervention constantProposalSystem false true () → False :=
  fun allegedIntervention => allegedIntervention.proposalChanges rfl

def audit : DeferredAudit
    (NeuralCausalTrace system false ()) Unit where
  inspect := fun _sealed => ()

def sealedParentTrace :
    SealedTrace (NeuralCausalTrace system false ()) :=
  ⟨parentTrace⟩

theorem auditDoesNotChangeParentTrace :
    (runDeferredAudit audit sealedParentTrace).1 = sealedParentTrace :=
  deferredAudit_preservesPrimaryTrace audit sealedParentTrace

end NeuralExamples

end ConstitutiveAlignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveAlignment.NeuralProposalSystem.run
#print axioms ConstitutiveAlignment.runDeferredAudit
#print axioms ConstitutiveAlignment.deferredAudit_preservesPrimaryTrace
#print axioms ConstitutiveAlignment.NeuralExamples.intervention
#print axioms ConstitutiveAlignment.NeuralExamples.rejectedProposal_isPreserved
#print axioms ConstitutiveAlignment.NeuralExamples.constantProposalSystem_hasNoIntervention
#print axioms ConstitutiveAlignment.NeuralExamples.auditDoesNotChangeParentTrace
/- AXIOM_AUDIT_END -/
