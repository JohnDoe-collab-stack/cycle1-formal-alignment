import ConstitutiveAlignment.NeuralRealization
import ConstitutiveAlignment.ReferenceModel

set_option linter.checkUnivs false

/-!
# Transformer realization

The transformer is an instance of the bounded neural plane.  Tokens,
activations, cache, addressable memory, and a constitutive relation are primary
objects.  The relation is consumed by prediction; it is not a passive label.
This file closes a controlled one-step intervention only, not transformer
multicycle autonomy.
-/

namespace ConstitutiveAlignment

universe uToken uActivation uCache uMemoryReference uRelation
universe uWeights uLearning uPrediction uProposal uCandidate uError

structure TransformerAuthorizedView
    (Token : Type uToken)
    (Cache : Type uCache)
    (MemoryReference : Type uMemoryReference)
    (Relation : Type uRelation) where
  tokens : List Token
  cache : Cache
  memory : MemoryReference
  relation : Relation
  budget : Nat

structure TransformerCore where
  Token : Type uToken
  Activation : Type uActivation
  Cache : Type uCache
  MemoryReference : Type uMemoryReference
  Relation : Type uRelation
  Weights : Type uWeights
  LearningEvidence : Weights → Weights → Type uLearning
  learn : Weights → Weights
  learningEvidence : (weights : Weights) →
    LearningEvidence weights (learn weights)
  Prediction : Type uPrediction
  Proposal : Type uProposal
  Candidate : Type uCandidate
  Error : Type uError
  activate : List Token → Activation
  predict : Weights → Activation →
    TransformerAuthorizedView Token Cache MemoryReference Relation → Prediction
  propose :
    TransformerAuthorizedView Token Cache MemoryReference Relation →
      Prediction → Proposal
  elaborate : (proposal : Proposal) →
    ElaborationOutcome Proposal Candidate Error proposal

def TransformerCore.toNeuralSystem
    (core : TransformerCore) : NeuralProposalSystem where
  ConstitutiveState := core.Relation
  FormalCandidate := core.Candidate
  OperationalObject := core.Proposal
  LearnedState := core.Weights
  AuthorizedView := TransformerAuthorizedView
    core.Token core.Cache core.MemoryReference core.Relation
  Prediction := core.Prediction
  Proposal := core.Proposal
  Error := core.Error
  predict := fun weights view =>
    core.predict weights (core.activate view.tokens) view
  propose := core.propose
  elaborate := core.elaborate

structure TransformerPrimaryTrace
    (core : TransformerCore)
    (weights : core.Weights)
    (view : TransformerAuthorizedView
      core.Token core.Cache core.MemoryReference core.Relation) where
  activation : core.Activation
  activationExact : activation = core.activate view.tokens
  causal : NeuralCausalTrace core.toNeuralSystem weights view

def TransformerCore.run
    (core : TransformerCore)
    (weights : core.Weights)
    (view : TransformerAuthorizedView
      core.Token core.Cache core.MemoryReference core.Relation) :
    TransformerPrimaryTrace core weights view :=
  { activation := core.activate view.tokens
    activationExact := rfl
    causal := core.toNeuralSystem.run weights view }

structure TransformerLearningIntervention
    (core : TransformerCore)
    (parent : core.Weights)
    (view : TransformerAuthorizedView
      core.Token core.Cache core.MemoryReference core.Relation) where
  learning : core.LearningEvidence parent (core.learn parent)
  causal : NeuralIntervention core.toNeuralSystem parent (core.learn parent) view

universe uRejectReason uTransformerRejected uTransformerSuccession

structure TransformerSuccession (core : TransformerCore) where
  RejectReason : Type uRejectReason
  Rejected : core.Relation → core.Proposal → RejectReason →
    Type uTransformerRejected
  successor : core.Relation → core.Proposal → core.Relation
  Succeeds : core.Relation → core.Proposal → core.Relation →
    Type uTransformerSuccession

/- This witness adds the two outcome branches required by the causal contract.
   It does not identify neural acceptance with constitutive succession. -/
structure TransformerCausalSuccession
    (core : TransformerCore)
    (succession : TransformerSuccession core)
    {parent : core.Weights}
    {view : TransformerAuthorizedView
      core.Token core.Cache core.MemoryReference core.Relation}
    (intervention : TransformerLearningIntervention core parent view) where
  parentRejectReason : succession.RejectReason
  parentRejected : succession.Rejected view.relation
    intervention.causal.parentTrace.proposal parentRejectReason
  learnedSucceeds : succession.Succeeds view.relation
    intervention.causal.learnedTrace.proposal
    (succession.successor view.relation
      intervention.causal.learnedTrace.proposal)

/-! ## Finite one-step transformer -/

namespace TransformerExamples

/- A technical memory address is renamed together with its store.  Reading the
   renamed focus returns the same content, so the address itself carries no
   hidden semantic identity. -/
structure TwoCellMemory where
  left : Bool
  right : Bool
  focus : Bool

def TwoCellMemory.read : TwoCellMemory → Bool
  | ⟨left, _right, false⟩ => left
  | ⟨_left, right, true⟩ => right

def TwoCellMemory.rename : TwoCellMemory → TwoCellMemory
  | ⟨left, right, focus⟩ => ⟨right, left, Bool.not focus⟩

theorem TwoCellMemory.read_rename (memory : TwoCellMemory) :
    memory.rename.read = memory.read := by
  cases memory with
  | mk left right focus =>
      cases focus <;> rfl

def tokenParity : List Bool → Bool
  | [] => false
  | token :: remaining => Bool.xor token (tokenParity remaining)

inductive LearningEvidence : Bool → Bool → Type
  | falseToTrue : LearningEvidence false true
  | trueToFalse : LearningEvidence true false

inductive ErrorReason : Type
  | rejectedFalse

def core : TransformerCore where
  Token := Bool
  Activation := Bool
  Cache := Bool
  MemoryReference := TwoCellMemory
  Relation := Bool
  Weights := Bool
  LearningEvidence := LearningEvidence
  learn := Bool.not
  learningEvidence := by
    intro weights
    cases weights
    · exact .falseToTrue
    · exact .trueToFalse
  Prediction := Bool
  Proposal := Bool
  Candidate := Bool
  Error := LocalizedError ErrorReason
  activate := tokenParity
  predict := fun weights activation view =>
    Bool.xor weights
      (Bool.xor activation
        (Bool.xor view.cache
          (Bool.xor view.memory.read view.relation)))
  propose := fun _view prediction => prediction
  elaborate
    | false => .rejected ⟨0, .rejectedFalse⟩
    | true => .accepted true

def fixedView : TransformerAuthorizedView Bool Bool TwoCellMemory Bool where
  tokens := [false]
  cache := false
  memory := ⟨false, true, false⟩
  relation := false
  budget := 1

def parentTrace : TransformerPrimaryTrace core false fixedView :=
  core.run false fixedView

def learnedTrace : TransformerPrimaryTrace core true fixedView :=
  core.run true fixedView

theorem transformerPredictionChanges :
    parentTrace.causal.predicted = learnedTrace.causal.predicted → False := by
  intro impossible
  nomatch impossible

theorem transformerProposalChanges :
    parentTrace.causal.proposal = learnedTrace.causal.proposal → False := by
  intro impossible
  nomatch impossible

def oneStepIntervention :
    TransformerLearningIntervention core false fixedView :=
  { learning := .falseToTrue
    causal :=
      { parentTrace := parentTrace.causal
        learnedTrace := learnedTrace.causal
        predictionChanges := transformerPredictionChanges
        proposalChanges := transformerProposalChanges } }

inductive SuccessionRejectReason : Type
  | unchangedPrediction

inductive Rejected : Bool → Bool → SuccessionRejectReason → Type
  | parentFalse : Rejected false false .unchangedPrediction

inductive Succeeds : Bool → Bool → Bool → Type
  | learnedTrue : Succeeds false true true

def succession : TransformerSuccession core where
  RejectReason := SuccessionRejectReason
  Rejected := Rejected
  successor := fun _relation proposal => proposal
  Succeeds := Succeeds

def causalSuccession :
    TransformerCausalSuccession core succession oneStepIntervention :=
  { parentRejectReason := .unchangedPrediction
    parentRejected := .parentFalse
    learnedSucceeds := .learnedTrue }

def relationAblatedView :
    TransformerAuthorizedView Bool Bool TwoCellMemory Bool where
  tokens := fixedView.tokens
  cache := fixedView.cache
  memory := fixedView.memory
  relation := true
  budget := fixedView.budget

theorem consumedRelation_changesFuturePrediction :
    (core.run false fixedView).causal.predicted =
      (core.run false relationAblatedView).causal.predicted → False := by
  intro impossible
  nomatch impossible

def renameMemoryInView
    (view : TransformerAuthorizedView Bool Bool TwoCellMemory Bool) :
    TransformerAuthorizedView Bool Bool TwoCellMemory Bool where
  tokens := view.tokens
  cache := view.cache
  memory := view.memory.rename
  relation := view.relation
  budget := view.budget

theorem predictionInvariant_underAddressRenaming
    (weights activation : Bool)
    (view : TransformerAuthorizedView Bool Bool TwoCellMemory Bool) :
    core.predict weights activation (renameMemoryInView view) =
      core.predict weights activation view := by
  cases view with
  | mk tokens cache memory relation budget =>
      cases memory with
      | mk left right focus =>
          cases focus <;> rfl

/- Removing the relation from the control computation makes the targeted
   relation intervention inert. -/
def inertRelationPrediction
    (weights activation : Bool)
    (view : TransformerAuthorizedView Bool Bool TwoCellMemory Bool) : Bool :=
  Bool.xor weights
    (Bool.xor activation (Bool.xor view.cache view.memory.read))

theorem inertRelationControl_doesNotChangePrediction :
    inertRelationPrediction false false fixedView =
      inertRelationPrediction false false relationAblatedView :=
  rfl

def occurrenceRealization : FullTrajectoryRealization
    ReferenceModel.machine .outside
    (StrongPerimetralTurning.History.Occurrence ReferenceModel.outsideHistory)
    (fun _occurrence => Unit) :=
  { occurrenceMap :=
      { toFun := fun occurrence => occurrence
        injective := by
          intro firstOccurrence secondOccurrence equality
          exact equality }
    consumed := fun _occurrence => () }

theorem rejectedParentProposal_isPreserved :
    parentTrace.causal.elaboration =
      ElaborationOutcome.rejected ⟨0, .rejectedFalse⟩ :=
  rfl

theorem acceptedLearnedProposal_isPreserved :
    learnedTrace.causal.elaboration =
      ElaborationOutcome.accepted true :=
  rfl

end TransformerExamples

end ConstitutiveAlignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveAlignment.TransformerCore.toNeuralSystem
#print axioms ConstitutiveAlignment.TransformerCore.run
#print axioms ConstitutiveAlignment.TransformerExamples.oneStepIntervention
#print axioms ConstitutiveAlignment.TransformerExamples.causalSuccession
#print axioms ConstitutiveAlignment.TransformerExamples.consumedRelation_changesFuturePrediction
#print axioms ConstitutiveAlignment.TransformerExamples.predictionInvariant_underAddressRenaming
#print axioms ConstitutiveAlignment.TransformerExamples.inertRelationControl_doesNotChangePrediction
#print axioms ConstitutiveAlignment.TransformerExamples.occurrenceRealization
#print axioms ConstitutiveAlignment.TransformerExamples.rejectedParentProposal_isPreserved
#print axioms ConstitutiveAlignment.TransformerExamples.acceptedLearnedProposal_isPreserved
/- AXIOM_AUDIT_END -/
