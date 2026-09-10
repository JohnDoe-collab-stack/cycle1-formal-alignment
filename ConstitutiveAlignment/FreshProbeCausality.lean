import ConstitutiveAlignment.TransformerDynamics

set_option linter.checkUnivs false

/-!
# Strict fresh-probe learning causality

The causal chain from learning to the next constitutive proposal is strengthened
with an upstream acquisition protocol.  Training input and evaluation probe have
distinct roles and values, the selected probe is bound by a unique commitment,
and freshness is a constructive refutation of membership in the training
corpus.  Parent and learned paths then share one authorized view; only the
learned predictive state differs.

The generic contract remains conditional.  The finite transformer instance
constructs every field and does not obtain freshness from an external assumption.
-/

namespace ConstitutiveAlignment

universe uCorpus uProbe uTraining uCommitment uBinding

structure TransformerTrainingProcedure (core : TransformerCore) where
  Corpus : Type uCorpus
  Probe : Type uProbe
  InCorpus : Corpus → Probe → Prop
  train : Corpus → core.Weights → core.Weights
  TrainingEvidence : Corpus → core.Weights → core.Weights → Type uTraining
  trainingEvidence : (corpus : Corpus) → (parent : core.Weights) →
    TrainingEvidence corpus parent (train corpus parent)
  view : Probe → TransformerAuthorizedView
    core.Token core.Cache core.MemoryReference core.Relation

structure FixedFreshProbeProtocol
    {core : TransformerCore}
    (training : TransformerTrainingProcedure core) where
  corpus : training.Corpus
  probe : training.Probe
  Commitment : Type uCommitment
  commitment : Commitment
  Binds : Commitment → training.Corpus → training.Probe → Type uBinding
  bound : Binds commitment corpus probe
  bindingUnique : {otherCorpus : training.Corpus} →
    {otherProbe : training.Probe} →
    Binds commitment otherCorpus otherProbe →
      otherCorpus = corpus ∧ otherProbe = probe
  fresh : training.InCorpus corpus probe → False

def FixedFreshProbeProtocol.authorizedView
    {core : TransformerCore}
    {training : TransformerTrainingProcedure core}
    (protocol : FixedFreshProbeProtocol training) :
    TransformerAuthorizedView
      core.Token core.Cache core.MemoryReference core.Relation :=
  training.view protocol.probe

def FixedFreshProbeProtocol.learnedState
    {core : TransformerCore}
    {training : TransformerTrainingProcedure core}
    (protocol : FixedFreshProbeProtocol training)
    (parent : core.Weights) : core.Weights :=
  training.train protocol.corpus parent

structure StrictFreshProbeCausality
    {core : TransformerCore}
    (training : TransformerTrainingProcedure core)
    (protocol : FixedFreshProbeProtocol training)
    (succession : TransformerSuccession core)
    (parent : core.Weights) where
  learning : training.TrainingEvidence protocol.corpus parent
    (protocol.learnedState parent)
  intervention : NeuralIntervention core.toNeuralSystem parent
    (protocol.learnedState parent) protocol.authorizedView
  parentRejectReason : succession.RejectReason
  parentRejected : succession.Rejected protocol.authorizedView.relation
    intervention.parentTrace.proposal parentRejectReason
  learnedSucceeds : succession.Succeeds protocol.authorizedView.relation
    intervention.learnedTrace.proposal
    (succession.successor protocol.authorizedView.relation
      intervention.learnedTrace.proposal)

theorem StrictFreshProbeCausality.probeCannotBelongToTraining
    {core : TransformerCore}
    {training : TransformerTrainingProcedure core}
    {protocol : FixedFreshProbeProtocol training}
    {succession : TransformerSuccession core}
    {parent : core.Weights}
    (_causality : StrictFreshProbeCausality training protocol succession parent) :
    training.InCorpus protocol.corpus protocol.probe → False :=
  protocol.fresh

theorem StrictFreshProbeCausality.boundProbeCannotBeSubstituted
    {core : TransformerCore}
    {training : TransformerTrainingProcedure core}
    {protocol : FixedFreshProbeProtocol training}
    {succession : TransformerSuccession core}
    {parent : core.Weights}
    (_causality : StrictFreshProbeCausality training protocol succession parent)
    {otherCorpus : training.Corpus}
    {otherProbe : training.Probe}
    (binding : protocol.Binds protocol.commitment otherCorpus otherProbe) :
    otherCorpus = protocol.corpus ∧ otherProbe = protocol.probe :=
  protocol.bindingUnique binding

theorem StrictFreshProbeCausality.predictionIsConsumedExactly
    {core : TransformerCore}
    {training : TransformerTrainingProcedure core}
    {protocol : FixedFreshProbeProtocol training}
    {succession : TransformerSuccession core}
    {parent : core.Weights}
    (causality : StrictFreshProbeCausality training protocol succession parent) :
    causality.intervention.learnedTrace.consumedPrediction =
      causality.intervention.learnedTrace.predicted :=
  causality.intervention.learnedTrace.consumedExact

theorem StrictFreshProbeCausality.proposalComesFromConsumedPrediction
    {core : TransformerCore}
    {training : TransformerTrainingProcedure core}
    {protocol : FixedFreshProbeProtocol training}
    {succession : TransformerSuccession core}
    {parent : core.Weights}
    (causality : StrictFreshProbeCausality training protocol succession parent) :
    causality.intervention.learnedTrace.proposal =
      core.propose protocol.authorizedView
        causality.intervention.learnedTrace.consumedPrediction :=
  causality.intervention.learnedTrace.proposalExact

namespace FreshProbeExamples

open TransformerExamples

inductive Probe : Type
  | training
  | heldOut

def trainingCorpus : List Probe :=
  [.training]

def heldOutView : TransformerAuthorizedView Bool Bool TwoCellMemory Bool :=
  { fixedView with tokens := [true], cache := true, budget := 2 }

def view : Probe → TransformerAuthorizedView Bool Bool TwoCellMemory Bool
  | .training => fixedView
  | .heldOut => heldOutView

def train : List Probe → Bool → Bool
  | [], parent => parent
  | _probe :: _remaining, parent => Bool.not parent

inductive TrainingEvidence : List Probe → Bool → Bool → Type
  | empty (parent : Bool) : TrainingEvidence [] parent parent
  | nonempty (probe : Probe) (remaining : List Probe) (parent : Bool) :
      TrainingEvidence (probe :: remaining) parent (Bool.not parent)

def trainingProcedure : TransformerTrainingProcedure core where
  Corpus := List Probe
  Probe := Probe
  InCorpus := fun corpus probe => List.Mem probe corpus
  train := train
  TrainingEvidence := TrainingEvidence
  trainingEvidence
    | [], parent => .empty parent
    | probe :: remaining, parent => .nonempty probe remaining parent
  view := view

inductive Commitment : Type
  | canonical

inductive Binds : Commitment → List Probe → Probe → Type
  | canonical : Binds .canonical [.training] .heldOut

theorem heldOut_isFresh : List.Mem .heldOut trainingCorpus → False := by
  intro membership
  nomatch membership

theorem heldOutView_ne_trainingView : heldOutView = view .training → False := by
  intro equality
  have cacheEquality := congrArg
    (fun authorized : TransformerAuthorizedView Bool Bool TwoCellMemory Bool =>
      authorized.cache) equality
  change true = false at cacheEquality
  nomatch cacheEquality

def protocol : FixedFreshProbeProtocol trainingProcedure where
  corpus := trainingCorpus
  probe := .heldOut
  Commitment := Commitment
  commitment := .canonical
  Binds := Binds
  bound := .canonical
  bindingUnique := by
    intro otherCorpus otherProbe binding
    cases binding
    exact ⟨rfl, rfl⟩
  fresh := heldOut_isFresh

def parentTrace :=
  core.toNeuralSystem.run false protocol.authorizedView

def learnedTrace :=
  core.toNeuralSystem.run (protocol.learnedState false) protocol.authorizedView

theorem predictionChanges :
    parentTrace.predicted = learnedTrace.predicted → False := by
  intro impossible
  nomatch impossible

theorem proposalChanges :
    parentTrace.proposal = learnedTrace.proposal → False := by
  intro impossible
  nomatch impossible

def intervention : NeuralIntervention core.toNeuralSystem false
    (protocol.learnedState false) protocol.authorizedView :=
  { parentTrace := parentTrace
    learnedTrace := learnedTrace
    predictionChanges := predictionChanges
    proposalChanges := proposalChanges }

def strictCausality : StrictFreshProbeCausality
    trainingProcedure protocol succession false :=
  { learning := trainingProcedure.trainingEvidence protocol.corpus false
    intervention := intervention
    parentRejectReason := .unchangedPrediction
    parentRejected := .parentFalse
    learnedSucceeds := .learnedTrue }

theorem learnedState_isTransformerLearnedWeights :
    protocol.learnedState false = TransformerDynamics.learnedWeights :=
  rfl

structure StrictFreshProbeGateCertificate where
  acquisition : StrictFreshProbeCausality
    trainingProcedure protocol succession false
  fresh : trainingProcedure.InCorpus protocol.corpus protocol.probe → False
  authorizedViewDistinct : protocol.authorizedView = view .training → False
  commitmentExact : {otherCorpus : trainingProcedure.Corpus} →
    {otherProbe : trainingProcedure.Probe} →
    protocol.Binds protocol.commitment otherCorpus otherProbe →
      otherCorpus = protocol.corpus ∧ otherProbe = protocol.probe
  predictionChanged :
    acquisition.intervention.parentTrace.predicted =
      acquisition.intervention.learnedTrace.predicted → False
  predictionConsumed :
    acquisition.intervention.learnedTrace.consumedPrediction =
      acquisition.intervention.learnedTrace.predicted
  proposalChanged :
    acquisition.intervention.parentTrace.proposal =
      acquisition.intervention.learnedTrace.proposal → False
  learnedProposalExact :
    acquisition.intervention.learnedTrace.proposal =
      core.propose protocol.authorizedView
        acquisition.intervention.learnedTrace.consumedPrediction
  learnedWeightsExact :
    protocol.learnedState false = TransformerDynamics.learnedWeights

def strictFreshProbeGateCertificate : StrictFreshProbeGateCertificate :=
  { acquisition := strictCausality
    fresh := strictCausality.probeCannotBelongToTraining
    authorizedViewDistinct := heldOutView_ne_trainingView
    commitmentExact := strictCausality.boundProbeCannotBeSubstituted
    predictionChanged := strictCausality.intervention.predictionChanges
    predictionConsumed := strictCausality.predictionIsConsumedExactly
    proposalChanged := strictCausality.intervention.proposalChanges
    learnedProposalExact := strictCausality.proposalComesFromConsumedPrediction
    learnedWeightsExact := learnedState_isTransformerLearnedWeights }

end FreshProbeExamples
end ConstitutiveAlignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveAlignment.StrictFreshProbeCausality.probeCannotBelongToTraining
#print axioms ConstitutiveAlignment.StrictFreshProbeCausality.boundProbeCannotBeSubstituted
#print axioms ConstitutiveAlignment.StrictFreshProbeCausality.predictionIsConsumedExactly
#print axioms ConstitutiveAlignment.StrictFreshProbeCausality.proposalComesFromConsumedPrediction
#print axioms ConstitutiveAlignment.FreshProbeExamples.heldOut_isFresh
#print axioms ConstitutiveAlignment.FreshProbeExamples.heldOutView_ne_trainingView
#print axioms ConstitutiveAlignment.FreshProbeExamples.strictCausality
#print axioms ConstitutiveAlignment.FreshProbeExamples.learnedState_isTransformerLearnedWeights
#print axioms ConstitutiveAlignment.FreshProbeExamples.strictFreshProbeGateCertificate
/- AXIOM_AUDIT_END -/
