import ConstitutiveAlignment.TransformerRealization

set_option linter.checkUnivs false

/-!
# Finite transformer dynamics

This module composes the finite hard-attention realization with the generic
succession, causal-memory, and normative-confinement contracts.  One uniform
operator feeds each produced proposal into the relation field consumed by the
next run.  A dedicated ablation omits that incorporation and changes the second
proposal.

The result is finite and constructive.  It does not claim trained-network or
unbounded-horizon autonomy.
-/

namespace ConstitutiveAlignment
namespace TransformerDynamics

open TransformerExamples

abbrev View :=
  TransformerAuthorizedView Bool Bool TwoCellMemory Bool

def learnedWeights : core.Weights :=
  core.learn false

def run (view : View) : TransformerPrimaryTrace core learnedWeights view :=
  core.run learnedWeights view

def incorporateProposal (view : View) : View :=
  withRelation view (run view).causal.proposal

def transition : UniformTransition View where
  Step := fun source target => PLift (target = incorporateProposal source)
  next := incorporateProposal
  step := fun _source => ⟨rfl⟩

def twoLinkedTransformerCycles : LinkedTwoCycles transition fixedView :=
  transition.twoCycles fixedView

def firstTrace : TransformerPrimaryTrace core learnedWeights fixedView :=
  run fixedView

def secondView : View :=
  transition.next fixedView

def secondTrace : TransformerPrimaryTrace core learnedWeights secondView :=
  run secondView

theorem firstProposal_isSecondConsumedRelation :
    secondView.relation = firstTrace.causal.proposal :=
  rfl

theorem secondRun_consumesFirstProposal :
    secondTrace.causal.proposal =
      core.propose secondView secondTrace.causal.consumedPrediction :=
  secondTrace.causal.proposalExact

/- This view is the dedicated intercycle ablation: the first proposal is not
   incorporated, while tokens, cache, memory, budget, core, and weights remain
   unchanged. -/
def ablatedSecondView : View :=
  fixedView

def ablatedSecondTrace :
    TransformerPrimaryTrace core learnedWeights ablatedSecondView :=
  run ablatedSecondView

theorem intercycleAblation_changesSecondPrediction :
    secondTrace.causal.predicted =
      ablatedSecondTrace.causal.predicted → False := by
  intro impossible
  nomatch impossible

theorem intercycleAblation_changesSecondProposal :
    secondTrace.causal.proposal =
      ablatedSecondTrace.causal.proposal → False := by
  intro impossible
  nomatch impossible

/-! ## Memory relative to the two attention queries -/

def attentionFuture : FutureQuestions TwoCellMemory where
  Question := Bool
  Answer := fun _query => Bool
  behaviour := fun memory query => memory.attend query

def attentionMemory : MemoryEncoding TwoCellMemory where
  Memory := Bool × Bool
  encode := fun memory => (memory.left, memory.right)

theorem attentionMemoryExact :
    ExactCausalMemory attentionFuture attentionMemory where
  sound := by
    intro leftMemory rightMemory sameMemory query
    cases leftMemory with
    | mk leftLeft leftRight leftFocus =>
        cases rightMemory with
        | mk rightLeft rightRight rightFocus =>
            cases sameMemory
            cases query <;> rfl
  complete := by
    intro leftMemory rightMemory equivalent
    apply Prod.ext
    · exact equivalent false
    · exact equivalent true

theorem incorporation_preservesAttentionMemory (view : View) :
    attentionMemory.encode (incorporateProposal view).memory =
      attentionMemory.encode view.memory :=
  rfl

/-! ## Relative normative break and confinement -/

structure RelativeHallucinationWitness where
  candidate : ReferenceModel.machine.Candidate
  construction : StrongPerimetralTurning.History
    ReferenceModel.machine.Step ReferenceModel.machine.root
      (ReferenceModel.machine.endpoint candidate)
  faithful : ReferenceModel.machine.Faithful candidate
  realization : InjectiveMap
    (ReferenceModel.machine.Occurrence candidate)
    (ReferenceModel.machine.RealizedOccurrence candidate)
  realizationExact :
    realization = ReferenceModel.machine.occurrenceRealization faithful
  normRefuted : ReferenceModel.machine.Norm candidate → False
  retainedProposal :
    proposalCandidate parentTrace.causal.proposal = candidate

def parentRelativeHallucination : RelativeHallucinationWitness :=
  { candidate := .outside
    construction := ReferenceModel.outsideHistory
    faithful := .outsideTrace
    realization :=
      ReferenceModel.machine.occurrenceRealization (.outsideTrace)
    realizationExact := rfl
    normRefuted := fun normWitness => nomatch normWitness
    retainedProposal := rfl }

theorem parentRelativeHallucination_cannotBeEffectuated :
    CertifiedEffectuation ReferenceModel.actionExecutor false
      (ReferenceModel.actionOfCandidate parentRelativeHallucination.candidate) →
        False :=
  ReferenceModel.rejectedAction_cannotBeEffectuated

structure FiniteGateJCertificate where
  formationFailure :
    FormationFailure ReferenceModel.FormationRequest ReferenceModel.Formed
  operationalExit : OperationalExit ReferenceModel.machine
  normativeFailure : NormativeFailure ReferenceModel.machine
  relativeHallucination : RelativeHallucinationWitness
  operationalExitCandidate :
    operationalExit.candidate = relativeHallucination.candidate
  normativeFailureCandidate :
    normativeFailure.candidate = relativeHallucination.candidate
  retainedRejectedProposal :
    parentTrace.causal.elaboration =
      ElaborationOutcome.rejected ⟨0, ErrorReason.outsideRegime⟩
  governedEffectBlocked :
    CertifiedEffectuation ReferenceModel.actionExecutor false
      (ReferenceModel.actionOfCandidate relativeHallucination.candidate) → False
  memory : ExactCausalMemory attentionFuture attentionMemory
  linkedCycles : LinkedTwoCycles transition fixedView
  firstProposalConsumed :
    secondView.relation = firstTrace.causal.proposal
  ablationChangesPrediction :
    secondTrace.causal.predicted =
      ablatedSecondTrace.causal.predicted → False
  ablationChangesProposal :
    secondTrace.causal.proposal =
      ablatedSecondTrace.causal.proposal → False

def finiteGateJCertificate : FiniteGateJCertificate :=
  { formationFailure := ReferenceModel.formationFailure
    operationalExit := ReferenceModel.operationalExit
    normativeFailure := ReferenceModel.normativeFailure
    relativeHallucination := parentRelativeHallucination
    operationalExitCandidate := rfl
    normativeFailureCandidate := rfl
    retainedRejectedProposal := rejectedParentProposal_isPreserved
    governedEffectBlocked :=
      parentRelativeHallucination_cannotBeEffectuated
    memory := attentionMemoryExact
    linkedCycles := twoLinkedTransformerCycles
    firstProposalConsumed := firstProposal_isSecondConsumedRelation
    ablationChangesPrediction := intercycleAblation_changesSecondPrediction
    ablationChangesProposal := intercycleAblation_changesSecondProposal }

end TransformerDynamics
end ConstitutiveAlignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveAlignment.TransformerDynamics.transition
#print axioms ConstitutiveAlignment.TransformerDynamics.twoLinkedTransformerCycles
#print axioms ConstitutiveAlignment.TransformerDynamics.firstProposal_isSecondConsumedRelation
#print axioms ConstitutiveAlignment.TransformerDynamics.secondRun_consumesFirstProposal
#print axioms ConstitutiveAlignment.TransformerDynamics.intercycleAblation_changesSecondPrediction
#print axioms ConstitutiveAlignment.TransformerDynamics.intercycleAblation_changesSecondProposal
#print axioms ConstitutiveAlignment.TransformerDynamics.attentionMemoryExact
#print axioms ConstitutiveAlignment.TransformerDynamics.incorporation_preservesAttentionMemory
#print axioms ConstitutiveAlignment.TransformerDynamics.parentRelativeHallucination
#print axioms ConstitutiveAlignment.TransformerDynamics.parentRelativeHallucination_cannotBeEffectuated
#print axioms ConstitutiveAlignment.TransformerDynamics.finiteGateJCertificate
/- AXIOM_AUDIT_END -/
