import ConstitutiveAlignment.LearningCausality
import ConstitutiveAlignment.CausalMemory
import ConstitutiveAlignment.NormativeFailure
import ConstitutiveAlignment.ReflectiveMachine

set_option linter.checkUnivs false

/-!
# Finite reference architecture

This non-neural model integrates the generic contracts before any transformer
claim is attempted.  It has nontrivial proof-relevant histories, an autonomous
norm adequate to its regime, a faithful operational exit, future-relative
memory, certified and rejected actions, linked cycles, one-step learning
causality, and reflective non-closure.
-/

namespace ConstitutiveAlignment
namespace ReferenceModel

open Cycle2.DiagonalizationKernel

inductive Step : Bool → Bool → Type
  | rise : Step false true
  | return : Step true false

inductive Candidate : Type
  | admitted
  | outside

def endpoint : Candidate → Bool
  | .admitted => true
  | .outside => false

def admittedHistory :
    StrongPerimetralTurning.History Step false true :=
  .extend .root .rise

def outsideHistory :
    StrongPerimetralTurning.History Step false false :=
  .extend admittedHistory .return

def history : (candidate : Candidate) →
    StrongPerimetralTurning.History Step false (endpoint candidate)
  | .admitted => admittedHistory
  | .outside => outsideHistory

inductive Regime : Candidate → Type
  | admits : Regime .admitted

/- The norm is a separately declared family, not an alias of `Regime`. -/
inductive Norm : Candidate → Type
  | satisfied : Norm .admitted

inductive Faithful : Candidate → Type
  | admittedTrace : Faithful .admitted
  | outsideTrace : Faithful .outside

def machine : ConstitutiveMachine where
  State := Bool
  Step := Step
  root := false
  Candidate := Candidate
  endpoint := endpoint
  history := history
  Faithful := Faithful
  Regime := Regime
  Norm := Norm
  RealizedOccurrence := fun candidate =>
    StrongPerimetralTurning.History.Occurrence (history candidate)
  occurrenceRealization := fun _faithful =>
    { toFun := fun occurrence => occurrence
      injective := by
        intro firstOccurrence secondOccurrence equality
        exact equality }

def adequacy : MachineAdequacy machine where
  sound
    | .admitted, .admits => .satisfied
  complete
    | .admitted, .satisfied => .admits

def operationalExit : OperationalExit machine :=
  { candidate := .outside
    faithful := .outsideTrace
    inadmissible := fun regimeWitness => nomatch regimeWitness }

def normativeFailure : NormativeFailure machine :=
  operationalExit.toNormativeFailure adequacy

inductive FormationRequest : Type
  | wellFormed
  | malformed

inductive Formed : FormationRequest → Type
  | accepted : Formed .wellFormed

def formationFailure : FormationFailure FormationRequest Formed where
  request := .malformed
  rejectsFormation := fun formed => nomatch formed

/-! ## Local governed action layer -/

inductive ActionNature : Type
  | incorporate
  | inspect

inductive ActionTarget : Type
  | currentState
  | externalState

inductive ActionScope : Type
  | oneCycle
  | persistent

inductive ActionEffector : Type
  | commit
  | observe

def actionSignature : ActionSignature where
  Nature := ActionNature
  Target := ActionTarget
  Parameters := Candidate
  Context := Bool
  Scope := ActionScope
  Effector := ActionEffector

def actionOfCandidate (candidate : Candidate) :
    ConstitutiveAction actionSignature where
  nature := .incorporate
  target := .currentState
  parameters := candidate
  declaredContext := false
  scope := .oneCycle
  requestedEffector := .commit

def admittedAction : ConstitutiveAction actionSignature :=
  actionOfCandidate .admitted

def rejectedAction : ConstitutiveAction actionSignature :=
  actionOfCandidate .outside

inductive ActionAdmission :
    Bool → ConstitutiveAction actionSignature → Type
  | learnedCandidate : ActionAdmission false admittedAction

/- The action norm is declared separately from operational admission. -/
inductive ActionNorm :
    Bool → ConstitutiveAction actionSignature → Type
  | learnedCandidate : ActionNorm false admittedAction

inductive ActionCertificate :
    Bool → ConstitutiveAction actionSignature → Type
  | issued : ActionCertificate false admittedAction

inductive ActionEffect :
    Bool → ConstitutiveAction actionSignature → Type
  | incorporated : ActionEffect false admittedAction

def actionExecutor : NormativeExecutor actionSignature where
  Admission := ActionAdmission
  Norm := ActionNorm
  Certificate := ActionCertificate
  certificateAdmits
    | .issued => .learnedCandidate
  admissionSound
    | .learnedCandidate => .learnedCandidate
  Effect := ActionEffect
  perform
    | .issued => .incorporated

def admittedEffectuation :
    CertifiedEffectuation actionExecutor false admittedAction :=
  actionExecutor.effectuate .issued

theorem rejectedAction_hasNoCertificate :
    actionExecutor.Certificate false rejectedAction → False := by
  intro certificate
  nomatch certificate

theorem rejectedAction_cannotBeEffectuated :
    CertifiedEffectuation actionExecutor false rejectedAction → False :=
  noEffectuation_withoutCertificate rejectedAction_hasNoCertificate

def outsideLastRole :
    StrongPerimetralTurning.History.Occurrence outsideHistory :=
  .last

def outsideEarlierRole :
    StrongPerimetralTurning.History.Occurrence outsideHistory :=
  .earlier .last

def superficialReading
    (_occurrence :
      StrongPerimetralTurning.History.Occurrence outsideHistory) : Unit :=
  ()

theorem sameSuperficialReading :
    superficialReading outsideLastRole =
      superficialReading outsideEarlierRole :=
  rfl

def formationReading :
    StrongPerimetralTurning.History.Occurrence outsideHistory → Bool
  | .last => true
  | .earlier _prior => false

theorem distinctFormationReading :
    formationReading outsideLastRole =
      formationReading outsideEarlierRole → False := by
  intro impossible
  nomatch impossible

def occurrenceFuture : FutureQuestions
    (StrongPerimetralTurning.History.Occurrence outsideHistory) where
  Question := Unit
  Answer := fun _question => Bool
  behaviour := fun occurrence _question => formationReading occurrence

def occurrenceMemory : MemoryEncoding
    (StrongPerimetralTurning.History.Occurrence outsideHistory) where
  Memory := Bool
  encode := formationReading

theorem occurrenceMemoryExact :
    ExactCausalMemory occurrenceFuture occurrenceMemory where
  sound := by
    intro firstOccurrence secondOccurrence sameMemory _question
    exact sameMemory
  complete := by
    intro firstOccurrence secondOccurrence equivalent
    exact equivalent ()

/-! ## Local parent–learned causal pair -/

inductive PredictionProblem : Type
  | continuation
  | control

inductive ReferenceLearningEvidence :
    PredictionProblem → Bool → Bool → Type
  | falseToTrue (problem : PredictionProblem) :
      ReferenceLearningEvidence problem false true
  | trueToFalse (problem : PredictionProblem) :
      ReferenceLearningEvidence problem true false

def predictedCandidate : Bool → PredictionProblem → Candidate
  | false, .continuation => .outside
  | true, .continuation => .admitted
  | false, .control => .admitted
  | true, .control => .outside

inductive CausalRejectReason : Type
  | outsideRegime

inductive CausalRejected : Bool → Candidate → CausalRejectReason → Type
  | outsideAtRoot : CausalRejected false .outside .outsideRegime

inductive CausalSucceeds : Bool → Candidate → Bool → Type
  | admittedFromRoot : CausalSucceeds false .admitted true

def causalSystem : LearningCausalSystem where
  Problem := PredictionProblem
  PredictiveState := Bool
  Constitution := Bool
  Randomness := Bool
  Prediction := Candidate
  Proposal := Candidate
  learn := fun _problem state => Bool.not state
  LearningEvidence := ReferenceLearningEvidence
  learningEvidence := by
    intro problem state
    cases state
    · exact .falseToTrue problem
    · exact .trueToFalse problem
  predict := predictedCandidate
  propose := fun _problem _constitution _randomness prediction => prediction
  RejectReason := CausalRejectReason
  Rejected := CausalRejected
  successorState := fun _constitution proposal => endpoint proposal
  Succeeds := CausalSucceeds

def causalIntervention : InterventionCase causalSystem where
  problem := .continuation
  constitution := false
  randomness := false
  parentPredictiveState := false

theorem causalPredictionChanges :
    causalSystem.predict causalIntervention.parentPredictiveState
        causalIntervention.problem =
      causalSystem.predict causalIntervention.learnedPredictiveState
        causalIntervention.problem → False := by
  intro impossible
  nomatch impossible

theorem causalProposalChanges :
    (exactConsumedProposal causalSystem causalIntervention
        causalIntervention.parentPredictiveState).candidate =
      (exactConsumedProposal causalSystem causalIntervention
        causalIntervention.learnedPredictiveState).candidate → False := by
  intro impossible
  nomatch impossible

def oneStepCausality :
    OneStepLearningCausality causalSystem causalIntervention :=
  buildOneStepLearningCausality causalSystem causalIntervention
    causalPredictionChanges
    causalProposalChanges
    .outsideRegime
    .outsideAtRoot
    .admittedFromRoot

def learnedProposalAdmission :
    machine.Regime oneStepCausality.learnedProposal.candidate :=
  .admits

def learnedProposalNorm :
    machine.Norm oneStepCausality.learnedProposal.candidate :=
  adequacy.sound _ learnedProposalAdmission

def learnedProposalFaithful :
    machine.Faithful oneStepCausality.learnedProposal.candidate :=
  .admittedTrace

def parentProposalFaithful :
    machine.Faithful oneStepCausality.parentProposal.candidate :=
  .outsideTrace

theorem parentProposal_isOutside :
    oneStepCausality.parentProposal.candidate = .outside :=
  rfl

theorem parentProposal_isOperationalExitCandidate :
    oneStepCausality.parentProposal.candidate = operationalExit.candidate :=
  rfl

theorem parentProposal_isNormativeFailureCandidate :
    oneStepCausality.parentProposal.candidate = normativeFailure.candidate :=
  rfl

theorem learnedProposal_isAdmitted :
    oneStepCausality.learnedProposal.candidate = .admitted :=
  rfl

theorem learnedProposal_determinesAdmittedAction :
    actionOfCandidate oneStepCausality.learnedProposal.candidate =
      admittedAction :=
  rfl

theorem parentProposal_determinesRejectedAction :
    actionOfCandidate oneStepCausality.parentProposal.candidate =
      rejectedAction :=
  rfl

/- The same Bool state carrier admits a uniform linked transition and an exact
   autonomous memory update. -/
def stateFuture : FutureQuestions Bool where
  Question := Unit
  Answer := fun _question => Bool
  behaviour := fun state _question => state

def stateMemory : MemoryEncoding Bool where
  Memory := Bool
  encode := fun state => state

theorem stateMemoryExact : ExactCausalMemory stateFuture stateMemory where
  sound := fun sameMemory _question => sameMemory
  complete := fun equivalent => equivalent ()

def stateMemoryUpdate :
    AutonomousMemoryUpdate stateMemory Bool.not where
  update := Bool.not
  commutes := fun _state => rfl

def transition : UniformTransition Bool where
  Step := fun source target => PLift (target = Bool.not source)
  next := Bool.not
  step := fun _state => ⟨rfl⟩

def twoLinkedCycles : LinkedTwoCycles transition false :=
  transition.twoCycles false

theorem learnedSuccessor_isFirstCycleOutput :
    causalSystem.successorState causalIntervention.constitution
        oneStepCausality.learnedProposal.candidate =
      transition.next false :=
  rfl

theorem firstCycle_reconfiguresSecondMemory :
    stateMemory.encode (transition.next false) =
      stateMemoryUpdate.update (stateMemory.encode false) :=
  rfl

theorem secondCycle_consumesReconfiguredMemory :
    stateMemory.encode (iterateState transition 2 false) =
      stateMemoryUpdate.update
        (stateMemory.encode (iterateState transition 1 false)) :=
  rfl

def reflectiveDecode : Bool → Candidate
  | false => .admitted
  | true => .outside

def reflectiveEval : Bool → Bool → Prop
  | false, false => True
  | false, true => False
  | true, _input => False

def reflectiveView : ReflectiveMachineStatusView machine Bool where
  decode := reflectiveDecode
  eval := reflectiveEval
  program := false
  representsRegime := by
    intro input
    cases input
    · constructor
      · intro _holds
        exact ⟨.admits⟩
      · intro _inhabited
        exact True.intro
    · constructor
      · intro impossible
        exact False.elim impossible
      · intro inhabited
        obtain ⟨regimeWitness⟩ := inhabited
        nomatch regimeWitness

theorem representedRegime_andNorm_withDiagonalOutside :
    Represents reflectiveView.eval reflectiveView.program
        (CodedMachineRegimeStatus machine reflectiveView.decode) ∧
      Represents reflectiveView.eval reflectiveView.program
        (CodedMachineNormStatus machine reflectiveView.decode) ∧
      ¬ InternallyRepresentable reflectiveView.eval
        (diagonalStatus reflectiveView.eval) :=
  exactMachineStatusRepresentation_hasDiagonalOutside adequacy reflectiveView

def distinctExits :
    OperationalAndRepresentationalExit machine reflectiveView :=
  combineDistinctExits reflectiveView operationalExit

structure ArchitectureCertificate where
  regimeNormAdequacy : MachineAdequacy machine
  malformed : FormationFailure FormationRequest Formed
  exit : OperationalExit machine
  failure : NormativeFailure machine
  parentIsExit :
    oneStepCausality.parentProposal.candidate = exit.candidate
  parentIsNormativeFailure :
    oneStepCausality.parentProposal.candidate = failure.candidate
  sameReading :
    superficialReading outsideLastRole =
      superficialReading outsideEarlierRole
  differentFormation :
    formationReading outsideLastRole =
      formationReading outsideEarlierRole → False
  occurrenceMemory : ExactCausalMemory occurrenceFuture occurrenceMemory
  memory : ExactCausalMemory stateFuture stateMemory
  memoryUpdate : AutonomousMemoryUpdate stateMemory Bool.not
  admittedEffect : CertifiedEffectuation
    actionExecutor false admittedAction
  rejectedActionBlocked :
    CertifiedEffectuation actionExecutor false rejectedAction → False
  oneStepCausality : OneStepLearningCausality
    causalSystem causalIntervention
  learnedCandidateAdmitted :
    machine.Regime oneStepCausality.learnedProposal.candidate
  learnedCandidateNormative :
    machine.Norm oneStepCausality.learnedProposal.candidate
  learnedCandidateFaithful :
    machine.Faithful oneStepCausality.learnedProposal.candidate
  parentCandidateFaithful :
    machine.Faithful oneStepCausality.parentProposal.candidate
  learnedActionExact :
    actionOfCandidate oneStepCausality.learnedProposal.candidate =
      admittedAction
  parentActionExact :
    actionOfCandidate oneStepCausality.parentProposal.candidate =
      rejectedAction
  learnedStateIsFirstCycleOutput :
    causalSystem.successorState causalIntervention.constitution
        oneStepCausality.learnedProposal.candidate =
      transition.next false
  linkedCycles : LinkedTwoCycles transition false
  firstCycleReconfiguresMemory :
    stateMemory.encode (transition.next false) =
      memoryUpdate.update (stateMemory.encode false)
  secondCycleConsumesReconfiguredMemory :
    stateMemory.encode (iterateState transition 2 false) =
      memoryUpdate.update
        (stateMemory.encode (iterateState transition 1 false))
  reflection : ReflectiveMachineStatusView machine Bool
  exactStatusWithDiagonalOutside :
    Represents reflection.eval reflection.program
        (CodedMachineRegimeStatus machine reflection.decode) ∧
      Represents reflection.eval reflection.program
        (CodedMachineNormStatus machine reflection.decode) ∧
      ¬ InternallyRepresentable reflection.eval
        (diagonalStatus reflection.eval)
  operationalAndRepresentationalExit :
    OperationalAndRepresentationalExit machine reflection

def architectureCertificate : ArchitectureCertificate :=
  { regimeNormAdequacy := adequacy
    malformed := formationFailure
    exit := operationalExit
    failure := normativeFailure
    parentIsExit := parentProposal_isOperationalExitCandidate
    parentIsNormativeFailure := parentProposal_isNormativeFailureCandidate
    sameReading := sameSuperficialReading
    differentFormation := distinctFormationReading
    occurrenceMemory := occurrenceMemoryExact
    memory := stateMemoryExact
    memoryUpdate := stateMemoryUpdate
    admittedEffect := admittedEffectuation
    rejectedActionBlocked := rejectedAction_cannotBeEffectuated
    oneStepCausality := oneStepCausality
    learnedCandidateAdmitted := learnedProposalAdmission
    learnedCandidateNormative := learnedProposalNorm
    learnedCandidateFaithful := learnedProposalFaithful
    parentCandidateFaithful := parentProposalFaithful
    learnedActionExact := learnedProposal_determinesAdmittedAction
    parentActionExact := parentProposal_determinesRejectedAction
    learnedStateIsFirstCycleOutput := learnedSuccessor_isFirstCycleOutput
    linkedCycles := twoLinkedCycles
    firstCycleReconfiguresMemory := firstCycle_reconfiguresSecondMemory
    secondCycleConsumesReconfiguredMemory :=
      secondCycle_consumesReconfiguredMemory
    reflection := reflectiveView
    exactStatusWithDiagonalOutside :=
      representedRegime_andNorm_withDiagonalOutside
    operationalAndRepresentationalExit := distinctExits }

end ReferenceModel
end ConstitutiveAlignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveAlignment.ReferenceModel.adequacy
#print axioms ConstitutiveAlignment.ReferenceModel.operationalExit
#print axioms ConstitutiveAlignment.ReferenceModel.normativeFailure
#print axioms ConstitutiveAlignment.ReferenceModel.formationFailure
#print axioms ConstitutiveAlignment.ReferenceModel.admittedEffectuation
#print axioms ConstitutiveAlignment.ReferenceModel.rejectedAction_cannotBeEffectuated
#print axioms ConstitutiveAlignment.ReferenceModel.distinctFormationReading
#print axioms ConstitutiveAlignment.ReferenceModel.occurrenceMemoryExact
#print axioms ConstitutiveAlignment.ReferenceModel.oneStepCausality
#print axioms ConstitutiveAlignment.ReferenceModel.parentProposal_isOperationalExitCandidate
#print axioms ConstitutiveAlignment.ReferenceModel.parentProposal_isNormativeFailureCandidate
#print axioms ConstitutiveAlignment.ReferenceModel.learnedProposalAdmission
#print axioms ConstitutiveAlignment.ReferenceModel.learnedProposalNorm
#print axioms ConstitutiveAlignment.ReferenceModel.learnedProposalFaithful
#print axioms ConstitutiveAlignment.ReferenceModel.parentProposalFaithful
#print axioms ConstitutiveAlignment.ReferenceModel.learnedProposal_determinesAdmittedAction
#print axioms ConstitutiveAlignment.ReferenceModel.parentProposal_determinesRejectedAction
#print axioms ConstitutiveAlignment.ReferenceModel.stateMemoryExact
#print axioms ConstitutiveAlignment.ReferenceModel.stateMemoryUpdate
#print axioms ConstitutiveAlignment.ReferenceModel.twoLinkedCycles
#print axioms ConstitutiveAlignment.ReferenceModel.learnedSuccessor_isFirstCycleOutput
#print axioms ConstitutiveAlignment.ReferenceModel.firstCycle_reconfiguresSecondMemory
#print axioms ConstitutiveAlignment.ReferenceModel.secondCycle_consumesReconfiguredMemory
#print axioms ConstitutiveAlignment.ReferenceModel.reflectiveView
#print axioms ConstitutiveAlignment.ReferenceModel.representedRegime_andNorm_withDiagonalOutside
#print axioms ConstitutiveAlignment.ReferenceModel.architectureCertificate
/- AXIOM_AUDIT_END -/
