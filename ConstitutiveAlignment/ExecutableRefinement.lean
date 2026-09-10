import ConstitutiveAlignment.GovernedDynamics

set_option linter.checkUnivs false

/-!
# Refinement of the discrete executable boundary

Floating-point prediction remains an observed computation.  The exact formal
boundary begins after total discretization: it records the predicted decision,
the value actually consumed by proposition, the candidate, the independently
computed regime and norm verdicts, the diagnostic, the certificate, and the
governed effect.

Refinement means equality with the canonical discrete trace generated from the
formal transformer run.  It neither asks the neural producer to emit a proof nor
turns a numerical logit into a theorem.
-/

namespace ConstitutiveAlignment
namespace ExecutableRefinement

open TransformerExamples
open TransformerDynamics
open TransformerGovernedDynamics

inductive RuntimeDiagnostic : Type
  | outsideRegimeAndNorm

inductive RuntimeEffect : Type
  | relationIncorporated

def runtimeCandidate : Bool → ReferenceModel.Candidate :=
  proposalCandidate

def runtimeRegime : ReferenceModel.Candidate → Bool
  | .admitted => true
  | .outside => false

/- This decision is intentionally a separate definition from `runtimeRegime`. -/
def runtimeNorm : ReferenceModel.Candidate → Bool
  | .admitted => true
  | .outside => false

def runtimeDiagnostic : ReferenceModel.Candidate → Option RuntimeDiagnostic
  | .admitted => none
  | .outside => some .outsideRegimeAndNorm

def runtimeCertificate (candidate : ReferenceModel.Candidate) : Bool :=
  Bool.and (runtimeRegime candidate) (runtimeNorm candidate)

def runtimeEffect : ReferenceModel.Candidate → Option RuntimeEffect
  | .admitted => some .relationIncorporated
  | .outside => none

inductive DecidedStatus (Witness : Type) : Bool → Type
  | accepted : Witness → DecidedStatus Witness true
  | rejected : (Witness → False) → DecidedStatus Witness false

inductive CertificateStatus (candidate : ReferenceModel.Candidate) : Bool → Type
  | issued : ReferenceModel.actionExecutor.Certificate false
      (ReferenceModel.actionOfCandidate candidate) →
      CertificateStatus candidate true
  | withheld : (ReferenceModel.actionExecutor.Certificate false
      (ReferenceModel.actionOfCandidate candidate) → False) →
      CertificateStatus candidate false

inductive GovernedEffectStatus
    (candidate : ReferenceModel.Candidate) : Option RuntimeEffect → Type
  | effectuated : CertifiedEffectuation ReferenceModel.actionExecutor false
      (ReferenceModel.actionOfCandidate candidate) →
      GovernedEffectStatus candidate (some .relationIncorporated)
  | confined : (CertifiedEffectuation ReferenceModel.actionExecutor false
      (ReferenceModel.actionOfCandidate candidate) → False) →
      GovernedEffectStatus candidate none

def regimeDecision : (candidate : ReferenceModel.Candidate) →
    DecidedStatus (ReferenceModel.machine.Regime candidate)
      (runtimeRegime candidate)
  | .admitted => .accepted .admits
  | .outside => .rejected (fun admitted => nomatch admitted)

def normDecision : (candidate : ReferenceModel.Candidate) →
    DecidedStatus (ReferenceModel.machine.Norm candidate)
      (runtimeNorm candidate)
  | .admitted => .accepted .satisfied
  | .outside => .rejected (fun normative => nomatch normative)

def certificateStatus : (candidate : ReferenceModel.Candidate) →
    CertificateStatus candidate (runtimeCertificate candidate)
  | .admitted => .issued .issued
  | .outside => .withheld ReferenceModel.rejectedAction_hasNoCertificate

def governedEffectStatus : (candidate : ReferenceModel.Candidate) →
    GovernedEffectStatus candidate (runtimeEffect candidate)
  | .admitted => .effectuated ReferenceModel.admittedEffectuation
  | .outside => .confined ReferenceModel.rejectedAction_cannotBeEffectuated

theorem runtimeRejectionConfines
    (candidate : ReferenceModel.Candidate)
    (rejected : runtimeNorm candidate = false) :
    runtimeCertificate candidate = false ∧ runtimeEffect candidate = none := by
  cases candidate with
  | admitted => nomatch rejected
  | outside => exact ⟨rfl, rfl⟩

structure ExecutableTrace where
  inputRelation : Bool
  predictedDecision : Bool
  consumedDecision : Bool
  proposal : Bool
  candidate : ReferenceModel.Candidate
  regimeAdmitted : Bool
  normSatisfied : Bool
  diagnostic : Option RuntimeDiagnostic
  certificateIssued : Bool
  governedEffect : Option RuntimeEffect

def canonicalTrace
    (weights : core.Weights)
    (view : View) : ExecutableTrace :=
  let formalTrace := core.run weights view
  let proposal := formalTrace.causal.proposal
  let candidate := runtimeCandidate proposal
  { inputRelation := view.relation
    predictedDecision := formalTrace.causal.predicted
    consumedDecision := formalTrace.causal.consumedPrediction
    proposal := proposal
    candidate := candidate
    regimeAdmitted := runtimeRegime candidate
    normSatisfied := runtimeNorm candidate
    diagnostic := runtimeDiagnostic candidate
    certificateIssued := runtimeCertificate candidate
    governedEffect := runtimeEffect candidate }

/- The single equality is deliberately strongest: every primary field must be
   the field generated by the formal run, not merely observationally similar. -/
structure TraceRefinement
    (weights : core.Weights)
    (view : View)
    (executable : ExecutableTrace) : Prop where
  exact : executable = canonicalTrace weights view

theorem canonicalRefinement
    (weights : core.Weights)
    (view : View) : TraceRefinement weights view (canonicalTrace weights view) :=
  ⟨rfl⟩

theorem TraceRefinement.predictionConsumedExactly
    {weights : core.Weights}
    {view : View}
    {executable : ExecutableTrace}
    (refinement : TraceRefinement weights view executable) :
    executable.consumedDecision = executable.predictedDecision := by
  rw [refinement.exact]
  exact (core.run weights view).causal.consumedExact

theorem TraceRefinement.proposalConsumedExactly
    {weights : core.Weights}
    {view : View}
    {executable : ExecutableTrace}
    (refinement : TraceRefinement weights view executable) :
    executable.proposal =
      core.propose view executable.consumedDecision := by
  rw [refinement.exact]
  exact (core.run weights view).causal.proposalExact

theorem TraceRefinement.candidateDecodedExactly
    {weights : core.Weights}
    {view : View}
    {executable : ExecutableTrace}
  (refinement : TraceRefinement weights view executable) :
    executable.candidate = runtimeCandidate executable.proposal := by
  rw [refinement.exact]
  unfold canonicalTrace
  rfl

def TraceRefinement.regimeStatus
    {weights : core.Weights}
    {view : View}
    {executable : ExecutableTrace}
    (refinement : TraceRefinement weights view executable) :
    DecidedStatus (ReferenceModel.machine.Regime executable.candidate)
      executable.regimeAdmitted := by
  rw [refinement.exact]
  exact regimeDecision (canonicalTrace weights view).candidate

def TraceRefinement.normStatus
    {weights : core.Weights}
    {view : View}
    {executable : ExecutableTrace}
    (refinement : TraceRefinement weights view executable) :
    DecidedStatus (ReferenceModel.machine.Norm executable.candidate)
      executable.normSatisfied := by
  rw [refinement.exact]
  exact normDecision (canonicalTrace weights view).candidate

def TraceRefinement.certificateStatus
    {weights : core.Weights}
    {view : View}
    {executable : ExecutableTrace}
  (refinement : TraceRefinement weights view executable) :
    CertificateStatus executable.candidate executable.certificateIssued := by
  rw [refinement.exact]
  exact ExecutableRefinement.certificateStatus
    (canonicalTrace weights view).candidate

def TraceRefinement.governedEffectStatus
    {weights : core.Weights}
    {view : View}
    {executable : ExecutableTrace}
  (refinement : TraceRefinement weights view executable) :
    GovernedEffectStatus executable.candidate executable.governedEffect := by
  rw [refinement.exact]
  exact ExecutableRefinement.governedEffectStatus
    (canonicalTrace weights view).candidate

theorem TraceRefinement.rejectedHasNoGovernedEffect
    {weights : core.Weights}
    {view : View}
    {executable : ExecutableTrace}
    (refinement : TraceRefinement weights view executable)
  (rejected : executable.normSatisfied = false) :
    executable.certificateIssued = false ∧ executable.governedEffect = none := by
  rw [refinement.exact] at rejected ⊢
  exact runtimeRejectionConfines
    (canonicalTrace weights view).candidate rejected

def executableAt (depth : Nat) : ExecutableTrace :=
  canonicalTrace learnedWeights (viewAt depth)

theorem refinementAt (depth : Nat) :
    TraceRefinement learnedWeights (viewAt depth) (executableAt depth) :=
  canonicalRefinement learnedWeights (viewAt depth)

theorem nextExecutableConsumesPreviousProposal (depth : Nat) :
    (executableAt (Nat.succ depth)).inputRelation =
      (executableAt depth).proposal :=
  proposalIsNextConsumedRelation depth

structure LinkedTraceRefinement
    (firstView secondView : View)
    (first second : ExecutableTrace) : Prop where
  firstRefines : TraceRefinement learnedWeights firstView first
  secondRefines : TraceRefinement learnedWeights secondView second
  relationConsumed : second.inputRelation = first.proposal

theorem linkedAt (depth : Nat) : LinkedTraceRefinement
    (viewAt depth) (viewAt (Nat.succ depth))
    (executableAt depth) (executableAt (Nat.succ depth)) :=
  { firstRefines := refinementAt depth
    secondRefines := refinementAt (Nat.succ depth)
    relationConsumed := nextExecutableConsumesPreviousProposal depth }

/-! ## Positive and negative boundary cases -/

def parentExecutable : ExecutableTrace :=
  canonicalTrace false fixedView

theorem parentRefinement : TraceRefinement false fixedView parentExecutable :=
  canonicalRefinement false fixedView

def learnedExecutable : ExecutableTrace :=
  canonicalTrace learnedWeights fixedView

theorem learnedRefinement :
    TraceRefinement learnedWeights fixedView learnedExecutable :=
  canonicalRefinement learnedWeights fixedView

def rewrittenParentCandidate : ExecutableTrace :=
  { parentExecutable with candidate := .admitted }

theorem rewrittenParentCandidate_hasNoRefinement :
    TraceRefinement false fixedView rewrittenParentCandidate → False := by
  intro refinement
  have candidateEquality :=
    congrArg ExecutableTrace.candidate refinement.exact
  nomatch candidateEquality

def forgedParentEffect : ExecutableTrace :=
  { parentExecutable with governedEffect := some .relationIncorporated }

theorem forgedParentEffect_hasNoRefinement :
    TraceRefinement false fixedView forgedParentEffect → False := by
  intro refinement
  have effectEquality :=
    congrArg ExecutableTrace.governedEffect refinement.exact
  nomatch effectEquality

def missingIntercycleLink : ExecutableTrace :=
  canonicalTrace learnedWeights fixedView

theorem missingIntercycleLink_cannotRefineSecondCycle :
    TraceRefinement learnedWeights (viewAt 1) missingIntercycleLink → False := by
  intro refinement
  have relationEquality :=
    congrArg ExecutableTrace.inputRelation refinement.exact
  nomatch relationEquality

def executableAudit : DeferredAudit ExecutableTrace Unit where
  inspect := fun _sealed => ()

def sealedParent : SealedTrace ExecutableTrace :=
  ⟨parentExecutable⟩

theorem executableAudit_preservesParent :
    (runDeferredAudit executableAudit sealedParent).1 = sealedParent :=
  deferredAudit_preservesPrimaryTrace executableAudit sealedParent

structure GateMCertificate where
  arbitraryDepthRefinement : (depth : Nat) →
    TraceRefinement learnedWeights (viewAt depth) (executableAt depth)
  linkedDepths : (depth : Nat) → LinkedTraceRefinement
    (viewAt depth) (viewAt (Nat.succ depth))
    (executableAt depth) (executableAt (Nat.succ depth))
  exactPredictionConsumption :
    parentExecutable.consumedDecision = parentExecutable.predictedDecision
  exactCandidateDecoding :
    parentExecutable.candidate = runtimeCandidate parentExecutable.proposal
  indexedCertificates : (depth : Nat) →
    CertificateStatus (executableAt depth).candidate
      (executableAt depth).certificateIssued
  indexedEffects : (depth : Nat) →
    GovernedEffectStatus (executableAt depth).candidate
      (executableAt depth).governedEffect
  rejectedEffectConfined :
    parentExecutable.certificateIssued = false ∧
      parentExecutable.governedEffect = none
  rewrittenCandidateRejected :
    TraceRefinement false fixedView rewrittenParentCandidate → False
  forgedEffectRejected :
    TraceRefinement false fixedView forgedParentEffect → False
  missingLinkRejected :
    TraceRefinement learnedWeights (viewAt 1) missingIntercycleLink → False
  deferredAuditSilent :
    (runDeferredAudit executableAudit sealedParent).1 = sealedParent

def gateMCertificate : GateMCertificate :=
  { arbitraryDepthRefinement := refinementAt
    linkedDepths := linkedAt
    exactPredictionConsumption :=
      parentRefinement.predictionConsumedExactly
    exactCandidateDecoding := parentRefinement.candidateDecodedExactly
    indexedCertificates := fun depth => (refinementAt depth).certificateStatus
    indexedEffects := fun depth => (refinementAt depth).governedEffectStatus
    rejectedEffectConfined :=
      parentRefinement.rejectedHasNoGovernedEffect rfl
    rewrittenCandidateRejected := rewrittenParentCandidate_hasNoRefinement
    forgedEffectRejected := forgedParentEffect_hasNoRefinement
    missingLinkRejected := missingIntercycleLink_cannotRefineSecondCycle
    deferredAuditSilent := executableAudit_preservesParent }

end ExecutableRefinement
end ConstitutiveAlignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveAlignment.ExecutableRefinement.canonicalRefinement
#print axioms ConstitutiveAlignment.ExecutableRefinement.TraceRefinement.predictionConsumedExactly
#print axioms ConstitutiveAlignment.ExecutableRefinement.TraceRefinement.proposalConsumedExactly
#print axioms ConstitutiveAlignment.ExecutableRefinement.TraceRefinement.candidateDecodedExactly
#print axioms ConstitutiveAlignment.ExecutableRefinement.TraceRefinement.regimeStatus
#print axioms ConstitutiveAlignment.ExecutableRefinement.TraceRefinement.normStatus
#print axioms ConstitutiveAlignment.ExecutableRefinement.TraceRefinement.certificateStatus
#print axioms ConstitutiveAlignment.ExecutableRefinement.TraceRefinement.governedEffectStatus
#print axioms ConstitutiveAlignment.ExecutableRefinement.TraceRefinement.rejectedHasNoGovernedEffect
#print axioms ConstitutiveAlignment.ExecutableRefinement.refinementAt
#print axioms ConstitutiveAlignment.ExecutableRefinement.nextExecutableConsumesPreviousProposal
#print axioms ConstitutiveAlignment.ExecutableRefinement.linkedAt
#print axioms ConstitutiveAlignment.ExecutableRefinement.rewrittenParentCandidate_hasNoRefinement
#print axioms ConstitutiveAlignment.ExecutableRefinement.forgedParentEffect_hasNoRefinement
#print axioms ConstitutiveAlignment.ExecutableRefinement.missingIntercycleLink_cannotRefineSecondCycle
#print axioms ConstitutiveAlignment.ExecutableRefinement.executableAudit_preservesParent
#print axioms ConstitutiveAlignment.ExecutableRefinement.gateMCertificate
/- AXIOM_AUDIT_END -/
