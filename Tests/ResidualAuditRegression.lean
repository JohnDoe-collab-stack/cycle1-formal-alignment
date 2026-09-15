import StrongPerimetralTurning

/-!
# Positive regression checks for the exported residual agreements

These checks consume the producer and the published abstract turning directly.
They are positive regressions: they do not replace the production proofs and
they do not import into the production modules.
-/

namespace StrongPerimetralTurning.Tests.ResidualAuditRegression

open StrongPerimetralTurning

theorem positive_agrees_with_stored_boundary
    (P : CircularPresentation) :
    (oneStepResidualPositive P).occurrence =
      (oneStepSegmentedBoundary P).positive.occurrence :=
  oneStepResidualPositive_agrees_with_segmentedBoundary P

theorem positive_agrees_with_native_path
    (P : CircularPresentation) :
    (oneStepResidualPositive P).occurrence =
      transportOccurrence
        (oneStepAfterPerimeter_positiveContinuation P).historyExact.symm
        (oneStepAfterPerimeter_positiveContinuation P).path.lastOccurrence :=
  rfl

theorem weak_residual_agrees_with_consumed_turning
    (P : CircularPresentation) :
    (oneStepWeakResidualOccurrence P).occurrence =
      (abstractTurningOfCircularPresentation P).uniqueResidualOccurrence.occurrence :=
  oneStepWeakResidualOccurrence_agrees_with_consumedTurning P

theorem consumed_residual_has_final_label
    (P : CircularPresentation) :
    let kernel :=
      (oneStepFaithfullyLabelledExtension P).toSegmentedResidualExtension
        |>.toResidualUniquenessKernel
    kernel.label
        (kernel.embedNew
          (abstractTurningOfCircularPresentation P).uniqueResidualOccurrence.occurrence) =
      .inr FinalRequirement.distinguished :=
  let kernel :=
    (oneStepFaithfullyLabelledExtension P).toSegmentedResidualExtension
      |>.toResidualUniquenessKernel
  (congrArg
    (fun occurrence => kernel.label (kernel.embedNew occurrence))
    (oneStepWeakResidualOccurrence_agrees_with_consumedTurning P)).symm.trans
      (oneStepWeakResidualOccurrence_label_is_final P)

theorem consumed_residual_is_the_only_continuation_occurrence
    (P : CircularPresentation)
    (other : History.Occurrence
      (oneStepFaithfullyLabelledExtension P).continuation) :
    other =
      (abstractTurningOfCircularPresentation P).uniqueResidualOccurrence.occurrence :=
  (oneStepWeakResidualOccurrence_unique P other).trans
    (oneStepWeakResidualOccurrence_agrees_with_consumedTurning P)

def nativeContinuationExactlyOne
    (P : CircularPresentation) :
    History.ExactlyOne
      (oneStepFaithfullyLabelledExtension P).continuation :=
  positiveContinuation_exactlyOne
    (oneStepFaithfullyLabelledExtension P)
    (oneStepAfterPerimeter_positiveContinuation P)

/-! ## Direct core regression

This finite separator deliberately starts at `ResidualDeterminationCore`.
The core exists on `Bool` internal roles and `Unit` historical occurrences,
while the rich completion proposition below is impossible already at its
internal-realization field.  The positive turning path therefore does not
construct a rich realization as an intermediate.
-/

abbrev AuditInternalRole := Bool
abbrev AuditOldOccurrence := Unit
abbrev AuditNewOccurrence := Unit
abbrev AuditResidualRole := Unit

def auditResidualContractible :
    SegmentedResidualRole.ContractibleRole AuditResidualRole :=
  { center := Unit.unit
    contracts := fun _ => rfl }

def auditResidualCore :
    SegmentedResidualRole.ResidualDeterminationCore
      AuditInternalRole
      AuditResidualRole
      AuditNewOccurrence
      auditResidualContractible :=
  { newLabel := fun _ => .inr Unit.unit
    newLabelInjective := by
      intro first second _
      cases first
      cases second
      rfl
    noInternalReuse := by
      intro occurrence role equality
      cases equality }

def auditCorePositive :
    SegmentedResidualRole.PositiveNewPart AuditNewOccurrence :=
  { occurrence := Unit.unit }

def auditCoreResidual :
    SegmentedResidualRole.CoreUniqueResidualOccurrence auditResidualCore :=
  SegmentedResidualRole.positiveCore_hasUniqueResidualOccurrence
    auditResidualCore auditCorePositive

example : auditCoreResidual.occurrence = Unit.unit := rfl

structure AuditRichCompatibleCompletion where
  internal :
    SegmentedResidualRole.ExactInternalRealization
      AuditInternalRole AuditOldOccurrence
  extension :
    SegmentedResidualRole.FaithfulExtension
      AuditInternalRole
      AuditResidualRole
      AuditOldOccurrence
      AuditNewOccurrence
      Unit
      internal
      auditResidualContractible
  newLabelAgrees :
    extension.label (extension.embedNew Unit.unit) =
      auditResidualCore.newLabel Unit.unit

theorem audit_noCompatibleRichCompletion :
    ¬ Nonempty AuditRichCompatibleCompletion := by
  intro completionExists
  rcases completionExists with ⟨completion⟩
  let internal := completion.internal
  have occurrencesEqual :
      internal.roleToOccurrence false =
        internal.roleToOccurrence true :=
    Subsingleton.elim _ _
  have falseRoundTrip :=
    internal.roleRoundTrip false
  have trueRoundTrip :=
    internal.roleRoundTrip true
  have falseEqualsTrue : false = true := by
    calc
      false = internal.occurrenceToRole
          (internal.roleToOccurrence false) :=
        falseRoundTrip.symm
      _ = internal.occurrenceToRole
          (internal.roleToOccurrence true) :=
        congrArg internal.occurrenceToRole occurrencesEqual
      _ = true := trueRoundTrip
  cases falseEqualsTrue

inductive AuditCarrier
  | boundary
  | continuation

inductive AuditExtension : AuditCarrier → AuditCarrier → Type
  | boundary_to_continuation : AuditExtension .boundary .continuation

def auditGenerator :
    AbstractSegmentedTurning.BoundaryGenerator
      AuditCarrier AuditExtension :=
  { boundary := .boundary
    continuation := .continuation
    generates := .boundary_to_continuation
    extensionIrreflexive := by
      intro carrier extension
      cases extension }

def auditRegime : AuditCarrier → Type
  | .boundary => Unit
  | .continuation => Empty

def auditObstructedRegime :
    AbstractSegmentedTurning.ObstructedRegime auditGenerator :=
  { Regime := auditRegime
    Interpretation := fun _ => Unit
    Attempt := fun _ => Empty
    canonicalRegime := Unit.unit
    classifyOrTotalize := by
      intro candidate regime
      cases candidate with
      | boundary => exact .inl (PLift.up rfl)
      | continuation => cases regime
    rejectTotalization := by
      intro candidate interpretation attempt
      cases attempt }

def auditCoreBoundary :
    AbstractSegmentedTurning.CoreSegmentedBoundary
      auditGenerator
      AuditInternalRole
      AuditResidualRole
      AuditNewOccurrence
      auditResidualContractible :=
  { core := auditResidualCore
    positive := auditCorePositive }

def auditCoreTurningResult :=
  AbstractSegmentedTurning.coreTurning
    auditCoreBoundary
    auditObstructedRegime

example :
    auditCoreTurningResult.uniqueResidualOccurrence.occurrence =
      auditCoreResidual.occurrence := by
  rfl

abbrev AuditContext (_ : AuditCarrier) := Unit
abbrev AuditContextualNewOccurrence
    {candidate : AuditCarrier} (_ : AuditContext candidate) := Unit

structure AuditResidualInterpretation where
  occurrence : Unit

abbrev AuditCoreBoundaryAt (candidate : AuditCarrier) :=
  AbstractSegmentedTurning.CorePositiveResidualBoundary
    auditGenerator
    AuditContext
    AuditContextualNewOccurrence
    AuditInternalRole
    AuditResidualRole
    auditResidualContractible
    candidate

def auditInterpretResidual
    {candidate : AuditCarrier}
    (boundary : AuditCoreBoundaryAt candidate)
    (unique :
      SegmentedResidualRole.CoreUniqueResidualOccurrence boundary.core) :
    AuditResidualInterpretation :=
  { occurrence := unique.occurrence }

abbrev AuditAttempt (interpretation : AuditResidualInterpretation) : Type :=
  PLift (interpretation.occurrence ≠ Unit.unit)

def auditCoupledRegime : AuditCarrier → Type
  | .boundary => Unit
  | .continuation =>
      Σ boundary : AuditCoreBoundaryAt .continuation,
        AuditAttempt
          (auditInterpretResidual
            boundary boundary.uniqueResidualOccurrence)

def auditCorePositiveBoundary :
    AbstractSegmentedTurning.CorePositiveResidualBoundary
      auditGenerator
      AuditContext
      AuditContextualNewOccurrence
      AuditInternalRole
      AuditResidualRole
      auditResidualContractible
      AuditCarrier.continuation :=
  { context := Unit.unit
    strict := .boundary_to_continuation
    core := auditResidualCore
    positive := auditCorePositive }

def auditCoreCoupled :
  AbstractSegmentedTurning.CoreCoupledObstructedRegime
      auditGenerator
      AuditContext
      AuditContextualNewOccurrence
      AuditInternalRole
      AuditResidualRole
      auditResidualContractible :=
  { Regime := auditCoupledRegime
    Interpretation := fun _ => AuditResidualInterpretation
    Attempt := AuditAttempt
    canonicalRegime := Unit.unit
    interpretResidual := auditInterpretResidual
    analyzeRegime := by
      intro candidate regime
      cases candidate with
      | boundary => exact .inl (PLift.up rfl)
      | continuation =>
          rcases regime with ⟨boundary, attempt⟩
          exact .inr ⟨boundary, attempt⟩
    rejectTotalization := by
      intro candidate interpretation attempt
      cases interpretation with
      | mk occurrence =>
          cases occurrence
          exact attempt.down rfl }

def auditCoreCoupledTurning :
    AbstractSegmentedTurning.CoreCoupledTurningConclusion auditCoreCoupled :=
  AbstractSegmentedTurning.coreCoupledTurning auditCoreCoupled

theorem auditCoupledInterpretation_uses_core_residual :
    (auditCoreCoupled.interpretResidual
      auditCorePositiveBoundary
      auditCoreResidual).occurrence =
        auditCoreResidual.occurrence := by
  rfl

theorem auditBoundaryResidual_eq_auditCoreResidual :
    auditCorePositiveBoundary.uniqueResidualOccurrence.occurrence =
      auditCoreResidual.occurrence := by
  rfl

theorem auditCoupledAttemptRejected
    (attempt : auditCoreCoupled.Attempt
      (auditCoreCoupled.interpretResidual
        auditCorePositiveBoundary
        auditCorePositiveBoundary.uniqueResidualOccurrence)) :
    False := by
  exact
    AbstractSegmentedTurning.CoreCoupledTurningConclusion.admittedPositiveBoundaryRejected
      auditCoreCoupledTurning auditCorePositiveBoundary attempt

theorem auditCoupledAttemptFromExplicitCoreRejected
    (attempt : auditCoreCoupled.Attempt
      (auditCoreCoupled.interpretResidual
        auditCorePositiveBoundary
        auditCoreResidual)) :
    False := by
  change auditCoreCoupled.Attempt
    (auditCoreCoupled.interpretResidual
      auditCorePositiveBoundary
      auditCorePositiveBoundary.uniqueResidualOccurrence) at attempt
  exact
    AbstractSegmentedTurning.CoreCoupledTurningConclusion.admittedPositiveBoundaryRejected
      auditCoreCoupledTurning auditCorePositiveBoundary attempt

end StrongPerimetralTurning.Tests.ResidualAuditRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.positive_agrees_with_stored_boundary
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.positive_agrees_with_native_path
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.weak_residual_agrees_with_consumed_turning
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.consumed_residual_has_final_label
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.consumed_residual_is_the_only_continuation_occurrence
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.nativeContinuationExactlyOne
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.auditResidualCore
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.auditCoreResidual
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.audit_noCompatibleRichCompletion
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.auditCoreTurningResult
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.auditCoreCoupled
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.auditCoreCoupledTurning
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.auditCoupledRegime
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.auditInterpretResidual
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.auditCoupledInterpretation_uses_core_residual
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.auditCoupledAttemptRejected
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.auditCoupledAttemptFromExplicitCoreRejected
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.auditBoundaryResidual_eq_auditCoreResidual
/- AXIOM_AUDIT_END -/
