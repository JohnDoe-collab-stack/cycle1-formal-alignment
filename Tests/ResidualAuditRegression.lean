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

end StrongPerimetralTurning.Tests.ResidualAuditRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.positive_agrees_with_stored_boundary
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.positive_agrees_with_native_path
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.weak_residual_agrees_with_consumed_turning
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.consumed_residual_has_final_label
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.consumed_residual_is_the_only_continuation_occurrence
#print axioms StrongPerimetralTurning.Tests.ResidualAuditRegression.nativeContinuationExactlyOne
/- AXIOM_AUDIT_END -/
