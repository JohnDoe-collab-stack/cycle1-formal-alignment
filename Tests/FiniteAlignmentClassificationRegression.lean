import Alignment.FiniteAlignmentClassification

namespace Alignment.Tests.FiniteAlignmentClassificationRegression

open GenesisReconstruction
open GenesisReconstruction.FiniteAnchoredMatchSearch
open GenesisReconstruction.FiniteAnchoredMatchDecision
open GenesisReconstruction.FiniteAlignmentClassification

inductive WideSource
  | matched
  | extra

/-- The source side has one identity whose anchored profile has no target counterpart. -/
def wideSourceRelation (_source target : WideSource) : Bool :=
  match target with
  | .matched => false
  | .extra => true

/-- The one-point target has only the `false` anchored profile. -/
def unitTargetRelation (_source _target : Unit) : Bool :=
  false

def wideSourceAnchor : Unit → WideSource :=
  fun _ => .matched

def unitTargetAnchor : Unit → Unit :=
  fun _ => ()

theorem wideSourceProfile_separates :
    ProfileSeparates
      (fun identity anchor =>
        wideSourceRelation (wideSourceAnchor anchor) identity) := by
  intro first second agreement
  cases first <;> cases second
  · rfl
  · have impossible := agreement ()
    cases impossible
  · have impossible := agreement ()
    cases impossible
  · rfl

theorem unitTargetProfile_separates :
    ProfileSeparates
      (fun identity anchor =>
        unitTargetRelation (unitTargetAnchor anchor) identity) := by
  intro first second _
  cases first
  cases second
  rfl

def backwardOnlyContext :
    AnchoredRelationContext WideSource Unit Unit Bool :=
  { sourceRelation := wideSourceRelation
    targetRelation := unitTargetRelation
    sourceAnchor := wideSourceAnchor
    targetAnchor := unitTargetAnchor
    sourceSeparates := wideSourceProfile_separates
    targetSeparates := unitTargetProfile_separates }

def unitListing : FiniteListing Unit :=
  { values := [()]
    complete := by
      intro value
      cases value
      exact List.Mem.head [] }

def wideSourceListing : FiniteListing WideSource :=
  { values := [WideSource.matched, WideSource.extra]
    complete := by
      intro value
      cases value with
      | matched =>
          exact List.Mem.head [WideSource.extra]
      | extra =>
          exact List.Mem.tail WideSource.matched (List.Mem.head []) }

/-- The extra source identity makes forward structural totality fail. -/
theorem backwardOnly_forward_check_fails :
    forwardTotalCheck
      backwardOnlyContext unitListing wideSourceListing unitListing = false := by
  rfl

/-- The one target identity still has a source counterpart. -/
theorem backwardOnly_backward_check_succeeds :
    backwardTotalCheck
      backwardOnlyContext unitListing wideSourceListing unitListing = true := by
  rfl

/-- The four-way classifier computes the backward-only regime. -/
def backwardOnlyClassification : Classification backwardOnlyContext :=
  classify backwardOnlyContext unitListing wideSourceListing unitListing

theorem backwardOnly_classification_kind :
    backwardOnlyClassification.kind = Kind.backwardOnly := by
  rfl

/-- The backward-only regime retains the reverse structural injection. -/
theorem backwardOnly_has_backward_matching :
    backwardOnlyClassification.backwardMatching? ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

/-- The backward-only regime exposes no exact transport. -/
theorem backwardOnly_has_no_exact_transport :
    backwardOnlyClassification.exactTransport? = none := by
  rfl

theorem backwardOnly_nonexact :
    backwardOnlyClassification.kind ≠ Kind.exact := by
  intro impossible
  cases impossible

/-- The classification itself refutes compatible exact alignment. -/
theorem backwardOnly_refutes_exact
    (alignment : CompatibleExactAlignment backwardOnlyContext) : False :=
  backwardOnlyClassification.refutesExact_of_nonexact
    backwardOnly_nonexact alignment

/-- A one-point source profile fixed to `false`. -/
def incompatibleSourceRelation (_source _target : Unit) : Bool :=
  false

/-- A one-point target profile fixed to `true`. -/
def incompatibleTargetRelation (_source _target : Unit) : Bool :=
  true

theorem incompatibleSourceProfile_separates :
    ProfileSeparates
      (fun identity anchor =>
        incompatibleSourceRelation (unitTargetAnchor anchor) identity) := by
  intro first second _
  cases first
  cases second
  rfl

theorem incompatibleTargetProfile_separates :
    ProfileSeparates
      (fun identity anchor =>
        incompatibleTargetRelation (unitTargetAnchor anchor) identity) := by
  intro first second _
  cases first
  cases second
  rfl

def noDirectionalContext :
    AnchoredRelationContext Unit Unit Unit Bool :=
  { sourceRelation := incompatibleSourceRelation
    targetRelation := incompatibleTargetRelation
    sourceAnchor := unitTargetAnchor
    targetAnchor := unitTargetAnchor
    sourceSeparates := incompatibleSourceProfile_separates
    targetSeparates := incompatibleTargetProfile_separates }

/-- No source identity has a target with the same anchored profile. -/
theorem noDirectional_forward_check_fails :
    forwardTotalCheck
      noDirectionalContext unitListing unitListing unitListing = false := by
  rfl

/-- No target identity has a source with the same anchored profile either. -/
theorem noDirectional_backward_check_fails :
    backwardTotalCheck
      noDirectionalContext unitListing unitListing unitListing = false := by
  rfl

/-- The classifier computes the weakest negative directional regime. -/
def noDirectionalClassification : Classification noDirectionalContext :=
  classify noDirectionalContext unitListing unitListing unitListing

theorem noDirectional_classification_kind :
    noDirectionalClassification.kind = Kind.noDirectionalMatching := by
  rfl

/-- No forward total matching is exposed by the classified value. -/
theorem noDirectional_has_no_forward_matching :
    noDirectionalClassification.forwardMatching? = none := by
  rfl

/-- No reverse total matching is exposed by the classified value. -/
theorem noDirectional_has_no_backward_matching :
    noDirectionalClassification.backwardMatching? = none := by
  rfl

/-- No exact transport is exposed by the classified value. -/
theorem noDirectional_has_no_exact_transport :
    noDirectionalClassification.exactTransport? = none := by
  rfl

theorem noDirectional_nonexact :
    noDirectionalClassification.kind ≠ Kind.exact := by
  intro impossible
  cases impossible

/-- Even the weakest negative directional regime constructively refutes exact alignment. -/
theorem noDirectional_refutes_exact
    (alignment : CompatibleExactAlignment noDirectionalContext) : False :=
  noDirectionalClassification.refutesExact_of_nonexact
    noDirectional_nonexact alignment

end Alignment.Tests.FiniteAlignmentClassificationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.backwardOnlyContext
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.backwardOnly_forward_check_fails
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.backwardOnly_backward_check_succeeds
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.backwardOnlyClassification
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.backwardOnly_classification_kind
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.backwardOnly_has_backward_matching
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.backwardOnly_has_no_exact_transport
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.backwardOnly_nonexact
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.backwardOnly_refutes_exact
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.noDirectionalContext
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.noDirectional_forward_check_fails
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.noDirectional_backward_check_fails
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.noDirectionalClassification
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.noDirectional_classification_kind
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.noDirectional_has_no_forward_matching
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.noDirectional_has_no_backward_matching
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.noDirectional_has_no_exact_transport
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.noDirectional_nonexact
#print axioms Alignment.Tests.FiniteAlignmentClassificationRegression.noDirectional_refutes_exact
/- AXIOM_AUDIT_END -/
