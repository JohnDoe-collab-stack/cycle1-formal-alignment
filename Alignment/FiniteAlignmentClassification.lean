import Alignment.FiniteAnchoredMatchDecision

/-!
# Executable classification of finite structural alignment

The finite search and decision layers separate forward structural totality,
reverse structural totality, and exact bidirectional alignment. This module
packages the four possible outcomes of the two executable checks as a
witness-carrying value.

The classification is deliberately relative to an `AnchoredRelationContext`
and to complete finite listings. The weakest negative case therefore states
only that no total anchored matching exists in either direction. It does not
claim that the two carriers are unrelated in every possible sense.
-/

namespace Alignment
namespace GenesisReconstruction
namespace FiniteAlignmentClassification

open FiniteAnchoredMatchSearch
open FiniteAnchoredMatchDecision

universe uSource uTarget uAnchor uValue

/-- Positive certificate for a finite context that embeds backward but not exactly. -/
structure BackwardOnlyCertificate
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    (context : AnchoredRelationContext Source Target Anchor Value) where
  matching : BackwardAnchoredMatching context
  refutesExact : CompatibleExactAlignment context → False

/-- Construct a backward-only certificate from the two directional checks. -/
def backwardOnlyCertificateOfChecks
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (forwardChecked : forwardTotalCheck context anchors sources targets = false)
    (backwardChecked : backwardTotalCheck context anchors sources targets = true) :
    BackwardOnlyCertificate context :=
  { matching :=
      backwardMatchingOfCheck
        context anchors sources targets backwardChecked
    refutesExact :=
      noCompatibleExactAlignment_of_forwardTotalCheck_false
        context anchors sources targets forwardChecked }

/--
Certificate that neither directional total anchored matching exists in the
finite context.
-/
structure NoDirectionalMatchingCertificate
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    (context : AnchoredRelationContext Source Target Anchor Value) where
  refutesForward : ForwardAnchoredMatching context → False
  refutesBackward : BackwardAnchoredMatching context → False
  refutesExact : CompatibleExactAlignment context → False

/-- Construct the fully negative directional certificate from two failed checks. -/
theorem noDirectionalMatchingCertificateOfChecks
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (forwardChecked : forwardTotalCheck context anchors sources targets = false)
    (backwardChecked : backwardTotalCheck context anchors sources targets = false) :
    NoDirectionalMatchingCertificate context :=
  { refutesForward :=
      noForwardMatching_of_forwardTotalCheck_false
        context anchors sources targets forwardChecked
    refutesBackward :=
      noBackwardMatching_of_backwardTotalCheck_false
        context anchors sources targets backwardChecked
    refutesExact :=
      noCompatibleExactAlignment_of_forwardTotalCheck_false
        context anchors sources targets forwardChecked }

/-- Four constructive regimes determined by the two finite directional checks. -/
inductive Classification
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    (context : AnchoredRelationContext Source Target Anchor Value) where
  | exact : TotalAnchoredMatching context → Classification context
  | forwardOnly : ForwardOnlyCertificate context → Classification context
  | backwardOnly : BackwardOnlyCertificate context → Classification context
  | noDirectionalMatching :
      NoDirectionalMatchingCertificate context → Classification context

/-- A proof-free tag exposing the computed regime. -/
inductive Kind where
  | exact
  | forwardOnly
  | backwardOnly
  | noDirectionalMatching

/-- Forget witnesses and retain only the four-way executable regime tag. -/
def Classification.kind
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value} :
    Classification context → Kind
  | .exact _ => .exact
  | .forwardOnly _ => .forwardOnly
  | .backwardOnly _ => .backwardOnly
  | .noDirectionalMatching _ => .noDirectionalMatching

/--
Compute the finite alignment regime directly from relational observations and
complete finite listings.
-/
def classify
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    [DecidableEq Value]
    (context : AnchoredRelationContext Source Target Anchor Value)
    (anchors : FiniteListing Anchor)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target) :
    Classification context :=
  match forwardChecked : forwardTotalCheck context anchors sources targets with
  | true =>
      match backwardChecked : backwardTotalCheck context anchors sources targets with
      | true =>
          .exact
            (totalMatchingOfChecks
              context anchors sources targets forwardChecked backwardChecked)
      | false =>
          .forwardOnly
            (forwardOnlyCertificateOfChecks
              context anchors sources targets forwardChecked backwardChecked)
  | false =>
      match backwardChecked : backwardTotalCheck context anchors sources targets with
      | true =>
          .backwardOnly
            (backwardOnlyCertificateOfChecks
              context anchors sources targets forwardChecked backwardChecked)
      | false =>
          .noDirectionalMatching
            (noDirectionalMatchingCertificateOfChecks
              context anchors sources targets forwardChecked backwardChecked)

/-- Recover a forward structural matching exactly in the regimes that contain one. -/
def Classification.forwardMatching?
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value} :
    Classification context → Option (ForwardAnchoredMatching context)
  | .exact matching => some matching.toForwardMatching
  | .forwardOnly certificate => some certificate.matching
  | .backwardOnly _ => none
  | .noDirectionalMatching _ => none

/-- Recover a backward structural matching exactly in the regimes that contain one. -/
def Classification.backwardMatching?
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value} :
    Classification context → Option (BackwardAnchoredMatching context)
  | .exact matching => some matching.toBackwardMatching
  | .forwardOnly _ => none
  | .backwardOnly certificate => some certificate.matching
  | .noDirectionalMatching _ => none

/-- Recover compatible exact alignment only from the exact regime. -/
def Classification.compatibleExactAlignment?
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value} :
    Classification context → Option (CompatibleExactAlignment context)
  | .exact matching => some matching.toCompatibleExactAlignment
  | .forwardOnly _ => none
  | .backwardOnly _ => none
  | .noDirectionalMatching _ => none

/-- Recover the exact initial type transport only from the exact regime. -/
def Classification.exactTransport?
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value} :
    Classification context → Option (ExactTypeTransport Source Target)
  | .exact matching => some matching.toExactTransport
  | .forwardOnly _ => none
  | .backwardOnly _ => none
  | .noDirectionalMatching _ => none

/-- Recover exact transport at any requested natural-number genesis depth only from the exact regime. -/
def Classification.finiteTransport?
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (classification : Classification context)
    (depth : Nat) :
    Option
      (ExactTypeTransport
        (IteratedCarrier Source depth)
        (IteratedCarrier Target depth)) :=
  match classification with
  | .exact matching => some (matching.finiteTransport depth)
  | .forwardOnly _ => none
  | .backwardOnly _ => none
  | .noDirectionalMatching _ => none

/-- Every non-exact classified regime carries a constructive exact-alignment refutation. -/
theorem Classification.refutesExact_of_nonexact
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (classification : Classification context)
    (nonExact : classification.kind ≠ Kind.exact)
    (alignment : CompatibleExactAlignment context) : False := by
  cases classification with
  | exact matching =>
      exact False.elim (nonExact rfl)
  | forwardOnly certificate =>
      exact certificate.refutesExact alignment
  | backwardOnly certificate =>
      exact certificate.refutesExact alignment
  | noDirectionalMatching certificate =>
      exact certificate.refutesExact alignment

end FiniteAlignmentClassification
end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.FiniteAlignmentClassification.BackwardOnlyCertificate
#print axioms Alignment.GenesisReconstruction.FiniteAlignmentClassification.backwardOnlyCertificateOfChecks
#print axioms Alignment.GenesisReconstruction.FiniteAlignmentClassification.NoDirectionalMatchingCertificate
#print axioms Alignment.GenesisReconstruction.FiniteAlignmentClassification.noDirectionalMatchingCertificateOfChecks
#print axioms Alignment.GenesisReconstruction.FiniteAlignmentClassification.Classification
#print axioms Alignment.GenesisReconstruction.FiniteAlignmentClassification.Kind
#print axioms Alignment.GenesisReconstruction.FiniteAlignmentClassification.Classification.kind
#print axioms Alignment.GenesisReconstruction.FiniteAlignmentClassification.classify
#print axioms Alignment.GenesisReconstruction.FiniteAlignmentClassification.Classification.forwardMatching?
#print axioms Alignment.GenesisReconstruction.FiniteAlignmentClassification.Classification.backwardMatching?
#print axioms Alignment.GenesisReconstruction.FiniteAlignmentClassification.Classification.compatibleExactAlignment?
#print axioms Alignment.GenesisReconstruction.FiniteAlignmentClassification.Classification.exactTransport?
#print axioms Alignment.GenesisReconstruction.FiniteAlignmentClassification.Classification.finiteTransport?
#print axioms Alignment.GenesisReconstruction.FiniteAlignmentClassification.Classification.refutesExact_of_nonexact
/- AXIOM_AUDIT_END -/
