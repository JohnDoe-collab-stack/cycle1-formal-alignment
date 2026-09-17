import Alignment.FiniteIntrinsicAlignmentDecision

/-!
# Certified finite intrinsic alignment decision

The raw finite intrinsic search already computes enough information to do more
than return an `Option`: a successful candidate reconstructs an intrinsic exact
alignment, while an exhausted search constructively refutes every such
alignment.

This module makes that stronger result the public semantic object.  The
negative branch is therefore not represented by information loss (`none`), but
by an explicit refutation certificate.  An optional alignment remains available
only as a derived convenience view.
-/

namespace Alignment
namespace GenesisReconstruction
namespace FiniteIntrinsicAlignmentDecision

open FiniteAnchoredMatchSearch

universe uSource uTarget uValue

/--
A total finite intrinsic decision: either an exact compatible alignment has been
constructed, or every such alignment is constructively refuted.
-/
inductive AlignmentDecision
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    (context : IntrinsicRelationalContext Source Target Value) : Type _ where
  | aligned :
      IntrinsicCompatibleExactAlignment context →
      AlignmentDecision context
  | impossible :
      (IntrinsicCompatibleExactAlignment context → False) →
      AlignmentDecision context

namespace AlignmentDecision

/-- Forget the negative certificate and retain only a possible alignment. -/
def alignment?
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value} :
    AlignmentDecision context → Option (IntrinsicCompatibleExactAlignment context)
  | .aligned alignment => some alignment
  | .impossible _ => none

/-- A small executable view of which semantic branch was obtained. -/
def isAligned
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value} :
    AlignmentDecision context → Bool
  | .aligned _ => true
  | .impossible _ => false

end AlignmentDecision

/--
End-to-end certified decision from complete local carrier listings alone.

No common anchor, mediator, cross-system pairing, exact transport, or supplied
transport family occurs in the input.  The raw function enumeration is internal
to the decision procedure.
-/
def decideAlignmentFromListings
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target) : AlignmentDecision context :=
  match found :
      findPassingCandidate
        context sources targets (generatedPairs sources targets) with
  | none =>
      .impossible
        (noAlignment_of_generatedFinder_none
          context sources targets found)
  | some candidate =>
      .aligned
        (alignmentOfPassingCandidate
          context sources targets candidate
          (findPassingCandidate_sound
            context sources targets (generatedPairs sources targets)
            candidate found))

/--
If an intrinsic exact alignment really exists, the certified finite decision
cannot land in its refutation branch.
-/
theorem decideAlignmentFromListings_isAligned_of_alignment
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (alignment : IntrinsicCompatibleExactAlignment context) :
    (decideAlignmentFromListings context sources targets).isAligned = true := by
  unfold decideAlignmentFromListings AlignmentDecision.isAligned
  cases found :
      findPassingCandidate
        context sources targets (generatedPairs sources targets) with
  | none =>
      exact
        (generatedFinder_ne_none_of_alignment
          context sources targets alignment found).elim
  | some candidate =>
      rfl

/--
Conversely, an independently proved impossibility forces the certified decision
to land in its refutation branch.
-/
theorem decideAlignmentFromListings_isAligned_false_of_refutation
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (refute : IntrinsicCompatibleExactAlignment context → False) :
    (decideAlignmentFromListings context sources targets).isAligned = false := by
  unfold decideAlignmentFromListings AlignmentDecision.isAligned
  cases found :
      findPassingCandidate
        context sources targets (generatedPairs sources targets) with
  | none =>
      rfl
  | some candidate =>
      have checked :
          candidatePasses context sources targets candidate = true :=
        findPassingCandidate_sound
          context sources targets (generatedPairs sources targets)
          candidate found
      have alignment : IntrinsicCompatibleExactAlignment context :=
        alignmentOfPassingCandidate
          context sources targets candidate checked
      exact (refute alignment).elim

/-- The old optional shape is retained only as a derived convenience view. -/
def certifiedSearchAlignmentFromListings?
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target) :
    Option (IntrinsicCompatibleExactAlignment context) :=
  (decideAlignmentFromListings context sources targets).alignment?

end FiniteIntrinsicAlignmentDecision
end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.AlignmentDecision
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.AlignmentDecision.alignment?
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.AlignmentDecision.isAligned
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.decideAlignmentFromListings
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.decideAlignmentFromListings_isAligned_of_alignment
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.decideAlignmentFromListings_isAligned_false_of_refutation
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.certifiedSearchAlignmentFromListings?
/- AXIOM_AUDIT_END -/
