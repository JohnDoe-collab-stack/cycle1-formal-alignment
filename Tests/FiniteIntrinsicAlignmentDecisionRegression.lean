import Alignment.CertifiedFiniteIntrinsicAlignmentDecision
import Tests.FiniteIntrinsicRelationalSearchRegression

namespace Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression

open GenesisReconstruction
open GenesisReconstruction.FiniteAnchoredMatchSearch
open GenesisReconstruction.FiniteIntrinsicAlignmentDecision
open FiniteIntrinsicRelationalSearchRegression
open IntrinsicRelationalMediatorRegression

/-!
This regression exercises the end-to-end finite intrinsic decision layer without
supplying `Anchor`, a mediator, a source/target pairing, an exact transport, or a
`FiniteTransportListing`.

The primary API is now the certified semantic decision: either an exact
compatible alignment is constructed, or all such alignments are constructively
refuted.  The optional search view is tested only as a derived projection.
-/

/--
The symmetric Boolean context has an intrinsic exact alignment, so exhaustive
search generated from the two local Boolean listings cannot return `none`.
-/
theorem symmetric_generatedFinder_succeeds :
    findPassingCandidate
        symmetricContext
        boolListing
        boolListing
        (generatedPairs boolListing boolListing) ≠ none :=
  generatedFinder_ne_none_of_alignment
    symmetricContext boolListing boolListing identityAlignment

/-- The certified decision reports the positive semantic branch. -/
theorem symmetric_certifiedDecision_is_aligned :
    (decideAlignmentFromListings
      symmetricContext boolListing boolListing).isAligned = true :=
  decideAlignmentFromListings_isAligned_of_alignment
    symmetricContext boolListing boolListing identityAlignment

/-- The optional convenience view therefore exposes an alignment. -/
theorem symmetric_certifiedSearch_succeeds :
    certifiedSearchAlignmentFromListings?
        symmetricContext boolListing boolListing ≠ none := by
  unfold certifiedSearchAlignmentFromListings?
  cases decision :
      decideAlignmentFromListings
        symmetricContext boolListing boolListing with
  | aligned alignment =>
      intro impossible
      cases impossible
  | impossible refute =>
      exact (refute identityAlignment).elim

/-! ## Direct intrinsic incompatibility, with no transport enumeration -/

/-- Every target diagonal entry of the directed relation is false. -/
theorem directedRelation_diagonal_false
    (value : Bool) :
    directedRelation value value = false := by
  cases value <;> rfl

/--
The incompatible context has no exact intrinsic alignment for a local reason:
the source diagonal observation at `false` is `true`, whereas every target
diagonal observation is `false`. No case split over candidate transports is
needed.
-/
theorem incompatibleContext_no_alignment_direct
    (alignment : IntrinsicCompatibleExactAlignment incompatibleContext) : False := by
  have diagonalTrue :
      directedRelation
          (alignment.transport.forward false)
          (alignment.transport.forward false) = true := by
    simpa [incompatibleContext, symmetricRelation] using
      (alignment.preservesRelation false false)
  have diagonalFalse :
      directedRelation
          (alignment.transport.forward false)
          (alignment.transport.forward false) = false :=
    directedRelation_diagonal_false (alignment.transport.forward false)
  have impossible : false = true := diagonalFalse.symm.trans diagonalTrue
  cases impossible

/--
Consequently the exhaustive raw-function finder must return `none`: a returned
candidate would reconstruct the exact alignment just refuted above.
-/
theorem incompatible_generatedFinder_returns_none :
    findPassingCandidate
        incompatibleContext
        boolListing
        boolListing
        (generatedPairs boolListing boolListing) = none := by
  generalize resultEquation :
      findPassingCandidate
        incompatibleContext
        boolListing
        boolListing
        (generatedPairs boolListing boolListing) = result
  cases result with
  | none =>
      exact resultEquation
  | some candidate =>
      have checked :
          candidatePasses
              incompatibleContext boolListing boolListing candidate = true :=
        findPassingCandidate_sound
          incompatibleContext
          boolListing
          boolListing
          (generatedPairs boolListing boolListing)
          candidate
          resultEquation
      have alignment : IntrinsicCompatibleExactAlignment incompatibleContext :=
        alignmentOfPassingCandidate
          incompatibleContext
          boolListing
          boolListing
          candidate
          checked
      exact (incompatibleContext_no_alignment_direct alignment).elim

/-- The certified decision reports the constructive impossibility branch. -/
theorem incompatible_certifiedDecision_is_impossible :
    (decideAlignmentFromListings
      incompatibleContext boolListing boolListing).isAligned = false :=
  decideAlignmentFromListings_isAligned_false_of_refutation
    incompatibleContext
    boolListing
    boolListing
    incompatibleContext_no_alignment_direct

/-- The optional convenience view forgets that certificate and returns `none`. -/
theorem incompatible_certifiedSearch_returns_none :
    certifiedSearchAlignmentFromListings?
        incompatibleContext boolListing boolListing = none := by
  unfold certifiedSearchAlignmentFromListings?
  cases decision :
      decideAlignmentFromListings
        incompatibleContext boolListing boolListing with
  | aligned alignment =>
      exact (incompatibleContext_no_alignment_direct alignment).elim
  | impossible refute =>
      rfl

/--
The generated raw `none` remains independently sufficient to refute every
intrinsic compatible exact alignment. No candidate transport family occurs in
this proof.
-/
theorem incompatibleContext_has_no_alignment_from_local_listings
    (alignment : IntrinsicCompatibleExactAlignment incompatibleContext) : False :=
  noAlignment_of_generatedFinder_none
    incompatibleContext
    boolListing
    boolListing
    incompatible_generatedFinder_returns_none
    alignment

/-! ## Empty-carrier edge cases -/

/-- Complete local listing of the empty carrier. -/
def emptyListing : FiniteListing Empty :=
  { values := []
    complete := by
      intro identity
      exact nomatch identity }

/-- Complete local listing of the singleton carrier. -/
def unitListing : FiniteListing Unit :=
  { values := [()]
    complete := by
      intro identity
      cases identity
      exact List.Mem.head [] }

/-- Vacuous intrinsic context on two empty carriers. -/
def emptyEmptyContext : IntrinsicRelationalContext Empty Empty Bool :=
  { sourceRelation := fun first _ => nomatch first
    targetRelation := fun first _ => nomatch first
    sourceSeparates := by
      intro first _ _
      exact nomatch first
    targetSeparates := by
      intro first _ _
      exact nomatch first }

/-- The two empty carriers admit the unique exact transport. -/
def emptyEmptyAlignment : IntrinsicCompatibleExactAlignment emptyEmptyContext :=
  { transport :=
      { forward := fun identity => nomatch identity
        backward := fun identity => nomatch identity
        forwardBackward := by
          intro identity
          exact nomatch identity
        backwardForward := by
          intro identity
          exact nomatch identity }
    preservesRelation := by
      intro first _
      exact nomatch first }

/-- Exhaustive intrinsic decision correctly accepts the empty/empty case. -/
theorem emptyEmpty_certifiedDecision_is_aligned :
    (decideAlignmentFromListings
      emptyEmptyContext emptyListing emptyListing).isAligned = true :=
  decideAlignmentFromListings_isAligned_of_alignment
    emptyEmptyContext emptyListing emptyListing emptyEmptyAlignment

/-- Intrinsic context from one source identity to an empty target carrier. -/
def unitEmptyContext : IntrinsicRelationalContext Unit Empty Bool :=
  { sourceRelation := fun _ _ => true
    targetRelation := fun first _ => nomatch first
    sourceSeparates := by
      intro first second _
      cases first
      cases second
      rfl
    targetSeparates := by
      intro first _ _
      exact nomatch first }

/-- No exact transport can map a nonempty carrier into an empty one. -/
theorem unitEmpty_no_alignment
    (alignment : IntrinsicCompatibleExactAlignment unitEmptyContext) : False :=
  nomatch alignment.transport.forward ()

/-- The certified decision detects the nonempty/empty cardinality obstruction. -/
theorem unitEmpty_certifiedDecision_is_impossible :
    (decideAlignmentFromListings
      unitEmptyContext unitListing emptyListing).isAligned = false :=
  decideAlignmentFromListings_isAligned_false_of_refutation
    unitEmptyContext unitListing emptyListing unitEmpty_no_alignment

/-- Intrinsic context from an empty source carrier to one target identity. -/
def emptyUnitContext : IntrinsicRelationalContext Empty Unit Bool :=
  { sourceRelation := fun first _ => nomatch first
    targetRelation := fun _ _ => true
    sourceSeparates := by
      intro first _ _
      exact nomatch first
    targetSeparates := by
      intro first second _
      cases first
      cases second
      rfl }

/-- No exact transport can supply a backward map from a singleton into emptiness. -/
theorem emptyUnit_no_alignment
    (alignment : IntrinsicCompatibleExactAlignment emptyUnitContext) : False :=
  nomatch alignment.transport.backward ()

/-- The certified decision detects the empty/nonempty cardinality obstruction. -/
theorem emptyUnit_certifiedDecision_is_impossible :
    (decideAlignmentFromListings
      emptyUnitContext emptyListing unitListing).isAligned = false :=
  decideAlignmentFromListings_isAligned_false_of_refutation
    emptyUnitContext emptyListing unitListing emptyUnit_no_alignment

end Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.symmetric_generatedFinder_succeeds
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.symmetric_certifiedDecision_is_aligned
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.symmetric_certifiedSearch_succeeds
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.directedRelation_diagonal_false
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.incompatibleContext_no_alignment_direct
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.incompatible_generatedFinder_returns_none
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.incompatible_certifiedDecision_is_impossible
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.incompatible_certifiedSearch_returns_none
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.incompatibleContext_has_no_alignment_from_local_listings
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.emptyListing
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.unitListing
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.emptyEmptyContext
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.emptyEmptyAlignment
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.emptyEmpty_certifiedDecision_is_aligned
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.unitEmptyContext
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.unitEmpty_no_alignment
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.unitEmpty_certifiedDecision_is_impossible
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.emptyUnitContext
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.emptyUnit_no_alignment
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.emptyUnit_certifiedDecision_is_impossible
/- AXIOM_AUDIT_END -/
