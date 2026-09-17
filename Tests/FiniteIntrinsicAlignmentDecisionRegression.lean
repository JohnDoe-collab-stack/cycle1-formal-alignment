import Alignment.FiniteIntrinsicAlignmentDecision
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

The only finite search data passed to the new decision procedure are the
complete local carrier listings themselves.
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

/-- The public positive wrapper also succeeds without a supplied transport list. -/
theorem symmetric_searchFromListings_succeeds :
    searchAlignmentFromListings?
        symmetricContext boolListing boolListing ≠ none := by
  unfold searchAlignmentFromListings?
  cases found :
      findPassingCandidate
        symmetricContext
        boolListing
        boolListing
        (generatedPairs boolListing boolListing) with
  | none =>
      exact (symmetric_generatedFinder_succeeds found).elim
  | some candidate =>
      intro impossible
      cases impossible

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

/-- The public wrapper exposes the same negative decision. -/
theorem incompatible_searchFromListings_returns_none :
    searchAlignmentFromListings?
        incompatibleContext boolListing boolListing = none := by
  unfold searchAlignmentFromListings?
  rw [incompatible_generatedFinder_returns_none]

/--
The generated `none` is a constructive certificate that no intrinsic compatible
exact alignment exists. No candidate transport family occurs in this proof.
-/
theorem incompatibleContext_has_no_alignment_from_local_listings
    (alignment : IntrinsicCompatibleExactAlignment incompatibleContext) : False :=
  noAlignment_of_generatedFinder_none
    incompatibleContext
    boolListing
    boolListing
    incompatible_generatedFinder_returns_none
    alignment

end Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.symmetric_generatedFinder_succeeds
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.symmetric_searchFromListings_succeeds
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.directedRelation_diagonal_false
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.incompatibleContext_no_alignment_direct
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.incompatible_generatedFinder_returns_none
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.incompatible_searchFromListings_returns_none
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.incompatibleContext_has_no_alignment_from_local_listings
/- AXIOM_AUDIT_END -/
