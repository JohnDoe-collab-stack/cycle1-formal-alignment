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

The only finite search data are the complete local carrier listings themselves.
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

/--
For the intrinsically incompatible relation pair, exhaustive generation of all
local forward/backward functions and all intrinsic checks computes `none`.
-/
theorem incompatible_generatedFinder_returns_none :
    findPassingCandidate
        incompatibleContext
        boolListing
        boolListing
        (generatedPairs boolListing boolListing) = none := by
  rfl

/-- The public wrapper exposes the same negative decision. -/
theorem incompatible_searchFromListings_returns_none :
    searchAlignmentFromListings?
        incompatibleContext boolListing boolListing = none := by
  unfold searchAlignmentFromListings?
  rw [incompatible_generatedFinder_returns_none]

/--
The computed `none` is a constructive certificate that no intrinsic compatible
exact alignment exists. No candidate transport family is supplied anywhere in
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

end Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.symmetric_generatedFinder_succeeds
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.symmetric_searchFromListings_succeeds
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.incompatible_generatedFinder_returns_none
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.incompatible_searchFromListings_returns_none
#print axioms Alignment.Tests.FiniteIntrinsicAlignmentDecisionRegression.incompatibleContext_has_no_alignment_from_local_listings
/- AXIOM_AUDIT_END -/
