import Alignment.FiniteIntrinsicRelationalSearch
import Tests.IntrinsicRelationalMediatorRegression

namespace Alignment.Tests.FiniteIntrinsicRelationalSearchRegression

open GenesisReconstruction
open GenesisReconstruction.FiniteAnchoredMatchSearch
open GenesisReconstruction.FiniteIntrinsicRelationalSearch
open IntrinsicRelationalMediatorRegression

/-- Exact transports are injective in their forward direction constructively. -/
theorem exactForward_injective
    {Source Target : Type}
    (transport : ExactTypeTransport Source Target) :
    Function.Injective transport.forward := by
  intro first second equality
  calc
    first = transport.backward (transport.forward first) :=
      (transport.forwardBackward first).symm
    _ = transport.backward (transport.forward second) :=
      congrArg transport.backward equality
    _ = second := transport.forwardBackward second

/-- Complete finite listing of the Boolean carrier. -/
def boolListing : FiniteListing Bool :=
  { values := [false, true]
    complete := by
      intro value
      cases value with
      | false => exact List.Mem.head [true]
      | true => exact List.Mem.tail false (List.Mem.head []) }

/--
Every exact Boolean self-transport has the same forward map as either identity
or swap. Thus the two candidates form a genuinely complete transport listing,
not a heuristic sample.
-/
def boolTransportListing : FiniteTransportListing Bool Bool :=
  { values := [ExactTypeTransport.reflexive Bool, swapTransport]
    complete := by
      intro transport
      cases falseImage : transport.forward false with
      | false =>
          refine
            ⟨ExactTypeTransport.reflexive Bool,
              List.Mem.head [swapTransport], ?_⟩
          intro source
          cases source with
          | false =>
              change false = transport.forward false
              exact falseImage.symm
          | true =>
              cases trueImage : transport.forward true with
              | false =>
                  have collision :
                      transport.forward false = transport.forward true := by
                    rw [falseImage, trueImage]
                  have impossible : false = true :=
                    exactForward_injective transport collision
                  cases impossible
              | true =>
                  rfl
      | true =>
          refine
            ⟨swapTransport,
              List.Mem.tail (ExactTypeTransport.reflexive Bool)
                (List.Mem.head []), ?_⟩
          intro source
          cases source with
          | false =>
              change true = transport.forward false
              exact falseImage.symm
          | true =>
              cases trueImage : transport.forward true with
              | false =>
                  rfl
              | true =>
                  have collision :
                      transport.forward false = transport.forward true := by
                    rw [falseImage, trueImage]
                  have impossible : false = true :=
                    exactForward_injective transport collision
                  cases impossible }

/-- On the symmetric relational context the first compatible transport is identity. -/
theorem symmetricFinder_returns_identity :
    findCompatibleTransport
        symmetricContext
        boolListing.values
        boolTransportListing.values =
      some (ExactTypeTransport.reflexive Bool) := by
  rfl

/-- The positive wrapper therefore constructs an intrinsic compatible alignment. -/
theorem symmetricSearch_succeeds :
    searchAlignment? symmetricContext boolListing boolTransportListing ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

/-! ## A relation pair with no intrinsic exact alignment -/

/-- A directed one-edge relation on Bool. -/
def directedRelation (source target : Bool) : Bool :=
  match source, target with
  | false, false => false
  | false, true => true
  | true, false => false
  | true, true => false

/-- Its full self-profile separates the two identities. -/
theorem directedSelfProfile_separates :
    ProfileSeparates
      (fun identity anchor : Bool => directedRelation anchor identity) := by
  intro first second agreement
  cases first <;> cases second
  · rfl
  · have impossible := agreement false
    cases impossible
  · have impossible := agreement false
    cases impossible
  · rfl

/--
Both sides are internally separating, but the symmetric equality pattern is not
isomorphic to the directed one-edge pattern.
-/
def incompatibleContext :
    IntrinsicRelationalContext Bool Bool Bool :=
  { sourceRelation := symmetricRelation
    targetRelation := directedRelation
    sourceSeparates := symmetricSelfProfile_separates
    targetSeparates := directedSelfProfile_separates }

/-- Identity fails the complete relational matrix check. -/
theorem incompatible_identity_rejected :
    preservesRelationOn
        incompatibleContext
        boolListing.values
        (ExactTypeTransport.reflexive Bool) = false := by
  rfl

/-- Swap fails as well. -/
theorem incompatible_swap_rejected :
    preservesRelationOn
        incompatibleContext
        boolListing.values
        swapTransport = false := by
  rfl

/-- Exhaustive intrinsic search therefore returns `none`. -/
theorem incompatibleFinder_returns_none :
    findCompatibleTransport
        incompatibleContext
        boolListing.values
        boolTransportListing.values = none := by
  rfl

/--
Because the transport listing is complete, the computed `none` is a
constructive refutation of every compatible exact relational alignment.
-/
theorem incompatibleContext_has_no_alignment
    (alignment : IntrinsicCompatibleExactAlignment incompatibleContext) : False :=
  noAlignment_of_findCompatibleTransport_none
    incompatibleContext
    boolListing
    boolTransportListing
    incompatibleFinder_returns_none
    alignment

end Alignment.Tests.FiniteIntrinsicRelationalSearchRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.FiniteIntrinsicRelationalSearchRegression.exactForward_injective
#print axioms Alignment.Tests.FiniteIntrinsicRelationalSearchRegression.boolListing
#print axioms Alignment.Tests.FiniteIntrinsicRelationalSearchRegression.boolTransportListing
#print axioms Alignment.Tests.FiniteIntrinsicRelationalSearchRegression.symmetricFinder_returns_identity
#print axioms Alignment.Tests.FiniteIntrinsicRelationalSearchRegression.symmetricSearch_succeeds
#print axioms Alignment.Tests.FiniteIntrinsicRelationalSearchRegression.directedRelation
#print axioms Alignment.Tests.FiniteIntrinsicRelationalSearchRegression.directedSelfProfile_separates
#print axioms Alignment.Tests.FiniteIntrinsicRelationalSearchRegression.incompatibleContext
#print axioms Alignment.Tests.FiniteIntrinsicRelationalSearchRegression.incompatible_identity_rejected
#print axioms Alignment.Tests.FiniteIntrinsicRelationalSearchRegression.incompatible_swap_rejected
#print axioms Alignment.Tests.FiniteIntrinsicRelationalSearchRegression.incompatibleFinder_returns_none
#print axioms Alignment.Tests.FiniteIntrinsicRelationalSearchRegression.incompatibleContext_has_no_alignment
/- AXIOM_AUDIT_END -/
