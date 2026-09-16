import StrongPerimetralTurning.IteratedConstitutivePersistence
import Examples.ConcreteContinuation.LoggedAlgebra
import Examples.Alignment.IteratedReadout

open Alignment

/-!
# Independent regression checks for dynamic alignment

The naturality proof below is deliberately redérived from `indexedSpoke`,
`extend`, and the two inverse laws.  It does not call the published
`extend_transport_natural` theorem.  The final counterexample uses a genuine
depth-one-to-depth-two extension and a bijective permutation of the two fresh
identities at depth two.
-/

namespace StrongPerimetralTurning.Tests.DynamicAlignmentRegression

open StrongPerimetralTurning
open StrongPerimetralTurning.Example
open StrongPerimetralTurning.IteratedConstitutivePersistence
open StrongPerimetralTurning.Examples.ConcreteContinuation.LoggedAlgebra
open StrongPerimetralTurning.Examples.Alignment.IteratedReadout

theorem independently_rederived_extend_transport_natural
    {Initial : Type uInitial}
    {sourceDepth targetDepth : Nat}
    {sourceAlignment : FiniteConstitutiveAlignment Initial sourceDepth}
    {targetAlignment : FiniteConstitutiveAlignment Initial targetDepth}
    (sourceA sourceB : sourceAlignment.Realization)
    (targetA targetB : targetAlignment.Realization)
    (depth : DepthExtension sourceDepth targetDepth)
    (identity : sourceA.Concrete) :
    (targetA.transport targetB).forward
        (sourceA.extend targetA depth identity) =
      sourceB.extend targetB depth
        ((sourceA.transport sourceB).forward identity) := by
  change
    targetB.indexedSpoke.forward
        (targetA.indexedSpoke.backward
          (targetA.indexedSpoke.forward
            (IteratedCarrier.embedFrom depth
              (sourceA.indexedSpoke.backward identity)))) =
      targetB.indexedSpoke.forward
        (IteratedCarrier.embedFrom depth
          (sourceB.indexedSpoke.backward
            (sourceB.indexedSpoke.forward
              (sourceA.indexedSpoke.backward identity))))
  rw [targetA.indexedSpoke.forwardBackward]
  rw [sourceB.indexedSpoke.forwardBackward]

theorem actual_free_logged_depth_one_to_three
    (occurrence :
      (iteratedRealization examplePresentation exampleConcreteAlgebra 1).Concrete) :
    (((iteratedRealization examplePresentation exampleConcreteAlgebra 3).transport
        (iteratedRealization examplePresentation loggedConcreteAlgebra 3)).forward
      ((iteratedRealization examplePresentation exampleConcreteAlgebra 1).extend
        (iteratedRealization examplePresentation exampleConcreteAlgebra 3)
        (DepthExtension.step (.step (.refl 1))) occurrence)) =
      (iteratedRealization examplePresentation loggedConcreteAlgebra 1).extend
        (iteratedRealization examplePresentation loggedConcreteAlgebra 3)
        (DepthExtension.step (.step (.refl 1)))
        (((iteratedRealization examplePresentation exampleConcreteAlgebra 1).transport
          (iteratedRealization examplePresentation loggedConcreteAlgebra 1)).forward
          occurrence) := by
  exact independently_rederived_extend_transport_natural
    (iteratedRealization examplePresentation exampleConcreteAlgebra 1)
    (iteratedRealization examplePresentation loggedConcreteAlgebra 1)
    (iteratedRealization examplePresentation exampleConcreteAlgebra 3)
    (iteratedRealization examplePresentation loggedConcreteAlgebra 3)
    (DepthExtension.step (.step (.refl 1))) occurrence

def swapFresh
    {Initial : Type uInitial} :
    IteratedCarrier Initial 2 → IteratedCarrier Initial 2
  | .inl (.inl initial) => .inl (.inl initial)
  | .inl (.inr witness) => by cases witness; exact .inr ()
  | .inr witness => by cases witness; exact .inl (.inr ())

theorem swapFresh_involutive
    {Initial : Type uInitial}
    (identity : IteratedCarrier Initial 2) :
    swapFresh (swapFresh identity) = identity := by
  cases identity with
  | inl prior =>
      cases prior with
      | inl initial => rfl
      | inr witness => cases witness; rfl
  | inr witness => cases witness; rfl

def badFreshTransport
    {Initial : Type uInitial} :
    ExactTypeTransport
      (IteratedCarrier Initial 2)
      (IteratedCarrier Initial 2) :=
  { forward := swapFresh
    backward := swapFresh
    forwardBackward := swapFresh_involutive
    backwardForward := swapFresh_involutive }

theorem badFreshTransport_is_bijective
    {Initial : Type uInitial} :
    Function.Injective (@swapFresh Initial) := by
  intro first second equality
  have := congrArg swapFresh equality
  simpa [swapFresh_involutive] using this

theorem bad_square_fails_at_positive_depth
    {Initial : Type uInitial} :
    (@badFreshTransport Initial).forward
        (@IteratedCarrier.embedFrom Initial 1 2 (DepthExtension.step (.refl 1))
          (@IteratedCarrier.freshAtStep Initial 0)) ≠
      @IteratedCarrier.embedFrom Initial 1 2 (DepthExtension.step (.refl 1))
        (@IteratedCarrier.freshAtStep Initial 0) := by
  intro equality
  change (@IteratedCarrier.freshAtStep Initial 1 : IteratedCarrier Initial 2) =
    @IteratedCarrier.embedFrom Initial 1 2 (DepthExtension.step (.refl 1))
      (@IteratedCarrier.freshAtStep Initial 0) at equality
  cases equality

/-! ## An actual free/logged realization counterexample -/

def swapFreshAtThree
    {Initial : Type uInitial} :
    IteratedCarrier Initial 3 → IteratedCarrier Initial 3
  | .inl prior =>
      match prior with
      | .inl priorTwo =>
          match priorTwo with
          | .inl initial => .inl (.inl (.inl initial))
          | .inr witness => by cases witness; exact .inl (.inr ())
      | .inr witness => by cases witness; exact .inl (.inl (.inr ()))
  | .inr witness => by cases witness; exact .inr ()

theorem swapFreshAtThree_involutive
    {Initial : Type uInitial}
    (identity : IteratedCarrier Initial 3) :
    swapFreshAtThree (swapFreshAtThree identity) = identity := by
  cases identity with
  | inl prior =>
      cases prior with
      | inl priorTwo =>
          cases priorTwo with
          | inl initial => rfl
          | inr witness => cases witness; rfl
      | inr witness => cases witness; rfl
  | inr witness => cases witness; rfl

def badThreeTransport
    {Initial : Type uInitial} :
    ExactTypeTransport
      (IteratedCarrier Initial 3)
      (IteratedCarrier Initial 3) :=
  { forward := swapFreshAtThree
    backward := swapFreshAtThree
    forwardBackward := swapFreshAtThree_involutive
    backwardForward := swapFreshAtThree_involutive }

def badFreeLoggedTransport :
    ExactTypeTransport
      (Examples.Alignment.IteratedReadout.FreeRealization 3).Concrete
      (Examples.Alignment.IteratedReadout.LoggedRealization 3).Concrete :=
  (Examples.Alignment.IteratedReadout.FreeRealization 3).indexedSpoke.reverse.compose
    ((badThreeTransport).compose
      (Examples.Alignment.IteratedReadout.LoggedRealization 3).indexedSpoke)

theorem bad_free_logged_square_fails :
    badFreeLoggedTransport.forward
        ((Examples.Alignment.IteratedReadout.FreeRealization 3).indexedSpoke.forward
          firstFreshAtThree) ≠
      (Examples.Alignment.IteratedReadout.LoggedRealization 3).indexedSpoke.forward
        firstFreshAtThree := by
  intro equality
  have pulled := congrArg
    (Examples.Alignment.IteratedReadout.LoggedRealization 3).indexedSpoke.backward equality
  unfold badFreeLoggedTransport ExactTypeTransport.compose ExactTypeTransport.reverse at pulled
  change
    (Examples.Alignment.IteratedReadout.LoggedRealization 3).indexedSpoke.backward
        ((Examples.Alignment.IteratedReadout.LoggedRealization 3).indexedSpoke.forward
          (badThreeTransport.forward
            ((Examples.Alignment.IteratedReadout.FreeRealization 3).indexedSpoke.backward
              ((Examples.Alignment.IteratedReadout.FreeRealization 3).indexedSpoke.forward
                firstFreshAtThree)))) =
      (Examples.Alignment.IteratedReadout.LoggedRealization 3).indexedSpoke.backward
        ((Examples.Alignment.IteratedReadout.LoggedRealization 3).indexedSpoke.forward
          firstFreshAtThree) at pulled
  rw [(Examples.Alignment.IteratedReadout.FreeRealization 3).indexedSpoke.forwardBackward] at pulled
  rw [(Examples.Alignment.IteratedReadout.LoggedRealization 3).indexedSpoke.forwardBackward] at pulled
  change swapFreshAtThree firstFreshAtThree = firstFreshAtThree at pulled
  cases pulled

theorem bad_free_logged_extension_square_fails :
    badFreeLoggedTransport.forward
        ((Examples.Alignment.IteratedReadout.FreeRealization 1).extend
          (Examples.Alignment.IteratedReadout.FreeRealization 3)
          (DepthExtension.step (.step (.refl 1)))
          ((Examples.Alignment.IteratedReadout.FreeRealization 1).indexedSpoke.forward
            firstFreshAtOne)) ≠
      (Examples.Alignment.IteratedReadout.LoggedRealization 1).extend
        (Examples.Alignment.IteratedReadout.LoggedRealization 3)
        (DepthExtension.step (.step (.refl 1)))
        ((Examples.Alignment.IteratedReadout.LoggedRealization 1).indexedSpoke.forward
          firstFreshAtOne) := by
  change
    badFreeLoggedTransport.forward
        ((Examples.Alignment.IteratedReadout.FreeRealization 3).indexedSpoke.forward
          firstFreshAtThree) ≠
      (Examples.Alignment.IteratedReadout.LoggedRealization 3).indexedSpoke.forward
        firstFreshAtThree
  exact bad_free_logged_square_fails

end StrongPerimetralTurning.Tests.DynamicAlignmentRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.Tests.DynamicAlignmentRegression.independently_rederived_extend_transport_natural
#print axioms StrongPerimetralTurning.Tests.DynamicAlignmentRegression.actual_free_logged_depth_one_to_three
#print axioms StrongPerimetralTurning.Tests.DynamicAlignmentRegression.swapFresh
#print axioms StrongPerimetralTurning.Tests.DynamicAlignmentRegression.swapFresh_involutive
#print axioms StrongPerimetralTurning.Tests.DynamicAlignmentRegression.badFreshTransport
#print axioms StrongPerimetralTurning.Tests.DynamicAlignmentRegression.badFreshTransport_is_bijective
#print axioms StrongPerimetralTurning.Tests.DynamicAlignmentRegression.bad_square_fails_at_positive_depth
#print axioms StrongPerimetralTurning.Tests.DynamicAlignmentRegression.swapFreshAtThree
#print axioms StrongPerimetralTurning.Tests.DynamicAlignmentRegression.swapFreshAtThree_involutive
#print axioms StrongPerimetralTurning.Tests.DynamicAlignmentRegression.badThreeTransport
#print axioms StrongPerimetralTurning.Tests.DynamicAlignmentRegression.badFreeLoggedTransport
#print axioms StrongPerimetralTurning.Tests.DynamicAlignmentRegression.bad_free_logged_square_fails
#print axioms StrongPerimetralTurning.Tests.DynamicAlignmentRegression.bad_free_logged_extension_square_fails
/- AXIOM_AUDIT_END -/
