import StrongPerimetralTurning

/-!
# Structural entry point

This file is a human-scale facade over the structural foundation.  It exposes
two complementary certificates and introduces no new assumption:

* the canonical perimeter is exactly realized and satisfies both the
  operational regime and the independent specification;
* one generated step beyond that perimeter is a strict continuation;
* its continuation contains exactly one occurrence and remains faithfully
  realizable in every supplied concrete continuation algebra;
* the same candidate lies outside both the operational regime and the
  independent specification.
* perimeter positions, free occurrences, and concrete occurrences form an
  exact structural bus before any readout or value type is chosen.

The short construction below does not replace the underlying proofs.  It makes
their joint conclusion inspectable from a single declaration.
-/

namespace StructuralEntrypoint

open StrongPerimetralTurning

/--
The canonical human-scale certificate: exact reconstruction of the perimeter
does not close construction.  A uniquely generated continuation remains
faithfully realizable in every supplied concrete continuation algebra, while
that continuation exits the established regime and its independent norm.
-/
structure ExactPerimeterAndFaithfulExit
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) : Type _ where
  perimeterExact :
    ExactPerimeterRealization P (perimeterDeployment P)
  perimeterInRegime :
    CircularRefinement P (perimeterDeployment P)
  perimeterSatisfiesSpecification :
    CircularSpecificationSatisfaction P (perimeterDeployment P)
  continuationStrict :
    StrictConstitutivePrefix
      (perimeterDeployment P) (oneStepAfterPerimeter P)
  continuationHasExactlyOneOccurrence :
    History.ExactlyOne
      (oneStepFaithfullyLabelledExtension P).continuation
  continuationFaithful :
    ExactConcreteRealization A (oneStepAfterPerimeter P)
  continuationOutsideRegime :
    CircularRefinement P (oneStepAfterPerimeter P) → False
  continuationOutsideSpecification :
    CircularSpecificationSatisfaction P (oneStepAfterPerimeter P) → False

/--
The certificate is constructed entirely from the canonical witnesses already
proved by the structural foundation. Since `A` is arbitrary, this declaration
constructs the faithful continuation for every supplied implementation; no
implementation is postulated by the facade.
-/
def exactPerimeterAndFaithfulExit
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    ExactPerimeterAndFaithfulExit P A :=
  { perimeterExact := perimeterRealization P
    perimeterInRegime := identityCircularRefinement P
    perimeterSatisfiesSpecification :=
      perimeterDeployment_specificationSatisfaction P
    continuationStrict := oneStepAfterPerimeterStrict P
    continuationHasExactlyOneOccurrence :=
      positiveContinuation_exactlyOne
        (oneStepFaithfullyLabelledExtension P)
        (oneStepAfterPerimeter_positiveContinuation P)
    continuationFaithful :=
      exactlyInterpretHistory A (oneStepAfterPerimeter P).history
    continuationOutsideRegime :=
      oneStepAfterPerimeter_notCircularRefinement P
    continuationOutsideSpecification :=
      oneStepAfterPerimeter_notSpecificationSatisfaction P }

/--
Exact structural bus from perimeter positions to free occurrences and then to
occurrences in any supplied concrete realization.

No readout value is part of this structure. The identities and their exact
correspondences are established before any evaluation is attached to them.

Conceptually, occurrences and their exact correspondences form a structural
bus onto which independent readouts can be attached after constitution.
-/
structure ExactReadoutBus
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) : Type _ where
  perimeterOccurrences :
    ExactTypeTransport
      (NonClosingPosition P.perimeter)
      (History.Occurrence (perimeterHistory P))
  concreteInterpretation :
    ExactHistoryInterpretation
      A
      (perimeterHistory P)
      (A.realizeHistory (perimeterHistory P))

/--
The structural bus is obtained entirely from already proved exact
correspondences. No evaluation and no value type is required.
-/
def exactReadoutBus
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    ExactReadoutBus P A :=
  { perimeterOccurrences :=
      { forward := requirementToOccurrence P
        backward := occurrenceToRequirement P
        forwardBackward := requirementToOccurrence_toRequirement P
        backwardForward := occurrenceToRequirement_toOccurrence P }
    concreteInterpretation :=
      exactlyInterpretHistory A (perimeterHistory P) }

namespace ExactReadoutBus

universe uValue

/--
Attach an arbitrary readout to perimeter identities and read it on the
corresponding concrete occurrences. The value type is completely independent
of the structural bus.
-/
def toConcreteReadout
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    (bus : ExactReadoutBus P A)
    {Value : Type uValue}
    (readout : NonClosingPosition P.perimeter → Value) :
    History.Occurrence
        (A.realizeHistory (perimeterHistory P)) →
      Value :=
  fun occurrence =>
    readout
      (bus.perimeterOccurrences.backward
        (bus.concreteInterpretation.backwardOccurrence occurrence))

/--
Read a concrete occurrence-indexed evaluation back on the canonical perimeter
identities.
-/
def toPerimeterReadout
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    (bus : ExactReadoutBus P A)
    {Value : Type uValue}
    (readout :
      History.Occurrence
          (A.realizeHistory (perimeterHistory P)) →
        Value) :
    NonClosingPosition P.perimeter → Value :=
  fun position =>
    readout
      (bus.concreteInterpretation.forwardOccurrence
        (bus.perimeterOccurrences.forward position))

/-- Perimeter readouts are recovered pointwise after transport to the realization. -/
theorem toPerimeterReadout_toConcreteReadout
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    (bus : ExactReadoutBus P A)
    {Value : Type uValue}
    (readout : NonClosingPosition P.perimeter → Value)
    (position : NonClosingPosition P.perimeter) :
    bus.toPerimeterReadout (bus.toConcreteReadout readout) position =
      readout position := by
  change
    readout
      (bus.perimeterOccurrences.backward
        (bus.concreteInterpretation.backwardOccurrence
          (bus.concreteInterpretation.forwardOccurrence
            (bus.perimeterOccurrences.forward position)))) =
      readout position
  rw [bus.concreteInterpretation.forwardBackward]
  rw [bus.perimeterOccurrences.forwardBackward]

/-- Concrete occurrence readouts are recovered pointwise after transport back. -/
theorem toConcreteReadout_toPerimeterReadout
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    (bus : ExactReadoutBus P A)
    {Value : Type uValue}
    (readout :
      History.Occurrence
          (A.realizeHistory (perimeterHistory P)) →
        Value)
    (occurrence :
      History.Occurrence
        (A.realizeHistory (perimeterHistory P))) :
    bus.toConcreteReadout (bus.toPerimeterReadout readout) occurrence =
      readout occurrence := by
  change
    readout
      (bus.concreteInterpretation.forwardOccurrence
        (bus.perimeterOccurrences.forward
          (bus.perimeterOccurrences.backward
            (bus.concreteInterpretation.backwardOccurrence occurrence)))) =
      readout occurrence
  rw [bus.perimeterOccurrences.backwardForward]
  rw [bus.concreteInterpretation.backwardForward]

end ExactReadoutBus

end StructuralEntrypoint

/- AXIOM_AUDIT_BEGIN -/
#print axioms StructuralEntrypoint.ExactPerimeterAndFaithfulExit
#print axioms StructuralEntrypoint.exactPerimeterAndFaithfulExit
#print axioms StructuralEntrypoint.ExactReadoutBus
#print axioms StructuralEntrypoint.exactReadoutBus
#print axioms StructuralEntrypoint.ExactReadoutBus.toConcreteReadout
#print axioms StructuralEntrypoint.ExactReadoutBus.toPerimeterReadout
#print axioms StructuralEntrypoint.ExactReadoutBus.toPerimeterReadout_toConcreteReadout
#print axioms StructuralEntrypoint.ExactReadoutBus.toConcreteReadout_toPerimeterReadout
/- AXIOM_AUDIT_END -/
