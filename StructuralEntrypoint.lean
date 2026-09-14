import Cycle1.ConstitutivePersistence

/-!
# Structural entry point

The theoretical unit of this project is neither a particular layer nor a final
result, but the demonstrated continuity of a single determination across
several distinct and interdependent layers.  Roles are established before their
representations, transported without merging the layers, and only then made
available to independent readouts.  This organization requires a global
interpretation of local results.

The same constitutive determination is followed through the facade as follows:

```text
constitutive positions/requirements of the perimeter
        ↓ exact agreement
local occurrences in an arbitrary history
        ↓ local-to-global reconstruction
canonical perimeter as an initial factor
        ├──────────────────────────────────┐
        ↓                                  ↓
one-occurrence continuation            perimeter positions
        ↓                                  ↕
perimeter preserved as a prefix        free occurrences
        ↓                                  ↕
exact realization of the               concrete occurrences in
extended history                       each realization
        ↓                                  ↓
exit from the regime and               coordination through
from the specification                 the same index
                                           ↓
                                       readouts attached only afterward
```

The facade preserves differences of status while demonstrating the exact
transports that allow a single constitutive determination to pass through
them. Here, identity means the persistence of that determination across
distinct layers through those transports.

This file is therefore a human-scale facade over the structural foundation.  It
exposes the following articulated results and introduces no new assumption:

* exact local realization in any rooted generated history reconstructs the
  canonical perimeter as an initial factor of that history;
* the canonical perimeter is exactly realized and satisfies both the
  operational regime and the independent specification, while one generated
  step beyond it is a strict one-occurrence continuation which remains exactly
  realizable in every supplied concrete continuation algebra but lies outside
  both the regime and the specification;
* that one-step continuation has an exact old/fresh occurrence split whose
  realizations commute with change of concrete representation and whose
  induced transports are pointwise independent of intermediate realizations;
* the canonical facade construction supplies mutually inverse correspondences
  between perimeter positions, free occurrences, and concrete occurrences
  before any readout or value type is chosen; two supplied concrete
  realizations are then coordinated through those same positions, so their
  occurrence readouts can be reindexed without adding an independent pairwise
  matching.

The short constructions below do not replace the underlying proofs.  They make
the local-to-global reconstruction, the canonical exit, its exact one-step
constitutive alignment, and the structural readout bus available in one
human-scale file.
-/

namespace StructuralEntrypoint

open StrongPerimetralTurning

/--
The central local-to-global reconstruction theorem of Cycle 1, exposed at the
human-scale entry point.

The input is an arbitrary exact local realization inside a genuine
`RootedGeneratedHistory`; it is not assumed to be the canonical deployment.
Its primitive data are a realization map and exact source-cursor agreement for
each non-closing perimeter requirement.  Injectivity is reconstructed from that
agreement rather than postulated.

The output constructively exhibits the canonical perimeter history as an exact
initial factor of the supplied history.  It may leave a positive continuation,
so this result does not claim that the perimeter exhausts the history.  This
facade is a definitional alias of the foundational construction.  It preserves
the witness layer and adds no hypothesis.  The compiler emits IR for it, and it
reduces to a value when the presentation and realization are supplied as closed
data.
-/
def localExactnessReconstructsPerimeter
    {P : CircularPresentation}
    {history : RootedGeneratedHistory P}
    (realization : ExactNonClosingRealization P history) :
    PerimeterExtension P history :=
  realization.toPerimeterExtension

/--
The canonical human-scale certificate: exact reconstruction of the perimeter
does not close construction.  The canonical one-step continuation contains
exactly one occurrence, and the resulting history, like every rooted generated
history, admits an `ExactConcreteRealization` in every supplied concrete
continuation algebra.  That history nevertheless exits the established regime
and its independent norm.  Both refutations are relative to the supplied
`CircularPresentation`, in particular its explicit
`rejectInitialContraction` field.
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
provides the repository's `ExactConcreteRealization` witness for the resulting
history in every supplied implementation; no implementation is postulated by
the facade.
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

/-!
The transition exposed above also instantiates a content-independent notion of
exact one-step constitutive alignment.  The abstract interface contains only
an exact old/fresh split.  Each concrete algebra supplies a separate exact
carrier realization of that split.  At this content-independent level,
`Realization` asserts no preservation of labels, order, or step semantics.
Naturality, path coherence, and relative pointwise uniqueness are then derived
by `ExactOneStepConstitutiveAlignment.Realization`; they are not additional
matching data.  In the canonical instance, the induced old and fresh elements
are proved to be the native concrete occurrences `.earlier` and `.last`.

This layer contains no admission, specification, or readout value.  Those
remain distinct before being articulated by the surrounding facade.
-/

/-- The canonical one-step transition as a content-independent alignment. -/
def canonicalConstitutiveAlignment
    (P : CircularPresentation) :
    ExactOneStepConstitutiveAlignment :=
  ConstitutivePersistence.canonicalOneStepAlignment P

/-- One supplied concrete algebra as an exact carrier realization. -/
def canonicalConstitutiveAlignmentRealization
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    (canonicalConstitutiveAlignment P).Realization :=
  ConstitutivePersistence.canonicalOneStepAlignmentRealization P A

/--
Structural bus from perimeter positions to free occurrences and then to
occurrences in any supplied concrete realization.

No readout value is part of this structure. The identities and their exact
correspondences are established before any evaluation is attached to them.
Here, `exact` means that the two maps of each correspondence are mutually
inverse.  The interface does not assert that an inhabitant is canonical or
unique, nor that an arbitrary inhabitant preserves order, adjacency, or labels.

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
The canonical structural bus used by the repository is obtained entirely from
already proved exact correspondences.  No evaluation and no value type is
required.  This definition supplies the canonical inhabitant; the
`ExactReadoutBus` interface itself does not assert uniqueness.
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
One exact spoke of the star-shaped bus, from perimeter identities directly to
the concrete occurrences of one supplied realization.

The spoke composes the already established position/free-occurrence and
free/concrete-occurrence correspondences.  It introduces no pairwise matching
with any other realization.
-/
def concreteOccurrenceSpoke
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    (bus : ExactReadoutBus P A) :
    ExactTypeTransport
      (NonClosingPosition P.perimeter)
      (History.Occurrence
        (A.realizeHistory (perimeterHistory P))) :=
  { forward := fun position =>
      bus.concreteInterpretation.forwardOccurrence
        (bus.perimeterOccurrences.forward position)
    backward := fun occurrence =>
      bus.perimeterOccurrences.backward
        (bus.concreteInterpretation.backwardOccurrence occurrence)
    forwardBackward := by
      intro position
      change
        bus.perimeterOccurrences.backward
            (bus.concreteInterpretation.backwardOccurrence
              (bus.concreteInterpretation.forwardOccurrence
                (bus.perimeterOccurrences.forward position))) =
          position
      rw [bus.concreteInterpretation.forwardBackward]
      rw [bus.perimeterOccurrences.forwardBackward]
    backwardForward := by
      intro occurrence
      change
        bus.concreteInterpretation.forwardOccurrence
            (bus.perimeterOccurrences.forward
              (bus.perimeterOccurrences.backward
                (bus.concreteInterpretation.backwardOccurrence occurrence))) =
          occurrence
      rw [bus.perimeterOccurrences.backwardForward]
      rw [bus.concreteInterpretation.backwardForward] }

/--
The concrete occurrence selected by one spoke at a perimeter position.

This is one spoke of the structural bus: the position is first sent to its free
occurrence and then to the corresponding occurrence in the supplied concrete
realization.  No readout value is involved.
-/
def concreteOccurrenceAt
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    (bus : ExactReadoutBus P A)
    (position : NonClosingPosition P.perimeter) :
    History.Occurrence
      (A.realizeHistory (perimeterHistory P)) :=
  bus.concreteOccurrenceSpoke.forward position

/--
Coordinate the concrete occurrences of two supplied realizations through their
shared perimeter identities.

The forward map follows the exact route

```text
source concrete occurrence
  -> free occurrence
  -> perimeter position
  -> free occurrence
  -> target concrete occurrence
```

and the backward map follows the reverse route.  Thus no independent pairwise
matching between the two concrete realizations is added.  The result is exact
for the two buses supplied here; it does not assert that every possible exact
coordination is equal to this one, nor does it impose a semantic relation on
values later attached to the coordinated occurrences.
-/
def concreteOccurrenceTransport
    {P : CircularPresentation}
    {A B : ConcreteContinuationAlgebra P}
    (sourceBus : ExactReadoutBus P A)
    (targetBus : ExactReadoutBus P B) :
    ExactTypeTransport
      (History.Occurrence
        (A.realizeHistory (perimeterHistory P)))
      (History.Occurrence
        (B.realizeHistory (perimeterHistory P))) :=
  { forward := fun occurrence =>
      targetBus.concreteOccurrenceSpoke.forward
        (sourceBus.concreteOccurrenceSpoke.backward occurrence)
    backward := fun occurrence =>
      sourceBus.concreteOccurrenceSpoke.forward
        (targetBus.concreteOccurrenceSpoke.backward occurrence)
    forwardBackward := by
      intro occurrence
      change
        sourceBus.concreteOccurrenceSpoke.forward
            (targetBus.concreteOccurrenceSpoke.backward
              (targetBus.concreteOccurrenceSpoke.forward
                (sourceBus.concreteOccurrenceSpoke.backward occurrence))) =
          occurrence
      rw [targetBus.concreteOccurrenceSpoke.forwardBackward]
      rw [sourceBus.concreteOccurrenceSpoke.backwardForward]
    backwardForward := by
      intro occurrence
      change
        targetBus.concreteOccurrenceSpoke.forward
            (sourceBus.concreteOccurrenceSpoke.backward
              (sourceBus.concreteOccurrenceSpoke.forward
                (targetBus.concreteOccurrenceSpoke.backward occurrence))) =
          occurrence
      rw [sourceBus.concreteOccurrenceSpoke.forwardBackward]
      rw [targetBus.concreteOccurrenceSpoke.backwardForward] }

/--
The concrete-to-concrete transport preserves the common perimeter index
pointwise.  This is the precise synchronization supplied by the structural bus:
the two concrete occurrences are coordinated because both realize the same
position, not because their values were compared after construction.
-/
theorem concreteOccurrenceTransport_atPosition
    {P : CircularPresentation}
    {A B : ConcreteContinuationAlgebra P}
    (sourceBus : ExactReadoutBus P A)
    (targetBus : ExactReadoutBus P B)
    (position : NonClosingPosition P.perimeter) :
    (sourceBus.concreteOccurrenceTransport targetBus).forward
        (sourceBus.concreteOccurrenceAt position) =
      targetBus.concreteOccurrenceAt position := by
  change
    targetBus.concreteOccurrenceSpoke.forward
        (sourceBus.concreteOccurrenceSpoke.backward
          (sourceBus.concreteOccurrenceSpoke.forward position)) =
      targetBus.concreteOccurrenceSpoke.forward position
  rw [sourceBus.concreteOccurrenceSpoke.forwardBackward]

/--
Concrete occurrence transport is pointwise independent of an intermediate bus.
All three transports are induced by the same perimeter identities; no function
extensionality or additional pairwise coherence datum is required.
-/
theorem concreteOccurrenceTransport_forward_comp
    {P : CircularPresentation}
    {A B C : ConcreteContinuationAlgebra P}
    (sourceBus : ExactReadoutBus P A)
    (middleBus : ExactReadoutBus P B)
    (targetBus : ExactReadoutBus P C)
    (occurrence :
      History.Occurrence
        (A.realizeHistory (perimeterHistory P))) :
    (middleBus.concreteOccurrenceTransport targetBus).forward
        ((sourceBus.concreteOccurrenceTransport middleBus).forward
          occurrence) =
      (sourceBus.concreteOccurrenceTransport targetBus).forward occurrence := by
  change
    targetBus.concreteOccurrenceSpoke.forward
        (middleBus.concreteOccurrenceSpoke.backward
          (middleBus.concreteOccurrenceSpoke.forward
            (sourceBus.concreteOccurrenceSpoke.backward occurrence))) =
      targetBus.concreteOccurrenceSpoke.forward
        (sourceBus.concreteOccurrenceSpoke.backward occurrence)
  rw [middleBus.concreteOccurrenceSpoke.forwardBackward]

/--
The repository's canonical concrete-to-concrete coordination.  Each spoke is
the canonical `exactReadoutBus`; canonicity here names this chosen construction,
not a uniqueness theorem for all inhabitants of `ExactReadoutBus`.
-/
def exactConcreteOccurrenceTransport
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P) :
    ExactTypeTransport
      (History.Occurrence
        (A.realizeHistory (perimeterHistory P)))
      (History.Occurrence
        (B.realizeHistory (perimeterHistory P))) :=
  (exactReadoutBus P A).concreteOccurrenceTransport (exactReadoutBus P B)

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
    readout (bus.concreteOccurrenceSpoke.backward occurrence)

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
    readout (bus.concreteOccurrenceSpoke.forward position)

/--
Reindex a supplied concrete readout from one realization to another through the
shared structural bus.  This transports the indexing of the values only; it
does not assert any semantic compatibility between independently supplied
readouts.
-/
def transportConcreteReadout
    {P : CircularPresentation}
    {A B : ConcreteContinuationAlgebra P}
    (sourceBus : ExactReadoutBus P A)
    (targetBus : ExactReadoutBus P B)
    {Value : Type uValue}
    (readout :
      History.Occurrence
          (A.realizeHistory (perimeterHistory P)) →
        Value) :
    History.Occurrence
        (B.realizeHistory (perimeterHistory P)) →
      Value :=
  fun occurrence =>
    readout
      ((sourceBus.concreteOccurrenceTransport targetBus).backward occurrence)

/--
A readout transported between two concrete realizations assigns the same value
to the occurrences selected by the same perimeter position.
-/
theorem transportConcreteReadout_atPosition
    {P : CircularPresentation}
    {A B : ConcreteContinuationAlgebra P}
    (sourceBus : ExactReadoutBus P A)
    (targetBus : ExactReadoutBus P B)
    {Value : Type uValue}
    (readout :
      History.Occurrence
          (A.realizeHistory (perimeterHistory P)) →
        Value)
    (position : NonClosingPosition P.perimeter) :
    sourceBus.transportConcreteReadout targetBus readout
        (targetBus.concreteOccurrenceAt position) =
      readout (sourceBus.concreteOccurrenceAt position) := by
  change
    readout
        (sourceBus.concreteOccurrenceSpoke.forward
          (targetBus.concreteOccurrenceSpoke.backward
            (targetBus.concreteOccurrenceSpoke.forward position))) =
      readout (sourceBus.concreteOccurrenceSpoke.forward position)
  rw [targetBus.concreteOccurrenceSpoke.forwardBackward]

/-- Reindexing a concrete readout to another bus and back recovers it pointwise. -/
theorem transportConcreteReadout_roundTrip
    {P : CircularPresentation}
    {A B : ConcreteContinuationAlgebra P}
    (sourceBus : ExactReadoutBus P A)
    (targetBus : ExactReadoutBus P B)
    {Value : Type uValue}
    (readout :
      History.Occurrence
          (A.realizeHistory (perimeterHistory P)) →
        Value)
    (occurrence :
      History.Occurrence
        (A.realizeHistory (perimeterHistory P))) :
    targetBus.transportConcreteReadout sourceBus
        (sourceBus.transportConcreteReadout targetBus readout) occurrence =
      readout occurrence := by
  change
    readout
        ((sourceBus.concreteOccurrenceTransport targetBus).backward
          ((targetBus.concreteOccurrenceTransport sourceBus).backward
            occurrence)) =
      readout occurrence
  change
    readout
        ((sourceBus.concreteOccurrenceTransport targetBus).backward
          ((sourceBus.concreteOccurrenceTransport targetBus).forward
            occurrence)) =
      readout occurrence
  rw [(sourceBus.concreteOccurrenceTransport targetBus).forwardBackward]

/--
Concrete readout reindexing is pointwise independent of an intermediate bus.
This is the readout consequence of concrete occurrence transport coherence; it
adds no semantic relation between independently supplied values.
-/
theorem transportConcreteReadout_comp
    {P : CircularPresentation}
    {A B C : ConcreteContinuationAlgebra P}
    (sourceBus : ExactReadoutBus P A)
    (middleBus : ExactReadoutBus P B)
    (targetBus : ExactReadoutBus P C)
    {Value : Type uValue}
    (readout :
      History.Occurrence
          (A.realizeHistory (perimeterHistory P)) →
        Value)
    (occurrence :
      History.Occurrence
        (C.realizeHistory (perimeterHistory P))) :
    middleBus.transportConcreteReadout targetBus
        (sourceBus.transportConcreteReadout middleBus readout) occurrence =
      sourceBus.transportConcreteReadout targetBus readout occurrence := by
  change
    readout
        ((sourceBus.concreteOccurrenceTransport middleBus).backward
          ((middleBus.concreteOccurrenceTransport targetBus).backward
            occurrence)) =
      readout
        ((sourceBus.concreteOccurrenceTransport targetBus).backward occurrence)
  exact congrArg readout
    (concreteOccurrenceTransport_forward_comp
      targetBus middleBus sourceBus occurrence)

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
      (bus.concreteOccurrenceSpoke.backward
        (bus.concreteOccurrenceSpoke.forward position)) =
      readout position
  rw [bus.concreteOccurrenceSpoke.forwardBackward]

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
      (bus.concreteOccurrenceSpoke.forward
        (bus.concreteOccurrenceSpoke.backward occurrence)) =
      readout occurrence
  rw [bus.concreteOccurrenceSpoke.backwardForward]

end ExactReadoutBus

end StructuralEntrypoint

/- AXIOM_AUDIT_BEGIN -/
#print axioms StructuralEntrypoint.localExactnessReconstructsPerimeter
#print axioms StructuralEntrypoint.ExactPerimeterAndFaithfulExit
#print axioms StructuralEntrypoint.exactPerimeterAndFaithfulExit
#print axioms StructuralEntrypoint.canonicalConstitutiveAlignment
#print axioms StructuralEntrypoint.canonicalConstitutiveAlignmentRealization
#print axioms StructuralEntrypoint.ExactReadoutBus
#print axioms StructuralEntrypoint.exactReadoutBus
#print axioms StructuralEntrypoint.ExactReadoutBus.concreteOccurrenceSpoke
#print axioms StructuralEntrypoint.ExactReadoutBus.concreteOccurrenceAt
#print axioms StructuralEntrypoint.ExactReadoutBus.concreteOccurrenceTransport
#print axioms StructuralEntrypoint.ExactReadoutBus.concreteOccurrenceTransport_atPosition
#print axioms StructuralEntrypoint.ExactReadoutBus.concreteOccurrenceTransport_forward_comp
#print axioms StructuralEntrypoint.ExactReadoutBus.exactConcreteOccurrenceTransport
#print axioms StructuralEntrypoint.ExactReadoutBus.toConcreteReadout
#print axioms StructuralEntrypoint.ExactReadoutBus.toPerimeterReadout
#print axioms StructuralEntrypoint.ExactReadoutBus.transportConcreteReadout
#print axioms StructuralEntrypoint.ExactReadoutBus.transportConcreteReadout_atPosition
#print axioms StructuralEntrypoint.ExactReadoutBus.transportConcreteReadout_roundTrip
#print axioms StructuralEntrypoint.ExactReadoutBus.transportConcreteReadout_comp
#print axioms StructuralEntrypoint.ExactReadoutBus.toPerimeterReadout_toConcreteReadout
#print axioms StructuralEntrypoint.ExactReadoutBus.toConcreteReadout_toPerimeterReadout
/- AXIOM_AUDIT_END -/
