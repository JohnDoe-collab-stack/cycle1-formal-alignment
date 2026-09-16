import StrongPerimetralTurning.IteratedConstitutivePersistence

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
* the same constitution extends to every finite number of real circular generation steps:
  earlier identities persist, each step contributes one fresh identity, and
  finite extension is independent of its proof-relevant depth witness and
  commutes with change of exact concrete realization; this independence also
  holds when source and target use different supplied realizations; at depth
  one both directions of horizontal transport, the fresh identity, and the
  vertical old map agree pointwise with the established one-step interface;
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
The central local-to-global reconstruction theorem of the circular instance, exposed at the
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
continuation algebra.  This realization field records a positive preservation
witness; once the algebra is supplied, it is not a condition selecting
histories.  In the circular instance, the regime and the independently defined
norm each hold exactly of the canonical perimeter, although their witness types
and proof routes remain distinct.  The continued history exits both.  Both
refutations are relative to the supplied `CircularPresentation`, in particular
its explicit `rejectInitialContraction` field.
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
  /-- Positive exact-transport witness, not a history-selection condition. -/
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

/-!
The one-step alignment above extends constructively to every finite number of
actual circular generations.  Each stage is produced by `generate` and
`appendGenerated`; it is not an abstract chain postulated by the facade.

Every determination, once constituted, persists through every later stage of
any finite prefix of this generated chain, and that persistence commutes with
change of exact realization.  A readout assembled afterward by finite extension
therefore preserves every distinction it already makes on those determinations.
This does not yet instantiate a transformer and does not identify independently
supplied readouts.
-/

/-- The exact free occurrence carrier after `n` actual circular generations. -/
def finiteConstitutivePersistence
    (P : CircularPresentation)
    (n : Nat) :
    FiniteConstitutiveAlignment
      (ConstitutivePersistence.InitialFreeOccurrence P) n :=
  IteratedConstitutivePersistence.iteratedAlignment P n

/-- One supplied algebra realizes the actual circular carrier at depth `n`. -/
def finiteConstitutivePersistenceRealization
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (n : Nat) :
    (finiteConstitutivePersistence P n).Realization :=
  IteratedConstitutivePersistence.iteratedRealization P A n

/--
Finite extension and change of realization commute on the actual circular instance
occurrences, including identities first constituted after the perimeter.
-/
theorem finiteExtensionRealizationNaturality
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    {sourceDepth targetDepth : Nat}
    (depth : DepthExtension sourceDepth targetDepth)
    (occurrence :
      (finiteConstitutivePersistenceRealization P A sourceDepth).Concrete) :
    (((finiteConstitutivePersistenceRealization P A targetDepth).transport
        (finiteConstitutivePersistenceRealization P B targetDepth)).forward
      ((finiteConstitutivePersistenceRealization P A sourceDepth).extend
        (finiteConstitutivePersistenceRealization P A targetDepth)
        depth occurrence)) =
      (finiteConstitutivePersistenceRealization P B sourceDepth).extend
        (finiteConstitutivePersistenceRealization P B targetDepth)
        depth
        (((finiteConstitutivePersistenceRealization P A sourceDepth).transport
          (finiteConstitutivePersistenceRealization P B sourceDepth)).forward
          occurrence) :=
  IteratedConstitutivePersistence.iterated_extend_transport_natural
    P A B depth occurrence

/--
Finite extension on actual circular realizations depends only on its source and
target depths, not on the proof-relevant `DepthExtension` witness supplied.
-/
theorem finiteExtensionWitnessIndependent
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    {sourceDepth targetDepth : Nat}
    (first second : DepthExtension sourceDepth targetDepth)
    (occurrence :
      (finiteConstitutivePersistenceRealization P A sourceDepth).Concrete) :
    (finiteConstitutivePersistenceRealization P A sourceDepth).extend
        (finiteConstitutivePersistenceRealization P A targetDepth)
        first occurrence =
      (finiteConstitutivePersistenceRealization P A sourceDepth).extend
        (finiteConstitutivePersistenceRealization P A targetDepth)
        second occurrence :=
  FiniteConstitutiveAlignment.Realization.extend_witness_independent
    (finiteConstitutivePersistenceRealization P A sourceDepth)
    (finiteConstitutivePersistenceRealization P A targetDepth)
    first second occurrence

/--
Finite extension remains witness-independent when its source and target are
two different supplied concrete realizations.
-/
theorem finiteExtensionWitnessIndependentAcrossRealizations
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    {sourceDepth targetDepth : Nat}
    (first second : DepthExtension sourceDepth targetDepth)
    (occurrence :
      (finiteConstitutivePersistenceRealization P A sourceDepth).Concrete) :
    (finiteConstitutivePersistenceRealization P A sourceDepth).extend
        (finiteConstitutivePersistenceRealization P B targetDepth)
        first occurrence =
      (finiteConstitutivePersistenceRealization P A sourceDepth).extend
        (finiteConstitutivePersistenceRealization P B targetDepth)
        second occurrence :=
  IteratedConstitutivePersistence.iteratedExtension_witness_independent
    P A B first second occurrence

/--
The finite horizontal transport at depth one is pointwise the previously
established one-step transport, so iteration adds no competing correspondence
at its base case.
-/
theorem finiteDepthOneTransportMatchesOneStep
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    (occurrence :
      (finiteConstitutivePersistenceRealization P A 1).Concrete) :
    (((finiteConstitutivePersistenceRealization P A 1).transport
        (finiteConstitutivePersistenceRealization P B 1)).forward occurrence) =
      (((canonicalConstitutiveAlignmentRealization P A).extendedTransport
        (canonicalConstitutiveAlignmentRealization P B)).forward occurrence) :=
  IteratedConstitutivePersistence.iteratedTransport_one_eq_oneStep
    P A B occurrence

/--
The backward finite horizontal transport at depth one is pointwise the
backward map of the previously established one-step transport.
-/
theorem finiteDepthOneBackwardTransportMatchesOneStep
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    (occurrence :
      (finiteConstitutivePersistenceRealization P B 1).Concrete) :
    (((finiteConstitutivePersistenceRealization P A 1).transport
        (finiteConstitutivePersistenceRealization P B 1)).backward occurrence) =
      (((canonicalConstitutiveAlignmentRealization P A).extendedTransport
        (canonicalConstitutiveAlignmentRealization P B)).backward occurrence) :=
  IteratedConstitutivePersistence.iteratedTransport_one_backward_eq_oneStep
    P A B occurrence

/-- The finite fresh identity at depth one is the one-step fresh identity. -/
theorem finiteDepthOneFreshMatchesOneStep
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    (finiteConstitutivePersistenceRealization P A 1).indexedSpoke.forward
        (IteratedCarrier.freshAtStep 0) =
      (canonicalConstitutiveAlignmentRealization P A).fresh :=
  IteratedConstitutivePersistence.iteratedRealization_one_fresh_eq_oneStep P A

/-! ## Operational meaning of aligned persistence -/

/--
The fresh identity of the canonical one-step alignment is exactly the
full-history residual occurrence consumed by the operational turning theorem.
-/
theorem oneStepAlignmentFreshIsConsumedResidual
    (P : CircularPresentation) :
    (canonicalConstitutiveAlignment P).fresh =
      (oneStepFaithfullyLabelledExtension P).newOccurrence
        ((abstractTurningOfCircularPresentation P).uniqueResidualOccurrence.occurrence) := by
  change
    (ConstitutivePersistence.canonicalOneStepAlignment P).fresh =
      (oneStepFaithfullyLabelledExtension P).newOccurrence
        ((abstractTurningOfCircularPresentation P).uniqueResidualOccurrence.occurrence)
  exact
    (ConstitutivePersistence.canonicalAlignment_fresh_eq_residualFreeOccurrence P).trans
      (ConstitutivePersistence.residualFreeOccurrence_agrees_with_consumedTurning P)

/--
The operational residual occurrence constituted at the first exit persists as
the same constitutive identity through every later finite circular depth.
-/
theorem finiteOperationalResidualPersists
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    {targetDepth : Nat}
    (depth : DepthExtension 1 targetDepth) :
    (finiteConstitutivePersistenceRealization P A 1).extend
        (finiteConstitutivePersistenceRealization P A targetDepth)
        depth
        (ConstitutivePersistence.oneStepResidualConcreteOccurrence P A) =
      (finiteConstitutivePersistenceRealization P A targetDepth).indexedSpoke.forward
          (IteratedCarrier.embedFrom depth
            (IteratedCarrier.freshAtStep 0)) := by
  simpa [finiteConstitutivePersistenceRealization, finiteConstitutivePersistence] using
    (IteratedConstitutivePersistence.iteratedResidualOccurrence_persists P A depth)

/--
Persistence of the operational residual occurrence is natural across supplied
exact concrete realizations.
-/
theorem finiteOperationalResidualNaturality
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    {targetDepth : Nat}
    (depth : DepthExtension 1 targetDepth) :
    ((finiteConstitutivePersistenceRealization P A targetDepth).transport
        (finiteConstitutivePersistenceRealization P B targetDepth)).forward
        ((finiteConstitutivePersistenceRealization P A 1).extend
          (finiteConstitutivePersistenceRealization P A targetDepth)
          depth
          (ConstitutivePersistence.oneStepResidualConcreteOccurrence P A)) =
      (finiteConstitutivePersistenceRealization P B 1).extend
        (finiteConstitutivePersistenceRealization P B targetDepth)
        depth
        (ConstitutivePersistence.oneStepResidualConcreteOccurrence P B) := by
  simpa [finiteConstitutivePersistenceRealization, finiteConstitutivePersistence] using
    (IteratedConstitutivePersistence.iteratedResidualOccurrence_extension_transport_natural
      P A B depth)

/-- The finite depth `0 → 1` extension is pointwise the one-step old map. -/
theorem finiteDepthZeroOneExtensionMatchesOneStep
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (occurrence :
      (finiteConstitutivePersistenceRealization P A 0).Concrete) :
    (finiteConstitutivePersistenceRealization P A 0).extend
        (finiteConstitutivePersistenceRealization P A 1)
        (.step (.refl 0)) occurrence =
      (canonicalConstitutiveAlignmentRealization P A).old occurrence :=
  IteratedConstitutivePersistence.iteratedExtension_zero_one_eq_oneStep
    P A occurrence

/-- Change of realization is pointwise independent of an intermediate algebra. -/
theorem finiteTransportPathCoherence
    (P : CircularPresentation)
    (A B C : ConcreteContinuationAlgebra P)
    (depth : Nat)
    (occurrence :
      (finiteConstitutivePersistenceRealization P A depth).Concrete) :
    (((finiteConstitutivePersistenceRealization P B depth).transport
        (finiteConstitutivePersistenceRealization P C depth)).forward
      (((finiteConstitutivePersistenceRealization P A depth).transport
        (finiteConstitutivePersistenceRealization P B depth)).forward
        occurrence)) =
      (((finiteConstitutivePersistenceRealization P A depth).transport
        (finiteConstitutivePersistenceRealization P C depth)).forward
        occurrence) :=
  FiniteConstitutiveAlignment.Realization.transport_comp
    (finiteConstitutivePersistenceRealization P A depth)
    (finiteConstitutivePersistenceRealization P B depth)
    (finiteConstitutivePersistenceRealization P C depth)
    occurrence

/--
Any distinction made by a finitely assembled readout persists on the exact
concrete occurrences through every later circular stage.
-/
theorem finiteReadoutDistinctionPersists
    {Value : Type}
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (initialReadout :
      ConstitutivePersistence.InitialFreeOccurrence P → Value)
    {sourceDepth targetDepth : Nat}
    (depth : DepthExtension sourceDepth targetDepth)
    (targetValues : FiniteFreshValues Value targetDepth)
    (first second :
      (finiteConstitutivePersistenceRealization P A sourceDepth).Concrete)
    (distinguished :
      (finiteConstitutivePersistenceRealization P A sourceDepth).realizeReadout
          (iteratedReadout initialReadout
            (FiniteFreshValues.take depth targetValues)) first ≠
        (finiteConstitutivePersistenceRealization P A sourceDepth).realizeReadout
          (iteratedReadout initialReadout
            (FiniteFreshValues.take depth targetValues)) second) :
    (finiteConstitutivePersistenceRealization P A targetDepth).realizeReadout
          (iteratedReadout initialReadout targetValues)
          ((finiteConstitutivePersistenceRealization P A sourceDepth).extend
            (finiteConstitutivePersistenceRealization P A targetDepth)
            depth first) ≠
      (finiteConstitutivePersistenceRealization P A targetDepth).realizeReadout
          (iteratedReadout initialReadout targetValues)
          ((finiteConstitutivePersistenceRealization P A sourceDepth).extend
            (finiteConstitutivePersistenceRealization P A targetDepth)
            depth second) :=
  FiniteConstitutiveAlignment.Realization.realizeIteratedReadout_distinction
    initialReadout
    (finiteConstitutivePersistenceRealization P A sourceDepth)
    (finiteConstitutivePersistenceRealization P A targetDepth)
    depth targetValues first second distinguished

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
#print axioms StructuralEntrypoint.finiteConstitutivePersistence
#print axioms StructuralEntrypoint.finiteConstitutivePersistenceRealization
#print axioms StructuralEntrypoint.finiteExtensionRealizationNaturality
#print axioms StructuralEntrypoint.finiteExtensionWitnessIndependent
#print axioms StructuralEntrypoint.finiteExtensionWitnessIndependentAcrossRealizations
#print axioms StructuralEntrypoint.finiteDepthOneTransportMatchesOneStep
#print axioms StructuralEntrypoint.finiteDepthOneBackwardTransportMatchesOneStep
#print axioms StructuralEntrypoint.finiteDepthOneFreshMatchesOneStep
#print axioms StructuralEntrypoint.oneStepAlignmentFreshIsConsumedResidual
#print axioms StructuralEntrypoint.finiteOperationalResidualPersists
#print axioms StructuralEntrypoint.finiteOperationalResidualNaturality
#print axioms StructuralEntrypoint.finiteDepthZeroOneExtensionMatchesOneStep
#print axioms StructuralEntrypoint.finiteTransportPathCoherence
#print axioms StructuralEntrypoint.finiteReadoutDistinctionPersists
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
