import Alignment.ReadoutPersistence
import Cycle1.ConstitutivePersistence

/-!
# Iterated constitutive persistence in Cycle 1

This module instantiates finite constitutive persistence with the actual
Cycle 1 producer.  Starting from the canonical perimeter, every successor
history is obtained by `generate` followed by `appendGenerated`.  Its free
occurrences are indexed exactly by the initial perimeter occurrences together
with one fresh identity per generated step.

The generic alignment laws are therefore not merely inhabited by an abstract
finite carrier: they act on the histories and concrete interpretations already
constructed by Cycle 1.  Admission, specification, and readout values remain
outside this realization layer.
-/

namespace StrongPerimetralTurning
namespace IteratedConstitutivePersistence

/-! ## The actual finite Cycle 1 histories -/

/-- Iterate the real free producer from the canonical perimeter. -/
def iteratedHistory
    (P : CircularPresentation) : Nat → RootedGeneratedHistory P
  | 0 => perimeterDeployment P
  | n + 1 =>
      let previous := iteratedHistory P n
      appendGenerated previous (generate previous.endpoint)

@[simp] theorem iteratedHistory_zero
    (P : CircularPresentation) :
    iteratedHistory P 0 = perimeterDeployment P :=
  rfl

@[simp] theorem iteratedHistory_one
    (P : CircularPresentation) :
    iteratedHistory P 1 = oneStepAfterPerimeter P :=
  rfl

/-- The continuation generated at every finite stage has one occurrence. -/
def successorContinuationExactlyOne
    (P : CircularPresentation)
    (n : Nat) :
    History.ExactlyOne
      (History.extend History.root
        (generate (iteratedHistory P n).endpoint).2) :=
  .single (generate (iteratedHistory P n).endpoint).2

/--
The actual successor history splits exactly into all previous occurrences and
the single occurrence created by the next call to `generate`.
-/
def successorOccurrenceSplit
    (P : CircularPresentation)
    (n : Nat) :
    ExactTypeTransport
      (History.Occurrence (iteratedHistory P n).history ⊕ Unit)
      (History.Occurrence (iteratedHistory P (n + 1)).history) :=
  ConstitutivePersistence.History.appendExactlyOneOccurrenceTransport
    (iteratedHistory P n).history
    (successorContinuationExactlyOne P n)

@[simp] theorem successorOccurrenceSplit_old
    (P : CircularPresentation)
    (n : Nat)
    (occurrence : History.Occurrence (iteratedHistory P n).history) :
    (successorOccurrenceSplit P n).forward (.inl occurrence) =
      History.Occurrence.earlier occurrence :=
  rfl

@[simp] theorem successorOccurrenceSplit_fresh
    (P : CircularPresentation)
    (n : Nat) :
    (successorOccurrenceSplit P n).forward (.inr ()) =
      History.Occurrence.last :=
  rfl

/-! ## Exact indexing of every iterated history -/

/--
The canonical finite index is identified with the free occurrences of the
actual Cycle 1 history at every depth.
-/
def iteratedOccurrenceSpoke
    (P : CircularPresentation) :
    (n : Nat) →
      ExactTypeTransport
        (IteratedCarrier (ConstitutivePersistence.InitialFreeOccurrence P) n)
        (History.Occurrence (iteratedHistory P n).history)
  | 0 => ExactTypeTransport.reflexive _
  | n + 1 =>
      (IteratedCarrier.oneStepTransport
        (ConstitutivePersistence.InitialFreeOccurrence P) n).reverse
        |>.compose ((iteratedOccurrenceSpoke P n).sumUnit)
        |>.compose (successorOccurrenceSplit P n)

@[simp] theorem iteratedOccurrenceSpoke_zero_forward
    (P : CircularPresentation)
    (occurrence : ConstitutivePersistence.InitialFreeOccurrence P) :
    (iteratedOccurrenceSpoke P 0).forward occurrence = occurrence :=
  rfl

@[simp] theorem iteratedOccurrenceSpoke_previous
    (P : CircularPresentation)
    (n : Nat)
    (identity :
      IteratedCarrier
        (ConstitutivePersistence.InitialFreeOccurrence P) n) :
    (iteratedOccurrenceSpoke P (n + 1)).forward
        (IteratedCarrier.embedPrevious identity) =
      History.Occurrence.earlier
        ((iteratedOccurrenceSpoke P n).forward identity) :=
  rfl

@[simp] theorem iteratedOccurrenceSpoke_fresh
    (P : CircularPresentation)
    (n : Nat) :
    (iteratedOccurrenceSpoke P (n + 1)).forward
        (IteratedCarrier.freshAtStep n) =
      History.Occurrence.last :=
  rfl

/-- The real free occurrence carrier at one finite Cycle 1 depth. -/
def cycle1Alignment
    (P : CircularPresentation)
    (n : Nat) :
    FiniteConstitutiveAlignment
      (ConstitutivePersistence.InitialFreeOccurrence P) n :=
  { Carrier := History.Occurrence (iteratedHistory P n).history
    carrierSpoke := iteratedOccurrenceSpoke P n }

/-- The finite construction at depth one is the established canonical split. -/
theorem cycle1Alignment_one_forward
    (P : CircularPresentation)
    (identity :
      ConstitutivePersistence.InitialFreeOccurrence P ⊕ Unit) :
    (cycle1Alignment P 1).carrierSpoke.forward identity =
      (ConstitutivePersistence.freeOccurrenceSplit P).forward identity :=
  by
    cases identity with
    | inl occurrence => rfl
    | inr witness => cases witness; rfl

/-- The depth-one finite spoke also agrees backwards with the one-step split. -/
theorem cycle1Alignment_one_backward
    (P : CircularPresentation)
    (occurrence : ConstitutivePersistence.ExtendedFreeOccurrence P) :
    (cycle1Alignment P 1).carrierSpoke.backward occurrence =
      (ConstitutivePersistence.freeOccurrenceSplit P).backward occurrence :=
  ExactTypeTransport.backward_eq_of_forward_eq
    (cycle1Alignment P 1).carrierSpoke
    (ConstitutivePersistence.freeOccurrenceSplit P)
    (cycle1Alignment_one_forward P)
    occurrence

/-! ## Exact concrete realizations of the iterated histories -/

/-- Expose an exact interpretation as the transport it already contains. -/
def interpretationTransport
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {source target : PositiveConstitution P}
    {freeHistory : GeneratedHistory source target}
    {concreteHistory :
      History A.ConcreteStep (A.stateAt source) (A.stateAt target)}
    (interpretation :
      ExactHistoryInterpretation A freeHistory concreteHistory) :
    ExactTypeTransport
      (History.Occurrence freeHistory)
      (History.Occurrence concreteHistory) :=
  { forward := interpretation.forwardOccurrence
    backward := interpretation.backwardOccurrence
    forwardBackward := interpretation.forwardBackward
    backwardForward := interpretation.backwardForward }

/-- Every supplied concrete algebra realizes the actual history at depth `n`. -/
def cycle1Realization
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (n : Nat) :
    (cycle1Alignment P n).Realization :=
  { Concrete :=
      History.Occurrence (A.realizeHistory (iteratedHistory P n).history)
    spoke := interpretationTransport
      (exactlyInterpretHistory A (iteratedHistory P n).history) }

@[simp] theorem cycle1Realization_atIndex
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (n : Nat)
    (identity :
      IteratedCarrier
        (ConstitutivePersistence.InitialFreeOccurrence P) n) :
    (cycle1Realization P A n).indexedSpoke.forward identity =
      (exactlyInterpretHistory A (iteratedHistory P n).history).forwardOccurrence
        ((iteratedOccurrenceSpoke P n).forward identity) :=
  rfl

@[simp] theorem cycle1Realization_previous_isEarlier
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (n : Nat)
    (identity :
      IteratedCarrier
        (ConstitutivePersistence.InitialFreeOccurrence P) n) :
    (cycle1Realization P A (n + 1)).indexedSpoke.forward
        (IteratedCarrier.embedPrevious identity) =
      History.Occurrence.earlier
        ((cycle1Realization P A n).indexedSpoke.forward identity) :=
  rfl

@[simp] theorem cycle1Realization_fresh_isLast
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (n : Nat) :
    (cycle1Realization P A (n + 1)).indexedSpoke.forward
        (IteratedCarrier.freshAtStep n) =
      History.Occurrence.last :=
  rfl

/-! ## Two-axis coherence on the actual Cycle 1 producer -/

/--
Changing concrete realization commutes with finite constitutive extension for
the histories generated by Cycle 1.  The identity may originate at any earlier
depth, not only at the perimeter.
-/
theorem cycle1_extend_transport_natural
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    {sourceDepth targetDepth : Nat}
    (depth : DepthExtension sourceDepth targetDepth)
    (occurrence : (cycle1Realization P A sourceDepth).Concrete) :
    (((cycle1Realization P A targetDepth).transport
        (cycle1Realization P B targetDepth)).forward
      ((cycle1Realization P A sourceDepth).extend
        (cycle1Realization P A targetDepth) depth occurrence)) =
      (cycle1Realization P B sourceDepth).extend
        (cycle1Realization P B targetDepth) depth
        (((cycle1Realization P A sourceDepth).transport
          (cycle1Realization P B sourceDepth)).forward occurrence) :=
  FiniteConstitutiveAlignment.Realization.extend_transport_natural
    (cycle1Realization P A sourceDepth)
    (cycle1Realization P B sourceDepth)
    (cycle1Realization P A targetDepth)
    (cycle1Realization P B targetDepth)
    depth occurrence

/--
At depth one, finite horizontal transport is pointwise the established
one-step transport.  Thus the iterated construction conservatively extends the
earlier interface in both directions, not only at the level of carrier types.
-/
theorem cycle1Transport_one_eq_oneStep
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    (occurrence : (cycle1Realization P A 1).Concrete) :
    ((cycle1Realization P A 1).transport
        (cycle1Realization P B 1)).forward occurrence =
      ((ConstitutivePersistence.canonicalOneStepAlignmentRealization P A).extendedTransport
        (ConstitutivePersistence.canonicalOneStepAlignmentRealization P B)).forward
          occurrence := by
  have roundTrip :=
    (cycle1Alignment P 1).carrierSpoke.backwardForward
      ((ConstitutivePersistence.canonicalOneStepAlignmentRealization P A).extendedSpoke.backward
        occurrence)
  exact congrArg
    (ConstitutivePersistence.canonicalOneStepAlignmentRealization P B).extendedSpoke.forward
    roundTrip

/-- Depth `0 → 1` extension is pointwise the established one-step old map. -/
theorem cycle1Extension_zero_one_eq_oneStep
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (occurrence : (cycle1Realization P A 0).Concrete) :
    (cycle1Realization P A 0).extend
        (cycle1Realization P A 1) (.step (.refl 0)) occurrence =
      (ConstitutivePersistence.canonicalOneStepAlignmentRealization P A).old
        occurrence :=
  rfl

end IteratedConstitutivePersistence
end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.iteratedHistory
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.successorOccurrenceSplit
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.iteratedOccurrenceSpoke
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.cycle1Alignment_one_forward
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.cycle1Alignment_one_backward
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.cycle1Realization
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.cycle1_extend_transport_natural
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.cycle1Transport_one_eq_oneStep
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.cycle1Extension_zero_one_eq_oneStep
/- AXIOM_AUDIT_END -/
