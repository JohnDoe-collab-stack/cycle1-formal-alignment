import Alignment.ReadoutPersistence
import StrongPerimetralTurning.ConstitutivePersistence

open Alignment

/-!
# Iterated constitutive persistence in the circular instance

This module instantiates finite constitutive persistence with the actual
circular instance producer.  Starting from the canonical perimeter, every successor
history is obtained by `generate` followed by `appendGenerated`.  Its free
occurrences are indexed exactly by the initial perimeter occurrences together
with one fresh identity per generated step.

The generic alignment laws are therefore not merely inhabited by an abstract
finite carrier: they act on the histories and concrete interpretations already
constructed by the circular instance.  Admission, specification, and readout values remain
outside this realization layer.
-/

namespace StrongPerimetralTurning
namespace IteratedConstitutivePersistence

/-! ## The actual finite circular histories -/

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
actual circular instance history at every depth.
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

/-- The real free occurrence carrier at one finite circular depth. -/
def iteratedAlignment
    (P : CircularPresentation)
    (n : Nat) :
    FiniteConstitutiveAlignment
      (ConstitutivePersistence.InitialFreeOccurrence P) n :=
  { Carrier := History.Occurrence (iteratedHistory P n).history
    carrierSpoke := iteratedOccurrenceSpoke P n }

/-- The finite construction at depth one is the established canonical split. -/
theorem iteratedAlignment_one_forward
    (P : CircularPresentation)
    (identity :
      ConstitutivePersistence.InitialFreeOccurrence P ⊕ Unit) :
    (iteratedAlignment P 1).carrierSpoke.forward identity =
      (ConstitutivePersistence.freeOccurrenceSplit P).forward identity :=
  by
    cases identity with
    | inl occurrence => rfl
    | inr witness => cases witness; rfl

/-- The depth-one finite spoke also agrees backwards with the one-step split. -/
theorem iteratedAlignment_one_backward
    (P : CircularPresentation)
    (occurrence : ConstitutivePersistence.ExtendedFreeOccurrence P) :
    (iteratedAlignment P 1).carrierSpoke.backward occurrence =
      (ConstitutivePersistence.freeOccurrenceSplit P).backward occurrence :=
  ExactTypeTransport.backward_eq_of_forward_eq
    (iteratedAlignment P 1).carrierSpoke
    (ConstitutivePersistence.freeOccurrenceSplit P)
    (iteratedAlignment_one_forward P)
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
def iteratedRealization
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (n : Nat) :
    (iteratedAlignment P n).Realization :=
  { Concrete :=
      History.Occurrence (A.realizeHistory (iteratedHistory P n).history)
    spoke := interpretationTransport
      (exactlyInterpretHistory A (iteratedHistory P n).history) }

@[simp] theorem iteratedRealization_atIndex
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (n : Nat)
    (identity :
      IteratedCarrier
        (ConstitutivePersistence.InitialFreeOccurrence P) n) :
    (iteratedRealization P A n).indexedSpoke.forward identity =
      (exactlyInterpretHistory A (iteratedHistory P n).history).forwardOccurrence
        ((iteratedOccurrenceSpoke P n).forward identity) :=
  rfl

@[simp] theorem iteratedRealization_previous_isEarlier
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (n : Nat)
    (identity :
      IteratedCarrier
        (ConstitutivePersistence.InitialFreeOccurrence P) n) :
    (iteratedRealization P A (n + 1)).indexedSpoke.forward
        (IteratedCarrier.embedPrevious identity) =
      History.Occurrence.earlier
        ((iteratedRealization P A n).indexedSpoke.forward identity) :=
  rfl

@[simp] theorem iteratedRealization_fresh_isLast
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (n : Nat) :
    (iteratedRealization P A (n + 1)).indexedSpoke.forward
        (IteratedCarrier.freshAtStep n) =
      History.Occurrence.last :=
  rfl

/-! ## Two-axis coherence on the actual circular producer -/

/--
Changing concrete realization commutes with finite constitutive extension for
the histories generated by the circular instance.  The identity may originate at any earlier
depth, not only at the perimeter.
-/
theorem iterated_extend_transport_natural
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    {sourceDepth targetDepth : Nat}
    (depth : DepthExtension sourceDepth targetDepth)
    (occurrence : (iteratedRealization P A sourceDepth).Concrete) :
    (((iteratedRealization P A targetDepth).transport
        (iteratedRealization P B targetDepth)).forward
      ((iteratedRealization P A sourceDepth).extend
        (iteratedRealization P A targetDepth) depth occurrence)) =
      (iteratedRealization P B sourceDepth).extend
        (iteratedRealization P B targetDepth) depth
        (((iteratedRealization P A sourceDepth).transport
          (iteratedRealization P B sourceDepth)).forward occurrence) :=
  FiniteConstitutiveAlignment.Realization.extend_transport_natural
    (iteratedRealization P A sourceDepth)
    (iteratedRealization P B sourceDepth)
    (iteratedRealization P A targetDepth)
    (iteratedRealization P B targetDepth)
    depth occurrence

/--
Finite extension between two supplied concrete realizations depends only on
its source and target depths, not on the `DepthExtension` witness.
-/
theorem iteratedExtension_witness_independent
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    {sourceDepth targetDepth : Nat}
    (first second : DepthExtension sourceDepth targetDepth)
    (occurrence : (iteratedRealization P A sourceDepth).Concrete) :
    (iteratedRealization P A sourceDepth).extend
        (iteratedRealization P B targetDepth) first occurrence =
      (iteratedRealization P A sourceDepth).extend
        (iteratedRealization P B targetDepth) second occurrence :=
  FiniteConstitutiveAlignment.Realization.extend_witness_independent
    (iteratedRealization P A sourceDepth)
    (iteratedRealization P B targetDepth)
    first second occurrence

/--
At depth one, finite horizontal transport is pointwise the established
one-step transport.  Thus the iterated construction conservatively extends the
earlier interface in both directions, not only at the level of carrier types.
-/
theorem iteratedTransport_one_eq_oneStep
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    (occurrence : (iteratedRealization P A 1).Concrete) :
    ((iteratedRealization P A 1).transport
        (iteratedRealization P B 1)).forward occurrence =
      ((ConstitutivePersistence.canonicalOneStepAlignmentRealization P A).extendedTransport
        (ConstitutivePersistence.canonicalOneStepAlignmentRealization P B)).forward
          occurrence := by
  have roundTrip :=
    (iteratedAlignment P 1).carrierSpoke.backwardForward
      ((ConstitutivePersistence.canonicalOneStepAlignmentRealization P A).extendedSpoke.backward
        occurrence)
  exact congrArg
    (ConstitutivePersistence.canonicalOneStepAlignmentRealization P B).extendedSpoke.forward
    roundTrip

/--
At depth one, the backward finite horizontal transport is pointwise the
backward map of the established one-step transport.
-/
theorem iteratedTransport_one_backward_eq_oneStep
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    (occurrence : (iteratedRealization P B 1).Concrete) :
    ((iteratedRealization P A 1).transport
        (iteratedRealization P B 1)).backward occurrence =
      ((ConstitutivePersistence.canonicalOneStepAlignmentRealization P A).extendedTransport
        (ConstitutivePersistence.canonicalOneStepAlignmentRealization P B)).backward
          occurrence :=
  ExactTypeTransport.backward_eq_of_forward_eq
    ((iteratedRealization P A 1).transport (iteratedRealization P B 1))
    ((ConstitutivePersistence.canonicalOneStepAlignmentRealization P A).extendedTransport
      (ConstitutivePersistence.canonicalOneStepAlignmentRealization P B))
    (iteratedTransport_one_eq_oneStep P A B)
    occurrence

/-- The finite fresh identity at depth one is the established one-step fresh identity. -/
theorem iteratedRealization_one_fresh_eq_oneStep
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    (iteratedRealization P A 1).indexedSpoke.forward
        (IteratedCarrier.freshAtStep 0) =
      (ConstitutivePersistence.canonicalOneStepAlignmentRealization P A).fresh :=
  rfl

/-! ## Persistence of the operational residual identity -/

/--
At depth one, the fresh identity of the finite circular realization is exactly
the concrete operational residual occurrence.
-/
theorem iteratedRealization_one_fresh_eq_residual
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    (iteratedRealization P A 1).indexedSpoke.forward
        (IteratedCarrier.freshAtStep 0) =
      ConstitutivePersistence.oneStepResidualConcreteOccurrence P A :=
  (iteratedRealization_one_fresh_eq_oneStep P A).trans
    (ConstitutivePersistence.canonicalAlignmentRealization_fresh_eq_residualConcreteOccurrence P A)

/--
The concrete operational residual identity is preserved by change of exact
realization at depth one.
-/
theorem iteratedResidualOccurrence_transport_natural
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P) :
    ((iteratedRealization P A 1).transport
        (iteratedRealization P B 1)).forward
        (ConstitutivePersistence.oneStepResidualConcreteOccurrence P A) =
      ConstitutivePersistence.oneStepResidualConcreteOccurrence P B := by
  rw [← iteratedRealization_one_fresh_eq_residual P A]
  exact
    (FiniteConstitutiveAlignment.Realization.transport_atIndex
      (iteratedRealization P A 1)
      (iteratedRealization P B 1)
      (IteratedCarrier.freshAtStep 0)).trans
      (iteratedRealization_one_fresh_eq_residual P B)

/--
Once the first operational residual occurrence has been constituted, that
identity persists through every later finite circular depth.
-/
theorem iteratedResidualOccurrence_persists
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    {targetDepth : Nat}
    (depth : DepthExtension 1 targetDepth) :
    (iteratedRealization P A 1).extend
        (iteratedRealization P A targetDepth)
        depth
        (ConstitutivePersistence.oneStepResidualConcreteOccurrence P A) =
      (iteratedRealization P A targetDepth).indexedSpoke.forward
        (IteratedCarrier.embedFrom depth
          (IteratedCarrier.freshAtStep 0)) := by
  calc
    (iteratedRealization P A 1).extend
        (iteratedRealization P A targetDepth)
        depth
        (ConstitutivePersistence.oneStepResidualConcreteOccurrence P A) =
      (iteratedRealization P A 1).extend
        (iteratedRealization P A targetDepth)
        depth
        ((iteratedRealization P A 1).indexedSpoke.forward
          (IteratedCarrier.freshAtStep 0)) :=
      congrArg
        ((iteratedRealization P A 1).extend
          (iteratedRealization P A targetDepth) depth)
        (iteratedRealization_one_fresh_eq_residual P A).symm
    _ =
      (iteratedRealization P A targetDepth).indexedSpoke.forward
        (IteratedCarrier.embedFrom depth
          (IteratedCarrier.freshAtStep 0)) :=
      FiniteConstitutiveAlignment.Realization.extend_atIndex
        (iteratedRealization P A 1)
        (iteratedRealization P A targetDepth)
        depth
        (IteratedCarrier.freshAtStep 0)

/--
Persistence of the operational residual identity commutes with change of exact
concrete realization.
-/
theorem iteratedResidualOccurrence_extension_transport_natural
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    {targetDepth : Nat}
    (depth : DepthExtension 1 targetDepth) :
    ((iteratedRealization P A targetDepth).transport
        (iteratedRealization P B targetDepth)).forward
        ((iteratedRealization P A 1).extend
          (iteratedRealization P A targetDepth)
          depth
          (ConstitutivePersistence.oneStepResidualConcreteOccurrence P A)) =
      (iteratedRealization P B 1).extend
        (iteratedRealization P B targetDepth)
        depth
        (ConstitutivePersistence.oneStepResidualConcreteOccurrence P B) := by
  calc
    ((iteratedRealization P A targetDepth).transport
        (iteratedRealization P B targetDepth)).forward
        ((iteratedRealization P A 1).extend
          (iteratedRealization P A targetDepth)
          depth
          (ConstitutivePersistence.oneStepResidualConcreteOccurrence P A)) =
      (iteratedRealization P B 1).extend
        (iteratedRealization P B targetDepth)
        depth
        (((iteratedRealization P A 1).transport
          (iteratedRealization P B 1)).forward
          (ConstitutivePersistence.oneStepResidualConcreteOccurrence P A)) :=
      iterated_extend_transport_natural
        P A B depth
        (ConstitutivePersistence.oneStepResidualConcreteOccurrence P A)
    _ =
      (iteratedRealization P B 1).extend
        (iteratedRealization P B targetDepth)
        depth
        (ConstitutivePersistence.oneStepResidualConcreteOccurrence P B) :=
      congrArg
        ((iteratedRealization P B 1).extend
          (iteratedRealization P B targetDepth) depth)
        (iteratedResidualOccurrence_transport_natural P A B)

/-- Depth `0 → 1` extension is pointwise the established one-step old map. -/
theorem iteratedExtension_zero_one_eq_oneStep
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (occurrence : (iteratedRealization P A 0).Concrete) :
    (iteratedRealization P A 0).extend
        (iteratedRealization P A 1) (.step (.refl 0)) occurrence =
      (ConstitutivePersistence.canonicalOneStepAlignmentRealization P A).old
        occurrence :=
  rfl

end IteratedConstitutivePersistence
end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.iteratedHistory
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.successorOccurrenceSplit
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.iteratedOccurrenceSpoke
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.iteratedAlignment_one_forward
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.iteratedAlignment_one_backward
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.iteratedRealization
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.iterated_extend_transport_natural
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.iteratedExtension_witness_independent
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.iteratedTransport_one_eq_oneStep
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.iteratedTransport_one_backward_eq_oneStep
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.iteratedRealization_one_fresh_eq_oneStep
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.iteratedRealization_one_fresh_eq_residual
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.iteratedResidualOccurrence_transport_natural
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.iteratedResidualOccurrence_persists
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.iteratedResidualOccurrence_extension_transport_natural
#print axioms StrongPerimetralTurning.IteratedConstitutivePersistence.iteratedExtension_zero_one_eq_oneStep
/- AXIOM_AUDIT_END -/
