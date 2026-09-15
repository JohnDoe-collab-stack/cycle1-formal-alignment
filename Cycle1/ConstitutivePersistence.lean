import StrongPerimetralTurning
import Alignment.Constitutive

/- Concrete interface components intentionally remain in distinct universes. -/
set_option linter.checkUnivs false

/-!
# Canonical one-step constitutive persistence

This module first treats the canonical transition from the exact perimeter to
its freely generated one-step continuation.  It keeps occurrence constitution,
exact concrete realization, operational admission, and specification
satisfaction as distinct layers.

No readout value participates in the constructions below.  Concrete-to-
concrete transports are induced through the shared free occurrence index.
-/

namespace StrongPerimetralTurning
namespace ConstitutivePersistence

universe uState uStep

/-! ## An exact occurrence split for a one-step append -/

/--
Appending an exactly-one history adds exactly one occurrence.  The sum records
the old occurrences on the left and the unique appended occurrence on the
right.  Both directions are computed structurally.
-/
def History.appendExactlyOneOccurrenceTransport
    {State : Type uState}
    {Step : State → State → Type uStep}
    {a b c : State}
    (firstHistory : History Step a b)
    {continuation : History Step b c}
    (one : History.ExactlyOne continuation) :
    ExactTypeTransport
      (History.Occurrence firstHistory ⊕ Unit)
      (History.Occurrence (History.append firstHistory continuation)) := by
  cases one with
  | single step =>
      exact
        { forward := fun occurrence =>
            match occurrence with
            | .inl old => .earlier old
            | .inr _ => .last
          backward := fun occurrence =>
            match occurrence with
            | .last => .inr ()
            | .earlier old => .inl old
          forwardBackward := by
            intro occurrence
            cases occurrence with
            | inl old => rfl
            | inr witness => cases witness; rfl
          backwardForward := by
            intro occurrence
            cases occurrence with
            | last => rfl
            | earlier old => rfl }

/-! ## Canonical free occurrences -/

abbrev InitialFreeOccurrence (P : CircularPresentation) :=
  History.Occurrence (perimeterHistory P)

abbrev ExtendedFreeOccurrence (P : CircularPresentation) :=
  History.Occurrence (oneStepAfterPerimeter P).history

abbrev InitialConcreteOccurrence
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :=
  History.Occurrence (A.realizeHistory (perimeterHistory P))

abbrev ExtendedConcreteOccurrence
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :=
  History.Occurrence
    (A.realizeHistory (oneStepAfterPerimeter P).history)

/-- The generated continuation after the perimeter has exactly one occurrence. -/
def oneStepContinuationExactlyOne
    (P : CircularPresentation) :
    History.ExactlyOne
      (oneStepAfterPerimeter_is_extension P).continuation :=
  .single (generate_after_perimeter P).2

/--
The exact free split of the canonical continuation into all prior occurrences
and its one new occurrence.
-/
def freeOccurrenceSplit
    (P : CircularPresentation) :
    ExactTypeTransport
      (InitialFreeOccurrence P ⊕ Unit)
      (ExtendedFreeOccurrence P) :=
  History.appendExactlyOneOccurrenceTransport
    (perimeterHistory P)
    (oneStepContinuationExactlyOne P)

/-- Embed an occurrence of the perimeter into its one-step continuation. -/
def oldFreeOccurrence
    (P : CircularPresentation) :
    InitialFreeOccurrence P → ExtendedFreeOccurrence P :=
  fun occurrence => (freeOccurrenceSplit P).forward (.inl occurrence)

/-- The unique occurrence added after the perimeter. -/
def newFreeOccurrence
    (P : CircularPresentation) :
    ExtendedFreeOccurrence P :=
  (freeOccurrenceSplit P).forward (.inr ())

theorem oldFreeOccurrence_injective
    (P : CircularPresentation) :
    Function.Injective (oldFreeOccurrence P) := by
  intro first second equality
  have classified := congrArg (freeOccurrenceSplit P).backward equality
  change Sum.inl first = Sum.inl second at classified
  exact Sum.inl.inj classified

theorem oldFreeOccurrence_ne_new
    (P : CircularPresentation)
    (occurrence : InitialFreeOccurrence P) :
    oldFreeOccurrence P occurrence ≠ newFreeOccurrence P := by
  intro equality
  have classified := congrArg (freeOccurrenceSplit P).backward equality
  change Sum.inl occurrence = Sum.inr () at classified
  cases classified

/-! ## Exact interpretation transports -/

private def exactTransportOfInterpretation
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

/-- Canonical exact interpretation of the perimeter history. -/
def initialInterpretation
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    ExactHistoryInterpretation
      A
      (perimeterHistory P)
      (A.realizeHistory (perimeterHistory P)) :=
  exactlyInterpretHistory A (perimeterHistory P)

/-- Canonical exact interpretation of the one-step extended history. -/
def extendedInterpretation
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    ExactHistoryInterpretation
      A
      (oneStepAfterPerimeter P).history
      (A.realizeHistory (oneStepAfterPerimeter P).history) :=
  exactlyInterpretHistory A (oneStepAfterPerimeter P).history

/-! ## The exact split in each concrete realization -/

/--
Every supplied concrete realization inherits the same exact old/new split from
the shared free occurrence index.
-/
def concreteOccurrenceSplit
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    ExactTypeTransport
      (InitialConcreteOccurrence P A ⊕ Unit)
      (ExtendedConcreteOccurrence P A) :=
  (exactTransportOfInterpretation (initialInterpretation P A)).reverse.sumUnit
    |>.compose (freeOccurrenceSplit P)
    |>.compose (exactTransportOfInterpretation (extendedInterpretation P A))

/-- The concrete image of an occurrence already present at the perimeter. -/
def concreteOldEmbedding
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    InitialConcreteOccurrence P A → ExtendedConcreteOccurrence P A :=
  fun occurrence => (concreteOccurrenceSplit P A).forward (.inl occurrence)

/-- The concrete image of the unique occurrence added after the perimeter. -/
def concreteNewOccurrence
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    ExtendedConcreteOccurrence P A :=
  (concreteOccurrenceSplit P A).forward (.inr ())

theorem concreteOldEmbedding_injective
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    Function.Injective (concreteOldEmbedding P A) := by
  intro first second equality
  unfold concreteOldEmbedding at equality
  have classified := congrArg (concreteOccurrenceSplit P A).backward equality
  rw [(concreteOccurrenceSplit P A).forwardBackward,
    (concreteOccurrenceSplit P A).forwardBackward] at classified
  exact Sum.inl.inj classified

theorem concreteOldEmbedding_ne_new
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (occurrence : InitialConcreteOccurrence P A) :
    concreteOldEmbedding P A occurrence ≠ concreteNewOccurrence P A := by
  intro equality
  unfold concreteOldEmbedding concreteNewOccurrence at equality
  have classified := congrArg (concreteOccurrenceSplit P A).backward equality
  rw [(concreteOccurrenceSplit P A).forwardBackward,
    (concreteOccurrenceSplit P A).forwardBackward] at classified
  cases classified

theorem concreteOldEmbedding_eq
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (occurrence : InitialConcreteOccurrence P A) :
    concreteOldEmbedding P A occurrence =
      (extendedInterpretation P A).forwardOccurrence
        (oldFreeOccurrence P
          ((initialInterpretation P A).backwardOccurrence occurrence)) := by
  rfl

theorem concreteNewOccurrence_eq
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    concreteNewOccurrence P A =
      (extendedInterpretation P A).forwardOccurrence
        (newFreeOccurrence P) := by
  rfl

/-!
The induced concrete split agrees with the native occurrence constructors of
the realized append.  The old equation uses the exact interpretation round
trip; the new equation is definitional.
-/

theorem concreteOldEmbedding_isEarlier
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (occurrence : InitialConcreteOccurrence P A) :
    concreteOldEmbedding P A occurrence =
      History.Occurrence.earlier occurrence := by
  rw [concreteOldEmbedding_eq]
  change
    History.Occurrence.earlier
        ((initialInterpretation P A).forwardOccurrence
          ((initialInterpretation P A).backwardOccurrence occurrence)) =
      History.Occurrence.earlier occurrence
  rw [(initialInterpretation P A).backwardForward]

theorem concreteNewOccurrence_isLast
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    concreteNewOccurrence P A = History.Occurrence.last := by
  rfl

/-! ## Transport between concrete realizations -/

/--
Coordinate the initial concrete occurrences of two realizations through their
shared free occurrence index.
-/
def initialConcreteTransport
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P) :
    ExactTypeTransport
      (InitialConcreteOccurrence P A)
      (InitialConcreteOccurrence P B) :=
  (exactTransportOfInterpretation (initialInterpretation P A)).reverse
    |>.compose (exactTransportOfInterpretation (initialInterpretation P B))

/--
Coordinate the extended concrete occurrences of two realizations through their
shared extended free occurrence index.
-/
def extendedConcreteTransport
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P) :
    ExactTypeTransport
      (ExtendedConcreteOccurrence P A)
      (ExtendedConcreteOccurrence P B) :=
  (exactTransportOfInterpretation (extendedInterpretation P A)).reverse
    |>.compose (exactTransportOfInterpretation (extendedInterpretation P B))

/-! ## Naturality of the one-step split -/

/--
Old occurrences commute with change of concrete realization.  Both routes are
induced by the same old free occurrence; no pairwise concrete matching is
supplied independently.
-/
theorem concreteOldEmbedding_natural
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    (occurrence : InitialConcreteOccurrence P A) :
    (extendedConcreteTransport P A B).forward
        (concreteOldEmbedding P A occurrence) =
      concreteOldEmbedding P B
        ((initialConcreteTransport P A B).forward occurrence) := by
  rw [concreteOldEmbedding_eq, concreteOldEmbedding_eq]
  change
    (extendedInterpretation P B).forwardOccurrence
        ((extendedInterpretation P A).backwardOccurrence
          ((extendedInterpretation P A).forwardOccurrence
            (oldFreeOccurrence P
              ((initialInterpretation P A).backwardOccurrence occurrence)))) =
      (extendedInterpretation P B).forwardOccurrence
        (oldFreeOccurrence P
          ((initialInterpretation P B).backwardOccurrence
            ((initialInterpretation P B).forwardOccurrence
              ((initialInterpretation P A).backwardOccurrence occurrence))))
  rw [(extendedInterpretation P A).forwardBackward]
  rw [(initialInterpretation P B).forwardBackward]

/-- The unique new occurrence also commutes with change of realization. -/
theorem concreteNewOccurrence_natural
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P) :
    (extendedConcreteTransport P A B).forward
        (concreteNewOccurrence P A) =
      concreteNewOccurrence P B := by
  rw [concreteNewOccurrence_eq, concreteNewOccurrence_eq]
  change
    (extendedInterpretation P B).forwardOccurrence
        ((extendedInterpretation P A).backwardOccurrence
          ((extendedInterpretation P A).forwardOccurrence
            (newFreeOccurrence P))) =
      (extendedInterpretation P B).forwardOccurrence (newFreeOccurrence P)
  rw [(extendedInterpretation P A).forwardBackward]

/-! ## Pointwise coherence -/

theorem initialConcreteTransport_refl
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (occurrence : InitialConcreteOccurrence P A) :
    (initialConcreteTransport P A A).forward occurrence = occurrence := by
  change
    (initialInterpretation P A).forwardOccurrence
        ((initialInterpretation P A).backwardOccurrence occurrence) = occurrence
  exact (initialInterpretation P A).backwardForward occurrence

theorem extendedConcreteTransport_refl
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (occurrence : ExtendedConcreteOccurrence P A) :
    (extendedConcreteTransport P A A).forward occurrence = occurrence := by
  change
    (extendedInterpretation P A).forwardOccurrence
        ((extendedInterpretation P A).backwardOccurrence occurrence) = occurrence
  exact (extendedInterpretation P A).backwardForward occurrence

theorem initialConcreteTransport_forward_comp
    (P : CircularPresentation)
    (A B C : ConcreteContinuationAlgebra P)
    (occurrence : InitialConcreteOccurrence P A) :
    (initialConcreteTransport P B C).forward
        ((initialConcreteTransport P A B).forward occurrence) =
      (initialConcreteTransport P A C).forward occurrence := by
  change
    (initialInterpretation P C).forwardOccurrence
        ((initialInterpretation P B).backwardOccurrence
          ((initialInterpretation P B).forwardOccurrence
            ((initialInterpretation P A).backwardOccurrence occurrence))) =
      (initialInterpretation P C).forwardOccurrence
        ((initialInterpretation P A).backwardOccurrence occurrence)
  rw [(initialInterpretation P B).forwardBackward]

theorem extendedConcreteTransport_forward_comp
    (P : CircularPresentation)
    (A B C : ConcreteContinuationAlgebra P)
    (occurrence : ExtendedConcreteOccurrence P A) :
    (extendedConcreteTransport P B C).forward
        ((extendedConcreteTransport P A B).forward occurrence) =
      (extendedConcreteTransport P A C).forward occurrence := by
  change
    (extendedInterpretation P C).forwardOccurrence
        ((extendedInterpretation P B).backwardOccurrence
          ((extendedInterpretation P B).forwardOccurrence
            ((extendedInterpretation P A).backwardOccurrence occurrence))) =
      (extendedInterpretation P C).forwardOccurrence
        ((extendedInterpretation P A).backwardOccurrence occurrence)
  rw [(extendedInterpretation P B).forwardBackward]

/-! ## Relative pointwise uniqueness -/

/--
A candidate transport is determined pointwise once its action agrees on every
old occurrence and on the unique new occurrence.  This is uniqueness relative
to the complete old/new split, not uniqueness of all exact transports without
these compatibility conditions.
-/
theorem extendedTransport_unique_at
    {P : CircularPresentation}
    {A B : ConcreteContinuationAlgebra P}
    (candidate :
      ExtendedConcreteOccurrence P A → ExtendedConcreteOccurrence P B)
    (onOld :
      (occurrence : InitialConcreteOccurrence P A) →
        candidate (concreteOldEmbedding P A occurrence) =
          concreteOldEmbedding P B
            ((initialConcreteTransport P A B).forward occurrence))
    (onNew :
      candidate (concreteNewOccurrence P A) =
        concreteNewOccurrence P B)
    (occurrence : ExtendedConcreteOccurrence P A) :
    candidate occurrence =
      (extendedConcreteTransport P A B).forward occurrence := by
  have reconstruction :=
    (concreteOccurrenceSplit P A).backwardForward occurrence
  generalize classificationEquality :
      (concreteOccurrenceSplit P A).backward occurrence = classification
  at reconstruction
  cases classification with
  | inl old =>
      change concreteOldEmbedding P A old = occurrence at reconstruction
      calc
        candidate occurrence =
            candidate (concreteOldEmbedding P A old) :=
          congrArg candidate reconstruction.symm
        _ = concreteOldEmbedding P B
              ((initialConcreteTransport P A B).forward old) :=
          onOld old
        _ = (extendedConcreteTransport P A B).forward
              (concreteOldEmbedding P A old) :=
          (concreteOldEmbedding_natural P A B old).symm
        _ = (extendedConcreteTransport P A B).forward occurrence :=
          congrArg (extendedConcreteTransport P A B).forward reconstruction

  | inr residual =>
      cases residual
      change concreteNewOccurrence P A = occurrence at reconstruction
      calc
        candidate occurrence = candidate (concreteNewOccurrence P A) :=
          congrArg candidate reconstruction.symm
        _ = concreteNewOccurrence P B := onNew
        _ = (extendedConcreteTransport P A B).forward
              (concreteNewOccurrence P A) :=
          (concreteNewOccurrence_natural P A B).symm
        _ = (extendedConcreteTransport P A B).forward occurrence :=
          congrArg (extendedConcreteTransport P A B).forward reconstruction

/-! ## Extraction into the content-independent alignment interface -/

/--
The canonical free one-step transition, viewed through the general exact
constitutive-alignment interface.
-/
def canonicalOneStepAlignment
    (P : CircularPresentation) :
    ExactOneStepConstitutiveAlignment :=
  { Initial := InitialFreeOccurrence P
    Extended := ExtendedFreeOccurrence P
    extension := freeOccurrenceSplit P }

/--
Every supplied concrete continuation algebra yields one exact realization of
the canonical constitutive alignment.  Admission and readout data are absent.
-/
def canonicalOneStepAlignmentRealization
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    (canonicalOneStepAlignment P).Realization :=
  { InitialConcrete := InitialConcreteOccurrence P A
    ExtendedConcrete := ExtendedConcreteOccurrence P A
    initialSpoke := exactTransportOfInterpretation (initialInterpretation P A)
    extendedSpoke := exactTransportOfInterpretation (extendedInterpretation P A) }

theorem canonicalAlignment_old_eq
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P)
    (occurrence : InitialConcreteOccurrence P A) :
    (canonicalOneStepAlignmentRealization P A).old occurrence =
      concreteOldEmbedding P A occurrence := by
  rfl

theorem canonicalAlignment_fresh_eq
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    (canonicalOneStepAlignmentRealization P A).fresh =
      concreteNewOccurrence P A := by
  rfl

theorem canonicalAlignment_concreteSplit_eq
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    (canonicalOneStepAlignmentRealization P A).concreteSplit =
      concreteOccurrenceSplit P A := by
  rfl

theorem canonicalAlignment_initialTransport_at
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    (occurrence : InitialConcreteOccurrence P A) :
    ((canonicalOneStepAlignmentRealization P A).initialTransport
      (canonicalOneStepAlignmentRealization P B)).forward occurrence =
      (initialConcreteTransport P A B).forward occurrence := by
  rfl

theorem canonicalAlignment_extendedTransport_at
    (P : CircularPresentation)
    (A B : ConcreteContinuationAlgebra P)
    (occurrence : ExtendedConcreteOccurrence P A) :
    ((canonicalOneStepAlignmentRealization P A).extendedTransport
      (canonicalOneStepAlignmentRealization P B)).forward occurrence =
      (extendedConcreteTransport P A B).forward occurrence := by
  rfl

/-! ## Operational meaning of the fresh alignment identity -/

/--
The residual occurrence determined directly by the Cycle 1 core, embedded into
the full free occurrence carrier used by the one-step constitutive alignment.
-/
def oneStepResidualFreeOccurrence
    (P : CircularPresentation) :
    ExtendedFreeOccurrence P :=
  (oneStepFaithfullyLabelledExtension P).newOccurrence
    (oneStepCoreResidualOccurrence P).occurrence

/--
In the actual Cycle 1 instance, the fresh constitutive identity is exactly the
full-history image of the core residual occurrence.
-/
theorem canonicalAlignment_fresh_eq_residualFreeOccurrence
    (P : CircularPresentation) :
    (canonicalOneStepAlignment P).fresh =
      oneStepResidualFreeOccurrence P := by
  rfl

/--
The same full-history occurrence is the residual occurrence consumed by the
published operational turning construction.
-/
theorem residualFreeOccurrence_agrees_with_consumedTurning
    (P : CircularPresentation) :
    oneStepResidualFreeOccurrence P =
      (oneStepFaithfullyLabelledExtension P).newOccurrence
        ((abstractTurningOfCircularPresentation P).uniqueResidualOccurrence.occurrence) := by
  unfold oneStepResidualFreeOccurrence
  exact congrArg
    (oneStepFaithfullyLabelledExtension P).newOccurrence
    (oneStepCoreResidualOccurrence_agrees_with_consumedTurning P)

/--
The fresh identity of the actual one-step Cycle 1 alignment carries the final
residual role.
-/
theorem canonicalAlignment_fresh_label_is_final
    (P : CircularPresentation) :
    (oneStepFaithfullyLabelledExtension P).label
        (canonicalOneStepAlignment P).fresh =
      .inr FinalRequirement.distinguished := by
  rw [canonicalAlignment_fresh_eq_residualFreeOccurrence]
  unfold oneStepResidualFreeOccurrence
  change
    (oneStepFaithfullyLabelledExtension P).label
        ((oneStepFaithfullyLabelledExtension P).newOccurrence
          (oneStepCoreResidualOccurrence P).occurrence) =
      .inr FinalRequirement.distinguished
  rfl

/--
Concrete realization of the operational residual identity in a supplied
continuation algebra.
-/
def oneStepResidualConcreteOccurrence
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    ExtendedConcreteOccurrence P A :=
  (extendedInterpretation P A).forwardOccurrence
    (oneStepResidualFreeOccurrence P)

/--
The fresh identity of every canonical realization induced by a supplied
`ConcreteContinuationAlgebra` is exactly the concrete realization of the
operational residual occurrence.
-/
theorem canonicalAlignmentRealization_fresh_eq_residualConcreteOccurrence
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    (canonicalOneStepAlignmentRealization P A).fresh =
      oneStepResidualConcreteOccurrence P A := by
  change
    (extendedInterpretation P A).forwardOccurrence
        (canonicalOneStepAlignment P).fresh =
      (extendedInterpretation P A).forwardOccurrence
        (oneStepResidualFreeOccurrence P)
  exact congrArg
    (extendedInterpretation P A).forwardOccurrence
    (canonicalAlignment_fresh_eq_residualFreeOccurrence P)

/-! ## Status remains a separate layer -/

universe uE uI uK uD uP uEnd uLoop
universe vA vB vC vF vG vH vJ

private abbrev ConcreteAlgebraFamily
    (P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}) :=
  ConcreteContinuationAlgebra.{uE, uI, uK, uD, vA, vB, vC, vF,
    vG, vH, vJ, uE, uI, uK, uD, uP, uEnd, uLoop} P

/--
The canonical extension preserves exact realizability while changing both its
operational and specification-relative status.  These fields are deliberately
separate from the occurrence transports above.
-/
structure OneStepPersistenceStatus
    (P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}) : Type _ where
  initialAdmissible :
    CircularRefinement P (perimeterDeployment P)
  initialSatisfiesSpecification :
    CircularSpecificationSatisfaction P (perimeterDeployment P)
  initialExactlyRealizable :
    (A : ConcreteAlgebraFamily.{uE, uI, uK, uD, uP, uEnd, uLoop,
      vA, vB, vC, vF, vG, vH, vJ} P) →
      ExactConcreteRealization A (perimeterDeployment P)
  extendedExactlyRealizable :
    (A : ConcreteAlgebraFamily.{uE, uI, uK, uD, uP, uEnd, uLoop,
      vA, vB, vC, vF, vG, vH, vJ} P) →
      ExactConcreteRealization A (oneStepAfterPerimeter P)
  extendedInadmissible :
    CircularRefinement P (oneStepAfterPerimeter P) → False
  extendedOutsideSpecification :
    CircularSpecificationSatisfaction P (oneStepAfterPerimeter P) → False

def oneStepPersistenceStatus
    (P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}) :
    OneStepPersistenceStatus.{uE, uI, uK, uD, uP, uEnd, uLoop,
      vA, vB, vC, vF, vG, vH, vJ} P :=
  { initialAdmissible := identityCircularRefinement P
    initialSatisfiesSpecification :=
      perimeterDeployment_specificationSatisfaction P
    initialExactlyRealizable := fun A =>
      exactlyInterpretHistory A (perimeterDeployment P).history
    extendedExactlyRealizable := fun A =>
      exactlyInterpretHistory A (oneStepAfterPerimeter P).history
    extendedInadmissible := oneStepAfterPerimeter_notCircularRefinement P
    extendedOutsideSpecification :=
      oneStepAfterPerimeter_notSpecificationSatisfaction P }

/-! ## Canonical persistence certificate -/

/--
The laws that make the one-step construction persistent across arbitrary
supplied concrete realizations.  The exact splits and transports themselves
remain inspectable as the canonical definitions above.
-/
structure OneStepConstitutivePersistence
    (P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}) : Type _ where
  oldNaturality :
    (A B : ConcreteAlgebraFamily.{uE, uI, uK, uD, uP, uEnd, uLoop,
      vA, vB, vC, vF, vG, vH, vJ} P) →
    (occurrence : InitialConcreteOccurrence P A) →
      (extendedConcreteTransport P A B).forward
          (concreteOldEmbedding P A occurrence) =
        concreteOldEmbedding P B
          ((initialConcreteTransport P A B).forward occurrence)
  newNaturality :
    (A B : ConcreteAlgebraFamily.{uE, uI, uK, uD, uP, uEnd, uLoop,
      vA, vB, vC, vF, vG, vH, vJ} P) →
      (extendedConcreteTransport P A B).forward
          (concreteNewOccurrence P A) =
        concreteNewOccurrence P B
  initialPathCoherence :
    (A B C : ConcreteAlgebraFamily.{uE, uI, uK, uD, uP, uEnd, uLoop,
      vA, vB, vC, vF, vG, vH, vJ} P) →
    (occurrence : InitialConcreteOccurrence P A) →
      (initialConcreteTransport P B C).forward
          ((initialConcreteTransport P A B).forward occurrence) =
        (initialConcreteTransport P A C).forward occurrence
  extendedPathCoherence :
    (A B C : ConcreteAlgebraFamily.{uE, uI, uK, uD, uP, uEnd, uLoop,
      vA, vB, vC, vF, vG, vH, vJ} P) →
    (occurrence : ExtendedConcreteOccurrence P A) →
      (extendedConcreteTransport P B C).forward
          ((extendedConcreteTransport P A B).forward occurrence) =
        (extendedConcreteTransport P A C).forward occurrence
  status : OneStepPersistenceStatus.{uE, uI, uK, uD, uP, uEnd, uLoop,
    vA, vB, vC, vF, vG, vH, vJ} P

/-- The canonical one-step constitutive persistence certificate. -/
def oneStepConstitutivePersistence
    (P : CircularPresentation.{uE, uI, uK, uD, uP, uEnd, uLoop}) :
    OneStepConstitutivePersistence.{uE, uI, uK, uD, uP, uEnd, uLoop,
      vA, vB, vC, vF, vG, vH, vJ} P :=
  { oldNaturality := concreteOldEmbedding_natural P
    newNaturality := concreteNewOccurrence_natural P
    initialPathCoherence := initialConcreteTransport_forward_comp P
    extendedPathCoherence := extendedConcreteTransport_forward_comp P
    status := oneStepPersistenceStatus.{uE, uI, uK, uD, uP, uEnd, uLoop,
      vA, vB, vC, vF, vG, vH, vJ} P }

end ConstitutivePersistence
end StrongPerimetralTurning

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.ConstitutivePersistence.History.appendExactlyOneOccurrenceTransport
#print axioms StrongPerimetralTurning.ConstitutivePersistence.freeOccurrenceSplit
#print axioms StrongPerimetralTurning.ConstitutivePersistence.oldFreeOccurrence_injective
#print axioms StrongPerimetralTurning.ConstitutivePersistence.oldFreeOccurrence_ne_new
#print axioms StrongPerimetralTurning.ConstitutivePersistence.initialInterpretation
#print axioms StrongPerimetralTurning.ConstitutivePersistence.extendedInterpretation
#print axioms StrongPerimetralTurning.ConstitutivePersistence.concreteOccurrenceSplit
#print axioms StrongPerimetralTurning.ConstitutivePersistence.concreteOldEmbedding_injective
#print axioms StrongPerimetralTurning.ConstitutivePersistence.concreteOldEmbedding_ne_new
#print axioms StrongPerimetralTurning.ConstitutivePersistence.concreteOldEmbedding_isEarlier
#print axioms StrongPerimetralTurning.ConstitutivePersistence.concreteNewOccurrence_isLast
#print axioms StrongPerimetralTurning.ConstitutivePersistence.concreteOldEmbedding_natural
#print axioms StrongPerimetralTurning.ConstitutivePersistence.concreteNewOccurrence_natural
#print axioms StrongPerimetralTurning.ConstitutivePersistence.initialConcreteTransport_refl
#print axioms StrongPerimetralTurning.ConstitutivePersistence.extendedConcreteTransport_refl
#print axioms StrongPerimetralTurning.ConstitutivePersistence.initialConcreteTransport_forward_comp
#print axioms StrongPerimetralTurning.ConstitutivePersistence.extendedConcreteTransport_forward_comp
#print axioms StrongPerimetralTurning.ConstitutivePersistence.extendedTransport_unique_at
#print axioms StrongPerimetralTurning.ConstitutivePersistence.canonicalOneStepAlignment
#print axioms StrongPerimetralTurning.ConstitutivePersistence.canonicalOneStepAlignmentRealization
#print axioms StrongPerimetralTurning.ConstitutivePersistence.canonicalAlignment_old_eq
#print axioms StrongPerimetralTurning.ConstitutivePersistence.canonicalAlignment_fresh_eq
#print axioms StrongPerimetralTurning.ConstitutivePersistence.canonicalAlignment_concreteSplit_eq
#print axioms StrongPerimetralTurning.ConstitutivePersistence.canonicalAlignment_initialTransport_at
#print axioms StrongPerimetralTurning.ConstitutivePersistence.canonicalAlignment_extendedTransport_at
#print axioms StrongPerimetralTurning.ConstitutivePersistence.oneStepResidualFreeOccurrence
#print axioms StrongPerimetralTurning.ConstitutivePersistence.canonicalAlignment_fresh_eq_residualFreeOccurrence
#print axioms StrongPerimetralTurning.ConstitutivePersistence.residualFreeOccurrence_agrees_with_consumedTurning
#print axioms StrongPerimetralTurning.ConstitutivePersistence.canonicalAlignment_fresh_label_is_final
#print axioms StrongPerimetralTurning.ConstitutivePersistence.oneStepResidualConcreteOccurrence
#print axioms StrongPerimetralTurning.ConstitutivePersistence.canonicalAlignmentRealization_fresh_eq_residualConcreteOccurrence
#print axioms StrongPerimetralTurning.ConstitutivePersistence.OneStepPersistenceStatus
#print axioms StrongPerimetralTurning.ConstitutivePersistence.oneStepPersistenceStatus
#print axioms StrongPerimetralTurning.ConstitutivePersistence.OneStepConstitutivePersistence
#print axioms StrongPerimetralTurning.ConstitutivePersistence.oneStepConstitutivePersistence
/- AXIOM_AUDIT_END -/
