import Cycle1.IteratedConstitutivePersistence
import Examples.ConcreteContinuation.LoggedAlgebra

/-!
# A non-constant readout across several Cycle 1 extensions

This closed example instantiates the finite persistence laws at three generated
steps beyond the perimeter.  The first, second, and third fresh identities
receive distinct natural-number values.  The same indexed values are then read
in both the free example algebra and the non-identity logged algebra.

The numbers neither constitute nor align the occurrences.  They witness, only
after constitution and exact transport, that a non-constant readout can retain
distinctions across several extensions and across distinct realizations.
-/

namespace StrongPerimetralTurning.Examples.Alignment.IteratedReadout

open StrongPerimetralTurning.Example
open StrongPerimetralTurning.IteratedConstitutivePersistence
open StrongPerimetralTurning.Examples.ConcreteContinuation.LoggedAlgebra

abbrev InitialOccurrence :=
  ConstitutivePersistence.InitialFreeOccurrence examplePresentation

/-- A structural depth for the finite non-closing perimeter positions. -/
def positionDepth :
    {node : LocalNode
      Example.Explicit Example.Implicit Example.Compatible
      Example.Difference Example.Provenance} →
    {spine : PerimeterSpine Example.Compatible node} →
    NonClosingPosition spine → Nat
  | _, _, .here => 0
  | _, _, .later position => positionDepth position + 1

/-- A non-constant initial readout, attached only after occurrence constitution. -/
def initialReadout : InitialOccurrence → Nat :=
  fun occurrence =>
    7 + 4 * positionDepth
      (occurrenceToRequirement examplePresentation occurrence)

/-- Three independently supplied, pairwise distinct extension values. -/
def valuesAtThree : FiniteFreshValues Nat 3 :=
  (((PUnit.unit, 10), 20), 30)

def oneToThree : DepthExtension 1 3 :=
  .step (.step (.refl 1))

def twoToThree : DepthExtension 2 3 :=
  .step (.refl 2)

def zeroToThree : DepthExtension 0 3 :=
  .step (.step (.step (.refl 0)))

def firstInitial : IteratedCarrier InitialOccurrence 0 :=
  requirementToOccurrence examplePresentation exampleP1

def secondInitial : IteratedCarrier InitialOccurrence 0 :=
  requirementToOccurrence examplePresentation exampleP2

def firstInitialAtThree : IteratedCarrier InitialOccurrence 3 :=
  IteratedCarrier.embedFrom zeroToThree firstInitial

def secondInitialAtThree : IteratedCarrier InitialOccurrence 3 :=
  IteratedCarrier.embedFrom zeroToThree secondInitial

def firstFreshAtOne : IteratedCarrier InitialOccurrence 1 :=
  IteratedCarrier.freshAtStep 0

def secondFreshAtTwo : IteratedCarrier InitialOccurrence 2 :=
  IteratedCarrier.freshAtStep 1

def thirdFreshAtThree : IteratedCarrier InitialOccurrence 3 :=
  IteratedCarrier.freshAtStep 2

def firstFreshAtThree : IteratedCarrier InitialOccurrence 3 :=
  IteratedCarrier.embedFrom oneToThree firstFreshAtOne

def secondFreshAtThree : IteratedCarrier InitialOccurrence 3 :=
  IteratedCarrier.embedFrom twoToThree secondFreshAtTwo

@[simp] theorem firstInitial_value :
    iteratedReadout initialReadout valuesAtThree firstInitialAtThree = 7 :=
  rfl

@[simp] theorem secondInitial_value :
    iteratedReadout initialReadout valuesAtThree secondInitialAtThree = 11 :=
  rfl

@[simp] theorem firstFresh_value :
    iteratedReadout initialReadout valuesAtThree firstFreshAtThree = 10 :=
  rfl

@[simp] theorem secondFresh_value :
    iteratedReadout initialReadout valuesAtThree secondFreshAtThree = 20 :=
  rfl

@[simp] theorem thirdFresh_value :
    iteratedReadout initialReadout valuesAtThree thirdFreshAtThree = 30 :=
  rfl

/-- The readout is observably non-constant after several generated steps. -/
theorem first_second_distinguished :
    iteratedReadout initialReadout valuesAtThree firstFreshAtThree ≠
      iteratedReadout initialReadout valuesAtThree secondFreshAtThree := by
  change (10 : Nat) ≠ 20
  decide

/-- A distinction already present at the perimeter survives all three steps. -/
theorem initial_distinction_persists :
    iteratedReadout initialReadout valuesAtThree firstInitialAtThree ≠
      iteratedReadout initialReadout valuesAtThree secondInitialAtThree := by
  apply iteratedReadout_distinction initialReadout zeroToThree valuesAtThree
  change (7 : Nat) ≠ 11
  decide

/-- The earlier distinction also follows from the general persistence law. -/
theorem first_second_distinction_persists :
    iteratedReadout initialReadout valuesAtThree
        (IteratedCarrier.embedFrom twoToThree
          (IteratedCarrier.embedPrevious firstFreshAtOne)) ≠
      iteratedReadout initialReadout valuesAtThree
        (IteratedCarrier.embedFrom twoToThree secondFreshAtTwo) := by
  apply iteratedReadout_distinction initialReadout twoToThree valuesAtThree
  change (10 : Nat) ≠ 20
  decide

/-! ## The same values in two genuinely different concrete realizations -/

abbrev FreeRealization (n : Nat) :=
  cycle1Realization examplePresentation exampleConcreteAlgebra n

abbrev LoggedRealization (n : Nat) :=
  cycle1Realization examplePresentation loggedConcreteAlgebra n

def freeReadoutAtThree : (FreeRealization 3).Concrete → Nat :=
  (FreeRealization 3).realizeReadout
    (iteratedReadout initialReadout valuesAtThree)

def loggedReadoutAtThree : (LoggedRealization 3).Concrete → Nat :=
  (LoggedRealization 3).realizeReadout
    (iteratedReadout initialReadout valuesAtThree)

/-- Horizontal transport is induced by the shared constitutive index. -/
theorem free_to_logged_atIndex
    (identity : IteratedCarrier InitialOccurrence 3) :
    ((FreeRealization 3).transport (LoggedRealization 3)).forward
        ((FreeRealization 3).indexedSpoke.forward identity) =
      (LoggedRealization 3).indexedSpoke.forward identity :=
  FiniteConstitutiveAlignment.Realization.transport_atIndex
    (FreeRealization 3) (LoggedRealization 3) identity

/-- Readouts derived from the same value assignment agree at every shared index. -/
theorem concreteReadouts_agree_atIndex
    (identity : IteratedCarrier InitialOccurrence 3) :
    freeReadoutAtThree
        ((FreeRealization 3).indexedSpoke.forward identity) =
      loggedReadoutAtThree
        ((LoggedRealization 3).indexedSpoke.forward identity) := by
  unfold freeReadoutAtThree loggedReadoutAtThree
  rw [FiniteConstitutiveAlignment.Realization.realizeReadout_atIndex]
  rw [FiniteConstitutiveAlignment.Realization.realizeReadout_atIndex]

/-- The non-identity logged realization observes the retained first value. -/
theorem logged_firstFresh_value :
    loggedReadoutAtThree
        ((LoggedRealization 3).indexedSpoke.forward firstFreshAtThree) = 10 := by
  unfold loggedReadoutAtThree
  rw [FiniteConstitutiveAlignment.Realization.realizeReadout_atIndex]
  rfl

/-- Its readout remains non-constant on identities born at different depths. -/
theorem logged_fresh_values_distinguished :
    loggedReadoutAtThree
        ((LoggedRealization 3).indexedSpoke.forward firstFreshAtThree) ≠
      loggedReadoutAtThree
        ((LoggedRealization 3).indexedSpoke.forward secondFreshAtThree) := by
  unfold loggedReadoutAtThree
  rw [FiniteConstitutiveAlignment.Realization.realizeReadout_atIndex]
  rw [FiniteConstitutiveAlignment.Realization.realizeReadout_atIndex]
  change (10 : Nat) ≠ 20
  decide

/--
The concrete commuting square is inhabited by the free and logged algebras on
the real Cycle 1 histories from depth one to depth three.
-/
theorem free_logged_extension_natural
    (occurrence : (FreeRealization 1).Concrete) :
    (((FreeRealization 3).transport (LoggedRealization 3)).forward
      ((FreeRealization 1).extend (FreeRealization 3)
        oneToThree occurrence)) =
      (LoggedRealization 1).extend (LoggedRealization 3)
        oneToThree
        (((FreeRealization 1).transport
          (LoggedRealization 1)).forward occurrence) :=
  cycle1_extend_transport_natural
    examplePresentation exampleConcreteAlgebra loggedConcreteAlgebra
    oneToThree occurrence

#eval iteratedReadout initialReadout valuesAtThree firstInitialAtThree
#eval iteratedReadout initialReadout valuesAtThree secondInitialAtThree
#eval iteratedReadout initialReadout valuesAtThree firstFreshAtThree
#eval iteratedReadout initialReadout valuesAtThree secondFreshAtThree
#eval iteratedReadout initialReadout valuesAtThree thirdFreshAtThree

end StrongPerimetralTurning.Examples.Alignment.IteratedReadout

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.Examples.Alignment.IteratedReadout.first_second_distinction_persists
#print axioms StrongPerimetralTurning.Examples.Alignment.IteratedReadout.initial_distinction_persists
#print axioms StrongPerimetralTurning.Examples.Alignment.IteratedReadout.free_to_logged_atIndex
#print axioms StrongPerimetralTurning.Examples.Alignment.IteratedReadout.concreteReadouts_agree_atIndex
#print axioms StrongPerimetralTurning.Examples.Alignment.IteratedReadout.logged_fresh_values_distinguished
#print axioms StrongPerimetralTurning.Examples.Alignment.IteratedReadout.free_logged_extension_natural
/- AXIOM_AUDIT_END -/
