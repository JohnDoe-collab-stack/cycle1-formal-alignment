import StrongPerimetralTurning.ConstitutivePersistence

open Alignment

/-!
# A non-identity concrete continuation algebra

This example witnesses that `ConcreteContinuationAlgebra` does not force the
free identity interpretation.  It is deliberately kept outside the structural
foundation: no theorem in the foundation or in the human-scale facade depends
on it.

The concrete state retains only a numerical formation depth.  Concrete steps
carry an observable event distinguishing the four generators of the free
formation algebra.  Returned explicit, implicit, difference, compatibility,
and provenance data are encoded as numerical observations rather than reused
as their free types.  Boundary freshness is witnessed by the strict increase
of formation depth.

Thus the example is not merely a renamed copy of `exampleConcreteAlgebra`:
its state space, step space, observations, and transition evidence are all
concrete types distinct from the free layer.  Nevertheless, every generated
history still receives the canonical exact realization supplied by
`exactlyInterpretHistory`.
-/

namespace StrongPerimetralTurning.Examples.ConcreteContinuation.LoggedAlgebra

open StrongPerimetralTurning.Example

/-! ## Concrete observations -/

def freeTailDepth : FreeTail → Nat
  | .first => 0
  | .next tail => freeTailDepth tail + 1

def explicitCode : Example.Explicit → Nat
  | .first => 10
  | .second => 20
  | .third => 30
  | .fourth => 40

def implicitCode : Example.Implicit → Nat
  | .first => 11
  | .second => 21
  | .third => 31
  | .fourth => 41

def differenceCode : Example.Difference → Nat
  | .first => 12
  | .second => 22
  | .third => 32
  | .fourth => 42

def compatibilityCode :
    {implicit : Example.Implicit} →
    {explicit : Example.Explicit} →
    Example.Compatible implicit explicit → Nat
  | _, _, .internalFirst => 100
  | _, _, .internalSecond => 101
  | _, _, .internalThird => 102
  | _, _, .internalFourth => 103
  | _, _, .firstToSecond => 110
  | _, _, .secondToThird => 111
  | _, _, .thirdToFourth => 112
  | _, _, .fourthToFirst => 113

def provenanceCode :
    {difference : Example.Difference} →
    Example.Provenance difference → Nat
  | _, .first => 200
  | _, .second => 201
  | _, .third => 202
  | _, .fourth => 203

def returnedExplicitCode : ReturnedExplicit examplePresentation → Nat
  | .source explicit => explicitCode explicit
  | .formed _ => 1000

def returnedImplicitCode : ReturnedImplicit examplePresentation → Nat
  | .source implicit => implicitCode implicit
  | .formed _ => 1001

def returnedCompatibilityCode :
    {implicit : ReturnedImplicit examplePresentation} →
    {explicit : ReturnedExplicit examplePresentation} →
    ReturnedCompatible examplePresentation implicit explicit → Nat
  | _, _, .source compatible => compatibilityCode compatible
  | _, _, .formedInternal _ => 1200
  | _, _, .leaveBoundary _ => 1201
  | _, _, .beyondAdvance tail => 1300 + freeTailDepth tail

def returnedDifferenceCode : ReturnedDifference examplePresentation → Nat
  | .source difference => differenceCode difference
  | .free tail => 1400 + freeTailDepth tail

def returnedProvenanceCode :
    {difference : ReturnedDifference examplePresentation} →
    ReturnedProvenance examplePresentation difference → Nat
  | _, .source provenance => provenanceCode provenance
  | _, .free tail => 1500 + freeTailDepth tail

/-! ## Formation depth and observable concrete steps -/

def formationDepth
    {P : CircularPresentation}
    {cursor : PerimeterCursor P}
    {difference : BoundaryDifferenceCode P cursor} :
    FreeConstitutionCore P cursor difference → Nat
  | .root => 0
  | .formed previous _ => formationDepth previous + 1

def positiveDepth
    {P : CircularPresentation}
    (state : PositiveConstitution P) : Nat :=
  formationDepth state.2.1.2

@[simp] theorem positiveDepth_canonicalTarget
    {P : CircularPresentation}
    (source : PositiveConstitution P) :
    positiveDepth (canonicalTarget source) = positiveDepth source + 1 :=
  rfl

inductive ConcreteEvent where
  | explicitPole
  | implicitPole
  | currentDifference
  | admissible
  deriving DecidableEq, Repr

structure LoggedStep (source target : Nat) where
  event : ConcreteEvent
  advances : target = source + 1

def loggedStep
    (source : PositiveConstitution examplePresentation)
    (event : ConcreteEvent) :
    LoggedStep (positiveDepth source) (positiveDepth (canonicalTarget source)) :=
  { event := event
    advances := positiveDepth_canonicalTarget source }

structure IntegrationReceipt (difference : Nat) where
  observed : Nat
  observedExact : observed = difference

structure ContinuationReceipt (source target : Nat) where
  observedSource : Nat
  observedTarget : Nat
  sourceExact : observedSource = source
  targetExact : observedTarget = target

structure FreshBoundaryReceipt (source target : Nat) where
  previousBoundary : Nat
  nextBoundary : Nat
  previousExact : previousBoundary = source
  nextExact : nextBoundary = target

theorem positiveDepth_canonicalTarget_ne
    (source : PositiveConstitution examplePresentation) :
    positiveDepth (canonicalTarget source) ≠ positiveDepth source := by
  rw [positiveDepth_canonicalTarget]
  exact Nat.ne_of_gt (Nat.lt_succ_self _)

/-! ## The non-identity algebra -/

def loggedConcreteAlgebra :
    ConcreteContinuationAlgebra examplePresentation :=
  { ConcreteState := Nat
    ConcreteStep := LoggedStep
    stateAt := positiveDepth

    ConcreteExplicit := Nat
    ConcreteImplicit := Nat
    ConcreteCompatible := fun _ _ => Nat
    interpretExplicit := returnedExplicitCode
    interpretImplicit := returnedImplicitCode
    interpretCompatible := returnedCompatibilityCode

    ConcreteDifference := Nat
    ConcreteProvenance := fun _ => Nat
    interpretDifference := returnedDifferenceCode
    interpretProvenance := returnedProvenanceCode

    ConcreteIntegration := IntegrationReceipt
    ConcreteContinuation := ContinuationReceipt
    ConcreteFreshBoundary := FreshBoundaryReceipt
    ConcreteBoundaryRecord := Nat
    boundaryRecordAt := positiveDepth

    concreteStep := fun source => loggedStep source .admissible
    explicitPoleStep := fun source => loggedStep source .explicitPole
    implicitPoleStep := fun source => loggedStep source .implicitPole
    differenceStep := fun source => loggedStep source .currentDifference
    admissibleStep := fun source _ => loggedStep source .admissible

    successorFormationExact := fun _ => rfl
    compatibilityRealized := fun source =>
      returnedCompatibilityCode (stepCompatibleAt source.1)
    compatibilityRealizedExact := fun _ => rfl
    differenceIntegrated := fun source =>
      { observed :=
          returnedDifferenceCode (boundaryDifferenceReadout source.2.2)
        observedExact := rfl }
    provenancePreserved := fun source =>
      returnedProvenanceCode (boundaryProvenanceReadout source.2.2)
    provenancePreservedExact := fun _ => rfl
    differenceContinued := fun source =>
      { observedSource :=
          returnedDifferenceCode (boundaryDifferenceReadout source.2.2)
        observedTarget :=
          returnedDifferenceCode
            (boundaryDifferenceReadout (canonicalTarget source).2.2)
        sourceExact := rfl
        targetExact := rfl }
    boundaryFresh := fun source =>
      { previousBoundary :=
          returnedDifferenceCode (boundaryDifferenceReadout source.2.2)
        nextBoundary :=
          returnedDifferenceCode
            (boundaryDifferenceReadout (canonicalTarget source).2.2)
        previousExact := rfl
        nextExact := rfl }
    boundaryRecordFresh := positiveDepth_canonicalTarget_ne }

/-! ## Observable non-triviality -/

theorem concreteState_advances
    (source : PositiveConstitution examplePresentation) :
    loggedConcreteAlgebra.stateAt (canonicalTarget source) ≠
      loggedConcreteAlgebra.stateAt source :=
  positiveDepth_canonicalTarget_ne source

theorem freeGenerators_remain_distinct
    (source : PositiveConstitution examplePresentation) :
    (loggedConcreteAlgebra.explicitPoleStep source).event ≠
      (loggedConcreteAlgebra.differenceStep source).event := by
  change ConcreteEvent.explicitPole ≠ ConcreteEvent.currentDifference
  decide

theorem explicitObservations_remain_distinct :
    loggedConcreteAlgebra.interpretExplicit
        (.source Example.Explicit.first) ≠
      loggedConcreteAlgebra.interpretExplicit
        (.source Example.Explicit.second) := by
  change (10 : Nat) ≠ 20
  decide

def exactLoggedRealization
    (history : RootedGeneratedHistory examplePresentation) :
    ExactConcreteRealization loggedConcreteAlgebra history :=
  exactlyInterpretHistory loggedConcreteAlgebra history.history

def oneStepLoggedRealization :
    ExactConcreteRealization loggedConcreteAlgebra
      (oneStepAfterPerimeter examplePresentation) :=
  exactLoggedRealization (oneStepAfterPerimeter examplePresentation)

/--
The non-identity logged algebra realizes the same content-independent one-step
carrier alignment as the free example.  This witnesses the concrete scope of
the general carrier-realization interface without adding a pairwise matching
or claiming independent preservation of labels, order, or step semantics.
-/
def oneStepLoggedAlignmentRealization :
    (ConstitutivePersistence.canonicalOneStepAlignment
      examplePresentation).Realization :=
  ConstitutivePersistence.canonicalOneStepAlignmentRealization
    examplePresentation loggedConcreteAlgebra

end StrongPerimetralTurning.Examples.ConcreteContinuation.LoggedAlgebra

/- AXIOM_AUDIT_BEGIN -/
#print axioms StrongPerimetralTurning.Examples.ConcreteContinuation.LoggedAlgebra.loggedConcreteAlgebra
#print axioms StrongPerimetralTurning.Examples.ConcreteContinuation.LoggedAlgebra.concreteState_advances
#print axioms StrongPerimetralTurning.Examples.ConcreteContinuation.LoggedAlgebra.freeGenerators_remain_distinct
#print axioms StrongPerimetralTurning.Examples.ConcreteContinuation.LoggedAlgebra.explicitObservations_remain_distinct
#print axioms StrongPerimetralTurning.Examples.ConcreteContinuation.LoggedAlgebra.exactLoggedRealization
#print axioms StrongPerimetralTurning.Examples.ConcreteContinuation.LoggedAlgebra.oneStepLoggedRealization
#print axioms StrongPerimetralTurning.Examples.ConcreteContinuation.LoggedAlgebra.oneStepLoggedAlignmentRealization
/- AXIOM_AUDIT_END -/
