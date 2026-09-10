import StrongPerimetralTurning

set_option linter.checkUnivs false

/-!
# Constitutive machines

This file exposes the smallest machine interface needed to reuse the Cycle 1
kernel without identifying construction, realization, operational admission,
or normative satisfaction.  Its circular instance is an adapter: it introduces
no replacement history, regime, norm, or realization theorem.
-/

namespace ConstitutiveAlignment

open StrongPerimetralTurning

universe uSource uTarget

/- The machine layer needs only the part of exact realization that prevents
   occurrence collapse.  Exact Cycle 1 round trips provide this map directly. -/
structure InjectiveMap (Source : Type uSource) (Target : Type uTarget) where
  toFun : Source → Target
  injective : Function.Injective toFun

namespace InjectiveMap

def trans
    {First : Type uSource}
    {Middle : Type uTarget}
    {Last : Type _}
    (first : InjectiveMap First Middle)
    (second : InjectiveMap Middle Last) : InjectiveMap First Last :=
  { toFun := fun value => second.toFun (first.toFun value)
    injective := by
      intro firstValue secondValue equality
      exact first.injective (second.injective equality) }

theorem preservesDistinct
    {Source : Type uSource}
    {Target : Type uTarget}
    (realization : InjectiveMap Source Target)
    {first second : Source}
    (distinct : first = second → False) :
    realization.toFun first = realization.toFun second → False :=
  fun equality => distinct (realization.injective equality)

end InjectiveMap

universe uState uStep uCandidate uFaithful uRegime uNorm uRealized

/- A constitutive machine carries proof-relevant rooted histories together with
   three deliberately separate predicates on the same candidate carrier. -/
structure ConstitutiveMachine where
  State : Type uState
  Step : State → State → Type uStep
  root : State
  Candidate : Type uCandidate
  endpoint : Candidate → State
  history : (candidate : Candidate) →
    History Step root (endpoint candidate)
  Faithful : Candidate → Type uFaithful
  Regime : Candidate → Type uRegime
  Norm : Candidate → Type uNorm
  RealizedOccurrence : Candidate → Type uRealized
  occurrenceRealization :
    {candidate : Candidate} → Faithful candidate →
      InjectiveMap
        (History.Occurrence (history candidate))
        (RealizedOccurrence candidate)

namespace ConstitutiveMachine

abbrev Occurrence
    (machine : ConstitutiveMachine)
    (candidate : machine.Candidate) : Type _ :=
  History.Occurrence (machine.history candidate)

end ConstitutiveMachine

/- Adequacy is an explicit pair of transformations between operational
   admission and autonomous normative satisfaction on the same candidate. -/
structure MachineAdequacy (machine : ConstitutiveMachine) where
  sound : (candidate : machine.Candidate) →
    machine.Regime candidate → machine.Norm candidate
  complete : (candidate : machine.Candidate) →
    machine.Norm candidate → machine.Regime candidate

abbrev OperationalExit (machine : ConstitutiveMachine) : Type _ :=
  AbstractSegmentedTurning.RegimeExit machine.Faithful machine.Regime

/- The Cycle 1 carrier and its existing proof objects instantiate the generic
   interface definitionally.  The implementation algebra contributes only the
   faithful concrete realization family. -/
def circularMachine
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) : ConstitutiveMachine where
  State := PositiveConstitution P
  Step := @GeneratedStep P
  root := initialPositive P
  Candidate := RootedGeneratedHistory P
  endpoint := RootedGeneratedHistory.endpoint
  history := RootedGeneratedHistory.history
  Faithful := ExactConcreteRealization A
  Regime := CircularRefinement P
  Norm := CircularSpecificationSatisfaction P
  RealizedOccurrence := fun candidate =>
    History.Occurrence (A.realizeHistory candidate.history)
  occurrenceRealization := fun faithful =>
    { toFun := faithful.forwardOccurrence
      injective := faithful.forwardOccurrence_injective }

def circularMachineAdequacy
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    MachineAdequacy (circularMachine P A) :=
  { sound := fun _candidate => circularRefinement_soundSpecification
    complete := fun _candidate => circularSpecification_complete }

def oneStepOperationalExit
    (P : CircularPresentation)
    (A : ConcreteContinuationAlgebra P) :
    OperationalExit (circularMachine P A) :=
  oneStepConcreteRegimeExit P A

/- Occurrence transport is inherited from exact Cycle 1 realization.  These
   projections make the connection available under the machine vocabulary
   without weakening the existing round-trip laws. -/
def forwardConcreteOccurrence
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {candidate : RootedGeneratedHistory P}
    (faithful : ExactConcreteRealization A candidate) :
    History.Occurrence candidate.history →
      History.Occurrence (A.realizeHistory candidate.history) :=
  faithful.forwardOccurrence

def backwardConcreteOccurrence
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {candidate : RootedGeneratedHistory P}
    (faithful : ExactConcreteRealization A candidate) :
    History.Occurrence (A.realizeHistory candidate.history) →
      History.Occurrence candidate.history :=
  faithful.backwardOccurrence

theorem forwardConcreteOccurrence_injective
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {candidate : RootedGeneratedHistory P}
    (faithful : ExactConcreteRealization A candidate) :
    Function.Injective (forwardConcreteOccurrence faithful) :=
  faithful.forwardOccurrence_injective

theorem backward_forwardConcreteOccurrence
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {candidate : RootedGeneratedHistory P}
    (faithful : ExactConcreteRealization A candidate)
    (occurrence : History.Occurrence candidate.history) :
    backwardConcreteOccurrence faithful
        (forwardConcreteOccurrence faithful occurrence) = occurrence :=
  faithful.forwardBackward occurrence

theorem forward_backwardConcreteOccurrence
    {P : CircularPresentation}
    {A : ConcreteContinuationAlgebra P}
    {candidate : RootedGeneratedHistory P}
    (faithful : ExactConcreteRealization A candidate)
    (occurrence :
      History.Occurrence (A.realizeHistory candidate.history)) :
    forwardConcreteOccurrence faithful
        (backwardConcreteOccurrence faithful occurrence) = occurrence :=
  faithful.backwardForward occurrence

/-! ## Constructive separator models -/

namespace Separators

inductive EmptyWitness : Type

/- Operational admission alone cannot manufacture normative satisfaction. -/
def regimeWithoutNorm : ConstitutiveMachine where
  State := Unit
  Step := fun _source _target => EmptyWitness
  root := ()
  Candidate := Unit
  endpoint := fun _candidate => ()
  history := fun _candidate => .root
  Faithful := fun _candidate => Unit
  Regime := fun _candidate => Unit
  Norm := fun _candidate => EmptyWitness
  RealizedOccurrence := fun _candidate => EmptyWitness
  occurrenceRealization := fun _faithful =>
    { toFun := fun occurrence => nomatch occurrence
      injective := by
        intro firstOccurrence
        nomatch firstOccurrence }

def regimeWithoutNorm_admitted : regimeWithoutNorm.Regime () :=
  ()

theorem regimeWithoutNorm_hasNoAdequacy :
    MachineAdequacy regimeWithoutNorm → False :=
  fun adequacy => nomatch adequacy.sound () regimeWithoutNorm_admitted

/- A two-step proof-relevant history has two distinct role occurrences even
   though a terminal-only reading into `Unit` returns the same value for both. -/
def firstStepHistory :
    History (fun _source _target : Unit => Unit) () () :=
  .extend .root ()

def twoStepHistory :
    History (fun _source _target : Unit => Unit) () () :=
  .extend firstStepHistory ()

def lastRole : History.Occurrence twoStepHistory :=
  .last

def earlierRole : History.Occurrence twoStepHistory :=
  .earlier .last

theorem lastRole_ne_earlierRole : lastRole = earlierRole → False := by
  intro equality
  have impossible : true = false :=
    congrArg
      (fun occurrence =>
        match occurrence with
        | .last => true
        | .earlier _prior => false)
      equality
  nomatch impossible

def terminalOnlyReading
    (_occurrence : History.Occurrence twoStepHistory) : Unit :=
  ()

theorem terminalOnlyReading_collapsesRoles :
    terminalOnlyReading lastRole = terminalOnlyReading earlierRole :=
  rfl

theorem noFaithfulTerminalOnlyRealization :
    InjectiveMap (History.Occurrence twoStepHistory) Unit → False := by
  intro realization
  apply lastRole_ne_earlierRole
  apply realization.injective
  cases realization.toFun lastRole
  cases realization.toFun earlierRole
  rfl

end Separators

end ConstitutiveAlignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveAlignment.InjectiveMap.trans
#print axioms ConstitutiveAlignment.InjectiveMap.preservesDistinct
#print axioms ConstitutiveAlignment.circularMachineAdequacy
#print axioms ConstitutiveAlignment.oneStepOperationalExit
#print axioms ConstitutiveAlignment.forwardConcreteOccurrence_injective
#print axioms ConstitutiveAlignment.backward_forwardConcreteOccurrence
#print axioms ConstitutiveAlignment.forward_backwardConcreteOccurrence
#print axioms ConstitutiveAlignment.Separators.regimeWithoutNorm_hasNoAdequacy
#print axioms ConstitutiveAlignment.Separators.lastRole_ne_earlierRole
#print axioms ConstitutiveAlignment.Separators.noFaithfulTerminalOnlyRealization
/- AXIOM_AUDIT_END -/
