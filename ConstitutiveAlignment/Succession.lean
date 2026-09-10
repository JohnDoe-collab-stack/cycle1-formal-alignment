import ConstitutiveAlignment.Machine

set_option linter.checkUnivs false

/-!
# Constitutive succession

Parametric learning, constitutive incorporation, and normative succession are
separate interfaces.  Uniform iteration recursively consumes the state that
the preceding transition actually produced.
-/

namespace ConstitutiveAlignment

universe uParameters uLearning uState uIncorporation uRegime uSuccession uStep

structure ParametricLearning (Parameters : Type uParameters) where
  learned : Parameters → Parameters
  LearningEvidence : Parameters → Parameters → Type uLearning
  evidence : (parameters : Parameters) →
    LearningEvidence parameters (learned parameters)

structure ConstitutiveIncorporation (State : Type uState) where
  incorporated : State → State
  Incorporates : State → State → Type uIncorporation
  witness : (state : State) → Incorporates state (incorporated state)

structure NormativeSuccession
    (State : Type uState)
    (Regime : State → Type uRegime) where
  successor : State → State
  Succeeds : State → State → Type uSuccession
  step : (state : State) → Succeeds state (successor state)
  preservesRegime : {state : State} →
    Regime state → Regime (successor state)

/- Incorporation and normative succession are independently specified.  Their
   agreement is therefore an explicit witness, not a definitional collapse. -/
structure ConstitutiveSuccession
    (State : Type uState)
    (Regime : State → Type uRegime) where
  incorporation : ConstitutiveIncorporation.{uState, uIncorporation} State
  normative : NormativeSuccession.{uState, uRegime, uSuccession} State Regime
  sameSuccessor : (state : State) →
    incorporation.incorporated state = normative.successor state

namespace ConstitutiveSuccession

def incorporatedRegime
    {State : Type uState}
    {Regime : State → Type uRegime}
    (succession : ConstitutiveSuccession State Regime)
    {state : State}
    (admitted : Regime state) :
    Regime (succession.incorporation.incorporated state) := by
  rw [succession.sameSuccessor state]
  exact succession.normative.preservesRegime admitted

end ConstitutiveSuccession

/- A uniform transition chooses no depth-specific fixture. -/
structure UniformTransition (State : Type uState) where
  Step : State → State → Type uStep
  next : State → State
  step : (state : State) → Step state (next state)

def iterateState
    {State : Type uState}
    (transition : UniformTransition State) : Nat → State → State
  | 0, initial => initial
  | Nat.succ depth, initial =>
      transition.next (iterateState transition depth initial)

def iterateHistory
    {State : Type uState}
    (transition : UniformTransition State)
    (depth : Nat)
    (initial : State) :
    StrongPerimetralTurning.History transition.Step initial
      (iterateState transition depth initial) := by
  induction depth with
  | zero => exact .root
  | succ depth inductionHypothesis =>
      exact .extend inductionHypothesis
        (transition.step (iterateState transition depth initial))

theorem iterateState_succ
    {State : Type uState}
    (transition : UniformTransition State)
    (depth : Nat)
    (initial : State) :
    iterateState transition (Nat.succ depth) initial =
      transition.next (iterateState transition depth initial) :=
  rfl

def Preserves
    {State : Type uState}
    (transition : UniformTransition State)
    (Obligation : State → Type _ ) : Type _ :=
  {state : State} → Obligation state → Obligation (transition.next state)

def preservesAlongIteration
    {State : Type uState}
    {transition : UniformTransition State}
    {Obligation : State → Type _}
    (preserves : Preserves transition Obligation)
    (depth : Nat)
    (initial : State)
    (obligation : Obligation initial) :
    Obligation (iterateState transition depth initial) := by
  induction depth with
  | zero => exact obligation
  | succ depth inductionHypothesis =>
      exact preserves
        (state := iterateState transition depth initial)
        inductionHypothesis

/- A partial transition makes inability to continue a positive, inspectable
   outcome.  No decidability principle is imported: the machine supplies the
   decision and, in the stopping branch, the refutation witness. -/
universe uCanAdvance

inductive AdvanceDecision
    {State : Type uState}
    (CanAdvance : State → Type uCanAdvance)
    (state : State) : Type _
  | advance : CanAdvance state → AdvanceDecision CanAdvance state
  | stop : (CanAdvance state → False) → AdvanceDecision CanAdvance state

structure PartialTransition (State : Type uState) where
  CanAdvance : State → Type uCanAdvance
  next : {state : State} → CanAdvance state → State
  Step : State → State → Type uStep
  step : {state : State} → (permission : CanAdvance state) →
    Step state (next permission)
  decide : (state : State) → AdvanceDecision CanAdvance state

inductive PartialStepResult
    {State : Type uState}
    (transition : PartialTransition State)
    (state : State) : Type _
  | advanced : (permission : transition.CanAdvance state) →
      transition.Step state (transition.next permission) →
      PartialStepResult transition state
  | stopped : (transition.CanAdvance state → False) →
      PartialStepResult transition state

def PartialTransition.run
    {State : Type uState}
    (transition : PartialTransition State)
    (state : State) : PartialStepResult transition state :=
  match transition.decide state with
  | .advance permission => .advanced permission (transition.step permission)
  | .stop refutation => .stopped refutation

structure LinkedTwoCycles
    {State : Type uState}
    (transition : UniformTransition State)
    (initial : State) where
  first : transition.Step initial (transition.next initial)
  second : transition.Step
    (transition.next initial)
    (transition.next (transition.next initial))

def UniformTransition.twoCycles
    {State : Type uState}
    (transition : UniformTransition State)
    (initial : State) : LinkedTwoCycles transition initial :=
  { first := transition.step initial
    second := transition.step (transition.next initial) }

/-! ## Finite linked-cycle witness -/

namespace SuccessionExamples

def toggleTransition : UniformTransition Bool where
  Step := fun source target => PLift (target = Bool.not source)
  next := Bool.not
  step := fun _state => ⟨rfl⟩

def twoLinkedToggles : LinkedTwoCycles toggleTransition false :=
  toggleTransition.twoCycles false

theorem firstToggle_is_secondInput :
    iterateState toggleTransition 1 false = true :=
  rfl

theorem secondToggle_consumesFirstOutput :
    iterateState toggleTransition 2 false =
      toggleTransition.next (iterateState toggleTransition 1 false) :=
  rfl

def boolObligation (_state : Bool) : Type := Unit

def togglePreservesObligation :
    Preserves toggleTransition boolObligation :=
  fun _obligation => ()

def obligationAfterTwoCycles :
    boolObligation (iterateState toggleTransition 2 false) :=
  preservesAlongIteration togglePreservesObligation 2 false ()

inductive Live : Bool → Type
  | atFalse : Live false

def toggleIncorporation : ConstitutiveIncorporation Bool where
  incorporated := Bool.not
  Incorporates := fun source target => PLift (target = Bool.not source)
  witness := fun _state => ⟨rfl⟩

def toggleNormativeSuccession : NormativeSuccession Bool boolObligation where
  successor := Bool.not
  Succeeds := fun source target => PLift (target = Bool.not source)
  step := fun _state => ⟨rfl⟩
  preservesRegime := fun _admitted => ()

def linkedIncorporationAndNorm :
    ConstitutiveSuccession Bool boolObligation where
  incorporation := toggleIncorporation
  normative := toggleNormativeSuccession
  sameSuccessor := fun _state => rfl

def stoppingTransition : PartialTransition Bool where
  CanAdvance := Live
  next := fun _permission => true
  Step := fun source target => PLift (source = false ∧ target = true)
  step
    | .atFalse => ⟨rfl, rfl⟩
  decide
    | false => .advance .atFalse
    | true => .stop (fun permission => nomatch permission)

def firstPartialStep : PartialStepResult stoppingTransition false :=
  stoppingTransition.run false

def explicitStop : PartialStepResult stoppingTransition true :=
  stoppingTransition.run true

end SuccessionExamples

end ConstitutiveAlignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveAlignment.iterateHistory
#print axioms ConstitutiveAlignment.iterateState_succ
#print axioms ConstitutiveAlignment.preservesAlongIteration
#print axioms ConstitutiveAlignment.ConstitutiveSuccession.incorporatedRegime
#print axioms ConstitutiveAlignment.PartialTransition.run
#print axioms ConstitutiveAlignment.UniformTransition.twoCycles
#print axioms ConstitutiveAlignment.SuccessionExamples.twoLinkedToggles
#print axioms ConstitutiveAlignment.SuccessionExamples.secondToggle_consumesFirstOutput
#print axioms ConstitutiveAlignment.SuccessionExamples.obligationAfterTwoCycles
#print axioms ConstitutiveAlignment.SuccessionExamples.linkedIncorporationAndNorm
#print axioms ConstitutiveAlignment.SuccessionExamples.firstPartialStep
#print axioms ConstitutiveAlignment.SuccessionExamples.explicitStop
/- AXIOM_AUDIT_END -/
