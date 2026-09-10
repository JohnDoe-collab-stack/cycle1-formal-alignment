import ConstitutiveAlignment.Succession

set_option linter.checkUnivs false

/-!
# One-step constitutive learning causality

The intervention fixes the problem, constitutive state, proposal producer, and
producer randomness.  Only the predictive state is changed by the declared
learning operation.  Each prediction is then explicitly consumed by the same
proposal function before rejection or succession is witnessed.
-/

namespace ConstitutiveAlignment

universe uProblem uPredictive uConstitution uRandomness uPrediction uProposal
universe uLearning uReason uRejected uSucceeds

structure LearningCausalSystem where
  Problem : Type uProblem
  PredictiveState : Type uPredictive
  Constitution : Type uConstitution
  Randomness : Type uRandomness
  Prediction : Type uPrediction
  Proposal : Type uProposal
  learn : Problem → PredictiveState → PredictiveState
  LearningEvidence :
    Problem → PredictiveState → PredictiveState → Type uLearning
  learningEvidence : (problem : Problem) → (parent : PredictiveState) →
    LearningEvidence problem parent (learn problem parent)
  predict : PredictiveState → Problem → Prediction
  propose : Problem → Constitution → Randomness → Prediction → Proposal
  RejectReason : Type uReason
  Rejected : Constitution → Proposal → RejectReason → Type uRejected
  successorState : Constitution → Proposal → Constitution
  Succeeds : Constitution → Proposal → Constitution → Type uSucceeds

structure InterventionCase (system : LearningCausalSystem) where
  problem : system.Problem
  constitution : system.Constitution
  randomness : system.Randomness
  parentPredictiveState : system.PredictiveState

def InterventionCase.learnedPredictiveState
    {system : LearningCausalSystem}
    (intervention : InterventionCase system) : system.PredictiveState :=
  system.learn intervention.problem intervention.parentPredictiveState

structure ConsumedProposal
    (system : LearningCausalSystem)
    (intervention : InterventionCase system)
    (predictiveState : system.PredictiveState) where
  candidate : system.Proposal
  consumedExactly : candidate =
    system.propose intervention.problem intervention.constitution
      intervention.randomness
      (system.predict predictiveState intervention.problem)

def exactConsumedProposal
    (system : LearningCausalSystem)
    (intervention : InterventionCase system)
    (predictiveState : system.PredictiveState) :
    ConsumedProposal system intervention predictiveState :=
  { candidate :=
      system.propose intervention.problem intervention.constitution
        intervention.randomness
        (system.predict predictiveState intervention.problem)
    consumedExactly := rfl }

structure OneStepLearningCausality
    (system : LearningCausalSystem)
    (intervention : InterventionCase system) where
  learning : system.LearningEvidence intervention.problem
    intervention.parentPredictiveState intervention.learnedPredictiveState
  parentProposal :
    ConsumedProposal system intervention intervention.parentPredictiveState
  learnedProposal :
    ConsumedProposal system intervention intervention.learnedPredictiveState
  predictionChanges :
    system.predict intervention.parentPredictiveState intervention.problem =
      system.predict intervention.learnedPredictiveState intervention.problem →
        False
  proposalChanges : parentProposal.candidate = learnedProposal.candidate → False
  parentRejectReason : system.RejectReason
  parentRejected :
    system.Rejected intervention.constitution parentProposal.candidate
      parentRejectReason
  learnedSucceeds :
    system.Succeeds intervention.constitution learnedProposal.candidate
      (system.successorState intervention.constitution
        learnedProposal.candidate)

def buildOneStepLearningCausality
    (system : LearningCausalSystem)
    (intervention : InterventionCase system)
    (predictionChanges :
      system.predict intervention.parentPredictiveState intervention.problem =
        system.predict intervention.learnedPredictiveState intervention.problem →
          False)
    (proposalChanges :
      (exactConsumedProposal system intervention
          intervention.parentPredictiveState).candidate =
        (exactConsumedProposal system intervention
          intervention.learnedPredictiveState).candidate → False)
    (parentRejectReason : system.RejectReason)
    (parentRejected :
      system.Rejected intervention.constitution
        (exactConsumedProposal system intervention
          intervention.parentPredictiveState).candidate
        parentRejectReason)
    (learnedSucceeds :
      system.Succeeds intervention.constitution
        (exactConsumedProposal system intervention
          intervention.learnedPredictiveState).candidate
        (system.successorState intervention.constitution
          (exactConsumedProposal system intervention
            intervention.learnedPredictiveState).candidate)) :
    OneStepLearningCausality system intervention :=
  { learning := system.learningEvidence intervention.problem
      intervention.parentPredictiveState
    parentProposal := exactConsumedProposal system intervention
      intervention.parentPredictiveState
    learnedProposal := exactConsumedProposal system intervention
      intervention.learnedPredictiveState
    predictionChanges := predictionChanges
    proposalChanges := proposalChanges
    parentRejectReason := parentRejectReason
    parentRejected := parentRejected
    learnedSucceeds := learnedSucceeds }

/- A trace containing learning and a proposal has no causal guarantee unless
   the consumed-prediction equalities and contrasting verdicts are supplied. -/
structure JuxtaposedLearningTrace (system : LearningCausalSystem) where
  problem : system.Problem
  parent : system.PredictiveState
  learning : system.LearningEvidence problem parent (system.learn problem parent)
  observedProposal : system.Proposal

/-! ## Finite constructive witness -/

namespace LearningExamples

inductive LearningWitness : Unit → Bool → Bool → Type
  | falseToTrue : LearningWitness () false true
  | trueToFalse : LearningWitness () true false

inductive RejectReason : Type
  | unchangedPrediction

inductive Rejected : Bool → Bool → RejectReason → Type
  | parentFalse : Rejected false false .unchangedPrediction

inductive Succeeds : Bool → Bool → Bool → Type
  | learnedTrue : Succeeds false true true

def system : LearningCausalSystem where
  Problem := Unit
  PredictiveState := Bool
  Constitution := Bool
  Randomness := Unit
  Prediction := Bool
  Proposal := Bool
  learn := fun _problem state => Bool.not state
  LearningEvidence := LearningWitness
  learningEvidence := by
    intro problem parent
    cases problem
    cases parent
    · exact .falseToTrue
    · exact .trueToFalse
  predict := fun state _problem => state
  propose := fun _problem _constitution _randomness prediction => prediction
  RejectReason := RejectReason
  Rejected := Rejected
  successorState := fun _constitution proposal => proposal
  Succeeds := Succeeds

def intervention : InterventionCase system where
  problem := ()
  constitution := false
  randomness := ()
  parentPredictiveState := false

theorem parentPrediction_ne_learnedPrediction :
    system.predict intervention.parentPredictiveState intervention.problem =
      system.predict intervention.learnedPredictiveState intervention.problem →
        False := by
  intro impossible
  nomatch impossible

theorem parentProposal_ne_learnedProposal :
    (exactConsumedProposal system intervention
        intervention.parentPredictiveState).candidate =
      (exactConsumedProposal system intervention
        intervention.learnedPredictiveState).candidate → False := by
  intro impossible
  nomatch impossible

def causalWitness : OneStepLearningCausality system intervention :=
  buildOneStepLearningCausality system intervention
    parentPrediction_ne_learnedPrediction
    parentProposal_ne_learnedProposal
    .unchangedPrediction
    .parentFalse
    .learnedTrue

/- Constant proposal production separates changed predictions from causal
   influence on the proposal. -/
def constantProposalSystem : LearningCausalSystem where
  Problem := Unit
  PredictiveState := Bool
  Constitution := Unit
  Randomness := Unit
  Prediction := Bool
  Proposal := Unit
  learn := fun _problem state => Bool.not state
  LearningEvidence := fun _problem parent learned =>
    PLift (learned = Bool.not parent)
  learningEvidence := fun _problem _parent => ⟨rfl⟩
  predict := fun state _problem => state
  propose := fun _problem _constitution _randomness _prediction => ()
  RejectReason := Unit
  Rejected := fun _constitution _proposal _reason => Unit
  successorState := fun constitution _proposal => constitution
  Succeeds := fun _source _proposal _target => Unit

def constantIntervention : InterventionCase constantProposalSystem where
  problem := ()
  constitution := ()
  randomness := ()
  parentPredictiveState := false

theorem constantProposalSystem_hasNoCausalWitness :
    OneStepLearningCausality constantProposalSystem constantIntervention → False :=
  fun witness => witness.proposalChanges rfl

end LearningExamples

end ConstitutiveAlignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveAlignment.exactConsumedProposal
#print axioms ConstitutiveAlignment.buildOneStepLearningCausality
#print axioms ConstitutiveAlignment.LearningExamples.parentPrediction_ne_learnedPrediction
#print axioms ConstitutiveAlignment.LearningExamples.parentProposal_ne_learnedProposal
#print axioms ConstitutiveAlignment.LearningExamples.causalWitness
#print axioms ConstitutiveAlignment.LearningExamples.constantProposalSystem_hasNoCausalWitness
/- AXIOM_AUDIT_END -/
