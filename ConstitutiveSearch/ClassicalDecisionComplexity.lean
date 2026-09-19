import ConstitutiveSearch.ConstitutiveComplexityInputPolynomial
import ConstitutiveSearch.FrontierTrajectory

/-!
# Minimal bridge to classical decision-complexity interfaces

The repository's polynomial-cost interface is indexed by Nat.  The classical
bridge therefore uses Nat-coded decision instances rather than opening a new
general encoding framework.

The notions P and NP below are relative to:
* one concrete input-size function Nat -> Nat;
* one explicit source-level cost model.

No concrete machine-runtime model is silently assumed.

P is witnessed by a correct Boolean decider with input-polynomial announced
cost.

NP is witnessed relative to an explicit certificate family by:
* polynomially bounded positive certificates;
* a correct Boolean verifier;
* polynomially bounded announced verification cost.

A SearchSystem can be projected along any announced Nat-indexed family of
states.  Its continuations become the NP-like certificate family.  A correct
polynomial constitutive decider becomes the P-like projection.

FrontierTrajectory supplies the AND/OR projection law: constitutive expansion,
accumulation and reduction preserve the extensional yes/no decision even when
they do not preserve all computational structure.
-/

namespace ConstitutiveSearch

universe uWitness uState uContinuation uConstitution uStep

/-- Nat-coded extensional decision problem with a concrete encoded input size. -/
structure DecisionProblem where
  inputSize : Nat → Nat
  Accept : Nat → Prop

/-- Correct deterministic decision procedure with an announced polynomial cost. -/
structure PolynomialDecider
    (problem : DecisionProblem) where
  decide : Nat → Bool
  cost : Nat → Nat
  correct :
    ∀ input : Nat,
      decide input = true ↔
        problem.Accept input
  costPolynomial :
    InputPolynomiallyBounded
      problem.inputSize
      cost

/-- Classical P interface relative to the declared size and cost model. -/
def InP
    (problem : DecisionProblem) : Prop :=
  Nonempty
    (PolynomialDecider problem)

/--
Polynomial verifier interface relative to an explicit certificate family.

Keeping the certificate family explicit is deliberate: it avoids hiding a
type-level existential in the bridge and states exactly which constitutive
objects play the witness role.
-/
structure PolynomialVerifier
    (problem : DecisionProblem)
    (Witness : Nat → Type uWitness) where
  witnessSize :
    {input : Nat} →
      Witness input →
        Nat
  verify :
    (input : Nat) →
      Witness input →
        Bool
  cost :
    (input : Nat) →
      Witness input →
        Nat
  certificateBound :
    CostPolynomial
  verifierCostBound :
    CostPolynomial
  sound :
    ∀ (input : Nat)
      (witness : Witness input),
      verify input witness = true →
        problem.Accept input
  complete :
    ∀ input : Nat,
      problem.Accept input →
        ∃ witness : Witness input,
          witnessSize witness ≤
              certificateBound.eval
                (problem.inputSize input) ∧
            verify input witness = true
  costBound :
    ∀ (input : Nat)
      (witness : Witness input),
      witnessSize witness ≤
          certificateBound.eval
            (problem.inputSize input) →
        cost input witness ≤
          verifierCostBound.eval
            (problem.inputSize input)

/-- Classical NP verifier interface relative to the announced witness family. -/
def InNP
    (problem : DecisionProblem)
    (Witness : Nat → Type uWitness) : Prop :=
  Nonempty
    (PolynomialVerifier
      problem
      Witness)

/--
Extensional decision problem obtained by selecting one SearchSystem state for
each Nat-coded instance and forgetting all other constitutive structure.
-/
def searchSystemDecisionProblem
    (system : SearchSystem.{uState,uContinuation})
    (stateAt : Nat → system.State)
    (inputSize : Nat → Nat) :
    DecisionProblem :=
  { inputSize := inputSize
    Accept := fun input =>
      system.Viable
        (stateAt input) }

/-- The NP-like role remains exactly existential accepted continuation. -/
theorem searchSystemDecisionProblem_accept_iff
    (system : SearchSystem.{uState,uContinuation})
    (stateAt : Nat → system.State)
    (inputSize : Nat → Nat)
    (input : Nat) :
    (searchSystemDecisionProblem
        system
        stateAt
        inputSize).Accept input ↔
      ∃ continuation :
          system.Continuation
            (stateAt input),
        system.Accept
          (stateAt input)
          continuation := by
  rfl

/--
Explicit data needed to project structural continuations to the classical NP
verifier interface.
-/
structure SearchSystemPolynomialVerifier
    (system : SearchSystem.{uState,uContinuation})
    (stateAt : Nat → system.State)
    (inputSize : Nat → Nat) where
  continuationSize :
    {input : Nat} →
      system.Continuation
        (stateAt input) →
          Nat
  verify :
    (input : Nat) →
      system.Continuation
        (stateAt input) →
          Bool
  cost :
    (input : Nat) →
      system.Continuation
        (stateAt input) →
          Nat
  certificateBound :
    CostPolynomial
  verifierCostBound :
    CostPolynomial
  verifySound :
    ∀ (input : Nat)
      (continuation :
        system.Continuation
          (stateAt input)),
      verify input continuation = true →
        system.Accept
          (stateAt input)
          continuation
  verifyComplete :
    ∀ (input : Nat)
      (continuation :
        system.Continuation
          (stateAt input)),
      system.Accept
          (stateAt input)
          continuation →
        verify input continuation = true
  smallAcceptedWitness :
    ∀ input : Nat,
      system.Viable
          (stateAt input) →
        ∃ continuation :
            system.Continuation
              (stateAt input),
          system.Accept
              (stateAt input)
              continuation ∧
            continuationSize continuation ≤
              certificateBound.eval
                (inputSize input)
  costBound :
    ∀ (input : Nat)
      (continuation :
        system.Continuation
          (stateAt input)),
      continuationSize continuation ≤
          certificateBound.eval
            (inputSize input) →
        cost input continuation ≤
          verifierCostBound.eval
            (inputSize input)

/-- Build the verifier from the explicit SearchSystem witness data. -/
def SearchSystemPolynomialVerifier.toPolynomialVerifier
    {system : SearchSystem.{uState,uContinuation}}
    {stateAt : Nat → system.State}
    {inputSize : Nat → Nat}
    (bridge :
      SearchSystemPolynomialVerifier
        system
        stateAt
        inputSize) :
    PolynomialVerifier
      (searchSystemDecisionProblem
        system
        stateAt
        inputSize)
      (fun input =>
        system.Continuation
          (stateAt input)) :=
  { witnessSize :=
      bridge.continuationSize
    verify :=
      bridge.verify
    cost :=
      bridge.cost
    certificateBound :=
      bridge.certificateBound
    verifierCostBound :=
      bridge.verifierCostBound
    sound := by
      intro input continuation verified
      exact
        ⟨continuation,
          bridge.verifySound
            input
            continuation
            verified⟩
    complete := by
      intro input viable
      rcases
          bridge.smallAcceptedWitness
            input
            viable with
        ⟨continuation,
          accepted,
          sizeBound⟩
      exact
        ⟨continuation,
          sizeBound,
          bridge.verifyComplete
            input
            continuation
            accepted⟩
    costBound :=
      bridge.costBound }

/-- The NP-like continuation role projects to NP under its explicit verifier hypotheses. -/
theorem npLike_projects_to_InNP
    {system : SearchSystem.{uState,uContinuation}}
    {stateAt : Nat → system.State}
    {inputSize : Nat → Nat}
    (bridge :
      SearchSystemPolynomialVerifier
        system
        stateAt
        inputSize) :
    InNP
      (searchSystemDecisionProblem
        system
        stateAt
        inputSize)
      (fun input =>
        system.Continuation
          (stateAt input)) :=
  ⟨bridge.toPolynomialVerifier⟩

/-- Explicit data needed to project a P-like constitutive procedure to P. -/
structure SearchSystemPolynomialDecider
    (system : SearchSystem.{uState,uContinuation})
    (stateAt : Nat → system.State)
    (inputSize : Nat → Nat) where
  decide : Nat → Bool
  cost : Nat → Nat
  correct :
    ∀ input : Nat,
      decide input = true ↔
        system.Viable
          (stateAt input)
  costPolynomial :
    InputPolynomiallyBounded
      inputSize
      cost

/-- Build the classical P decider from the explicit constitutive decider. -/
def SearchSystemPolynomialDecider.toPolynomialDecider
    {system : SearchSystem.{uState,uContinuation}}
    {stateAt : Nat → system.State}
    {inputSize : Nat → Nat}
    (bridge :
      SearchSystemPolynomialDecider
        system
        stateAt
        inputSize) :
    PolynomialDecider
      (searchSystemDecisionProblem
        system
        stateAt
        inputSize) :=
  { decide :=
      bridge.decide
    cost :=
      bridge.cost
    correct :=
      bridge.correct
    costPolynomial :=
      bridge.costPolynomial }

/-- The P-like role projects to P exactly under a correct polynomial decider. -/
theorem pLike_projects_to_InP
    {system : SearchSystem.{uState,uContinuation}}
    {stateAt : Nat → system.State}
    {inputSize : Nat → Nat}
    (bridge :
      SearchSystemPolynomialDecider
        system
        stateAt
        inputSize) :
    InP
      (searchSystemDecisionProblem
        system
        stateAt
        inputSize) :=
  ⟨bridge.toPolynomialDecider⟩

/-- Nat-indexed frontier decision problem obtained by forgetting constitution. -/
def frontierDecisionProblem
    (system : SearchSystem.{uState,uContinuation})
    (frontierAt :
      Nat →
        List system.State)
    (inputSize : Nat → Nat) :
    DecisionProblem :=
  { inputSize :=
      inputSize
    Accept := fun input =>
      FrontierViable
        system
        (frontierAt input) }

/--
AND/OR constitutive trajectories preserve the extensional decision between
their initial and final frontiers.
-/
theorem andOrTrajectory_projects_to_decision_equivalence
    {system : SearchSystem.{uState,uContinuation}}
    {Constitution : Type uConstitution}
    {Constitutes :
      Constitution →
        Constitution →
          Type uStep}
    {start finish :
      ConstitutiveState
        system
        Constitution}
    (trajectory :
      FrontierTrajectory
        system
        Constitutes
        start
        finish) :
    FrontierViable
        system
        start.frontier ↔
      FrontierViable
        system
        finish.frontier :=
  trajectory.viable_iff

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.DecisionProblem
#print axioms ConstitutiveSearch.PolynomialDecider
#print axioms ConstitutiveSearch.InP
#print axioms ConstitutiveSearch.PolynomialVerifier
#print axioms ConstitutiveSearch.InNP
#print axioms ConstitutiveSearch.searchSystemDecisionProblem
#print axioms ConstitutiveSearch.searchSystemDecisionProblem_accept_iff
#print axioms ConstitutiveSearch.SearchSystemPolynomialVerifier
#print axioms ConstitutiveSearch.SearchSystemPolynomialVerifier.toPolynomialVerifier
#print axioms ConstitutiveSearch.npLike_projects_to_InNP
#print axioms ConstitutiveSearch.SearchSystemPolynomialDecider
#print axioms ConstitutiveSearch.SearchSystemPolynomialDecider.toPolynomialDecider
#print axioms ConstitutiveSearch.pLike_projects_to_InP
#print axioms ConstitutiveSearch.frontierDecisionProblem
#print axioms ConstitutiveSearch.andOrTrajectory_projects_to_decision_equivalence
/- AXIOM_AUDIT_END -/
