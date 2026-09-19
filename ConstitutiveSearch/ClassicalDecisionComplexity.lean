import ConstitutiveSearch.ConstitutiveComplexityInputPolynomial
import ConstitutiveSearch.FrontierTrajectory

/-!
# Minimal bridge to classical decision-complexity interfaces

This file introduces only the interfaces needed to state the final bridge.

The notions P and NP below are relative to an explicit input-size function and
an explicit source-level cost.  No concrete machine-runtime model is silently
assumed.

* P is witnessed by a correct Boolean decider whose announced cost is
  input-polynomial.
* NP is witnessed by a polynomially bounded certificate family and a correct
  verifier whose announced verification cost is polynomial on certificates
  within that bound.

A SearchSystem projects extensionally to the decision problem "is this state
viable?".  Its structural continuations are exactly the NP-like witness role.
A correct polynomial constitutive decider projects to P.

FrontierTrajectory supplies the AND/OR projection law: constitutive expansion,
accumulation and reduction preserve the extensional yes/no decision even though
they need not preserve the computational structure that produced it.
-/

namespace ConstitutiveSearch

universe uInput uWitness uState uContinuation uConstitution uStep

/-- Extensional decision problem with an explicit concrete input-size measure. -/
structure DecisionProblem where
  Input : Type uInput
  inputSize : Input → Nat
  Accept : Input → Prop

/-- Correct deterministic decision procedure with an announced polynomial cost. -/
structure PolynomialDecider
    (problem : DecisionProblem.{uInput}) where
  decide : problem.Input → Bool
  cost : problem.Input → Nat
  correct :
    ∀ input : problem.Input,
      decide input = true ↔
        problem.Accept input
  costPolynomial :
    InputPolynomiallyBounded
      problem.inputSize
      cost

/-- Classical P interface relative to the declared size and cost model. -/
def InP
    (problem : DecisionProblem.{uInput}) : Prop :=
  Nonempty
    (PolynomialDecider problem)

/--
Polynomial verifier interface.

Witness size is polynomially bounded in input size for positive instances.
Verifier cost is polynomial for witnesses within that announced bound.
-/
structure PolynomialVerifier
    (problem : DecisionProblem.{uInput}) where
  Witness :
    problem.Input →
      Type uWitness
  witnessSize :
    {input : problem.Input} →
      Witness input →
        Nat
  verify :
    (input : problem.Input) →
      Witness input →
        Bool
  cost :
    (input : problem.Input) →
      Witness input →
        Nat
  certificateBound :
    CostPolynomial
  verifierCostBound :
    CostPolynomial
  sound :
    ∀ (input : problem.Input)
      (witness : Witness input),
      verify input witness = true →
        problem.Accept input
  complete :
    ∀ input : problem.Input,
      problem.Accept input →
        ∃ witness : Witness input,
          witnessSize witness ≤
              certificateBound.eval
                (problem.inputSize input) ∧
            verify input witness = true
  costBound :
    ∀ (input : problem.Input)
      (witness : Witness input),
      witnessSize witness ≤
          certificateBound.eval
            (problem.inputSize input) →
        cost input witness ≤
          verifierCostBound.eval
            (problem.inputSize input)

/-- Classical NP interface relative to the declared size and verifier-cost model. -/
def InNP.{uInput,uWitness}
    (problem : DecisionProblem.{uInput}) : Prop :=
  Nonempty
    (PolynomialVerifier.{uInput,uWitness}
      problem)

/-- Extensional decision problem obtained by forgetting everything except viability. -/
def searchSystemDecisionProblem
    (system : SearchSystem.{uState,uContinuation})
    (stateSize : system.State → Nat) :
    DecisionProblem.{uState} :=
  { Input := system.State
    inputSize := stateSize
    Accept := system.Viable }

/-- The NP-like constitutive role is exactly existential accepted continuation. -/
theorem searchSystemDecisionProblem_accept_iff
    (system : SearchSystem.{uState,uContinuation})
    (stateSize : system.State → Nat)
    (state : system.State) :
    (searchSystemDecisionProblem
        system
        stateSize).Accept state ↔
      ∃ continuation :
          system.Continuation state,
        system.Accept
          state
          continuation := by
  rfl

/--
Data required to project the structural continuation role of a SearchSystem to
the classical NP verifier interface.

No such verifier is manufactured without these explicit size/cost hypotheses.
-/
structure SearchSystemPolynomialVerifier
    (system : SearchSystem.{uState,uContinuation})
    (stateSize : system.State → Nat) where
  continuationSize :
    {state : system.State} →
      system.Continuation state →
        Nat
  verify :
    (state : system.State) →
      system.Continuation state →
        Bool
  cost :
    (state : system.State) →
      system.Continuation state →
        Nat
  certificateBound :
    CostPolynomial
  verifierCostBound :
    CostPolynomial
  verifySound :
    ∀ (state : system.State)
      (continuation :
        system.Continuation state),
      verify state continuation = true →
        system.Accept
          state
          continuation
  verifyComplete :
    ∀ (state : system.State)
      (continuation :
        system.Continuation state),
      system.Accept
          state
          continuation →
        verify state continuation = true
  smallAcceptedWitness :
    ∀ state : system.State,
      system.Viable state →
        ∃ continuation :
            system.Continuation state,
          system.Accept
              state
              continuation ∧
            continuationSize continuation ≤
              certificateBound.eval
                (stateSize state)
  costBound :
    ∀ (state : system.State)
      (continuation :
        system.Continuation state),
      continuationSize continuation ≤
          certificateBound.eval
            (stateSize state) →
        cost state continuation ≤
          verifierCostBound.eval
            (stateSize state)

/-- Build the classical NP verifier from the explicit SearchSystem witness data. -/
def SearchSystemPolynomialVerifier.toPolynomialVerifier
    {system : SearchSystem.{uState,uContinuation}}
    {stateSize : system.State → Nat}
    (bridge :
      SearchSystemPolynomialVerifier
        system
        stateSize) :
    PolynomialVerifier.{uState,uContinuation}
      (searchSystemDecisionProblem
        system
        stateSize) :=
  { Witness :=
      system.Continuation
    witnessSize :=
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
      intro state continuation verified
      exact
        ⟨continuation,
          bridge.verifySound
            state
            continuation
            verified⟩
    complete := by
      intro state viable
      rcases
          bridge.smallAcceptedWitness
            state
            viable with
        ⟨continuation,
          accepted,
          sizeBound⟩
      exact
        ⟨continuation,
          sizeBound,
          bridge.verifyComplete
            state
            continuation
            accepted⟩
    costBound :=
      bridge.costBound }

/-- The NP-like continuation role projects to NP once its explicit verifier data hold. -/
theorem npLike_projects_to_InNP
    {system : SearchSystem.{uState,uContinuation}}
    {stateSize : system.State → Nat}
    (bridge :
      SearchSystemPolynomialVerifier
        system
        stateSize) :
    InNP.{uState,uContinuation}
      (searchSystemDecisionProblem
        system
        stateSize) :=
  ⟨bridge.toPolynomialVerifier⟩

/--
Data required to project a constitutive P-like procedure to the classical P
decider interface.
-/
structure SearchSystemPolynomialDecider
    (system : SearchSystem.{uState,uContinuation})
    (stateSize : system.State → Nat) where
  decide :
    system.State → Bool
  cost :
    system.State → Nat
  correct :
    ∀ state : system.State,
      decide state = true ↔
        system.Viable state
  costPolynomial :
    InputPolynomiallyBounded
      stateSize
      cost

/-- Build the classical P decider from the explicit constitutive decision procedure. -/
def SearchSystemPolynomialDecider.toPolynomialDecider
    {system : SearchSystem.{uState,uContinuation}}
    {stateSize : system.State → Nat}
    (bridge :
      SearchSystemPolynomialDecider
        system
        stateSize) :
    PolynomialDecider
      (searchSystemDecisionProblem
        system
        stateSize) :=
  { decide :=
      bridge.decide
    cost :=
      bridge.cost
    correct :=
      bridge.correct
    costPolynomial :=
      bridge.costPolynomial }

/-- The P-like role projects to P exactly when a correct polynomial decider is supplied. -/
theorem pLike_projects_to_InP
    {system : SearchSystem.{uState,uContinuation}}
    {stateSize : system.State → Nat}
    (bridge :
      SearchSystemPolynomialDecider
        system
        stateSize) :
    InP
      (searchSystemDecisionProblem
        system
        stateSize) :=
  ⟨bridge.toPolynomialDecider⟩

/-- Decision problem on frontiers obtained by forgetting constitutive history. -/
def frontierDecisionProblem
    (system : SearchSystem.{uState,uContinuation})
    (frontierSize :
      List system.State → Nat) :
    DecisionProblem :=
  { Input :=
      List system.State
    inputSize :=
      frontierSize
    Accept :=
      FrontierViable system }

/--
AND/OR constitutive trajectories project to equality of the extensional
decision answer between their initial and final frontiers.
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
