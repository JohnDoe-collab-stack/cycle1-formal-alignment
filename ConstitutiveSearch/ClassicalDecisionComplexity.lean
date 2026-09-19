import ConstitutiveSearch.ConstitutiveComplexityInputPolynomial
import ConstitutiveSearch.FrontierTrajectory
import ConstitutiveSearch.RepresentationCost

/-!
# Historical finite-equality decision-code interface

Post-audit repair: cost is no longer an independent field attached to an
arbitrary Boolean function.

A decider or verifier is finite syntax interpreted by an executable semantics.
The interpreter returns both the Boolean result and source-level statistics.
Polynomial cost is defined from those statistics.

The language is deliberately minimal.  It prevents the pre-audit construction

  decide := arbitraryFunction
  cost := 0

because there is no independently supplied cost function and no constructor
embedding an arbitrary Boolean callback.

The second adversarial audit proved that these codes express only
finite/cofinite languages and that their executed cost is input-independent.
Accordingly, the exported membership predicates below are explicitly named
`InFiniteEqualityP` and `InFiniteEqualityNP`.  They are historical bounded
code-language interfaces, not definitions of classical P or NP.
-/

namespace ConstitutiveSearch

universe uState uContinuation uConstitution uStep

/-- Nat-coded extensional decision problem with a concrete encoded input size. -/
structure DecisionProblem where
  inputSize : Nat → Nat
  Accept : Nat → Prop

/-- Source-level execution statistics. -/
structure DecisionExecutionStats where
  steps : Nat

/-- Boolean result together with statistics produced by actual execution. -/
structure DecisionExecutionRun where
  result : Bool
  stats : DecisionExecutionStats

/--
Finite deterministic decider syntax.

No constructor embeds an arbitrary Nat -> Bool callback.
-/
inductive DeciderCode where
  | returnBool (value : Bool)
  | inputEq (expected : Nat)
  | negate (code : DeciderCode)
  | both (left right : DeciderCode)
  | either (left right : DeciderCode)

/-- Static source-level instruction count of one decider code. -/
def DeciderCode.size : DeciderCode → Nat
  | .returnBool _ =>
      1
  | .inputEq _ =>
      1
  | .negate code =>
      code.size + 1
  | .both left right =>
      left.size + right.size + 1
  | .either left right =>
      left.size + right.size + 1

/-- Every decider code contains at least one charged instruction. -/
theorem DeciderCode.size_pos
    (code : DeciderCode) :
    0 < code.size := by
  induction code with
  | returnBool value =>
      exact Nat.zero_lt_succ 0
  | inputEq expected =>
      exact Nat.zero_lt_succ 0
  | negate code inductionHypothesis =>
      exact Nat.zero_lt_succ code.size
  | both left right leftIH rightIH =>
      exact Nat.zero_lt_succ (left.size + right.size)
  | either left right leftIH rightIH =>
      exact Nat.zero_lt_succ (left.size + right.size)

/-- Executable semantics of the finite decider language. -/
def executeDecider :
    DeciderCode →
      Nat →
        DecisionExecutionRun
  | .returnBool value, _input =>
      { result := value
        stats := { steps := 1 } }
  | .inputEq expected, input =>
      { result :=
          if input = expected then
            true
          else
            false
        stats := { steps := 1 } }
  | .negate code, input =>
      let run :=
        executeDecider
          code
          input
      { result := !run.result
        stats :=
          { steps :=
              run.stats.steps + 1 } }
  | .both left right, input =>
      let leftRun :=
        executeDecider
          left
          input
      let rightRun :=
        executeDecider
          right
          input
      { result :=
          leftRun.result &&
            rightRun.result
        stats :=
          { steps :=
              leftRun.stats.steps +
                rightRun.stats.steps +
                  1 } }
  | .either left right, input =>
      let leftRun :=
        executeDecider
          left
          input
      let rightRun :=
        executeDecider
          right
          input
      { result :=
          leftRun.result ||
            rightRun.result
        stats :=
          { steps :=
              leftRun.stats.steps +
                rightRun.stats.steps +
                  1 } }

/-- Executed decider cost is exactly the syntax size; no independent cost exists. -/
theorem executeDecider_steps
    (code : DeciderCode)
    (input : Nat) :
    (executeDecider
      code
      input).stats.steps =
        code.size := by
  induction code with
  | returnBool value =>
      rfl
  | inputEq expected =>
      rfl
  | negate code inductionHypothesis =>
      change
        (executeDecider code input).stats.steps + 1 =
          code.size + 1
      rw [inductionHypothesis]
  | both left right leftIH rightIH =>
      change
        (executeDecider left input).stats.steps +
              (executeDecider right input).stats.steps + 1 =
          left.size + right.size + 1
      rw [leftIH, rightIH]
  | either left right leftIH rightIH =>
      change
        (executeDecider left input).stats.steps +
              (executeDecider right input).stats.steps + 1 =
          left.size + right.size + 1
      rw [leftIH, rightIH]

/-- The old fictional zero-cost probe is impossible for every executable decider. -/
theorem executeDecider_steps_ne_zero
    (code : DeciderCode)
    (input : Nat) :
    (executeDecider
      code
      input).stats.steps ≠
        0 := by
  rw [
    executeDecider_steps
  ]
  exact
    Nat.ne_of_gt
      code.size_pos

/-- Every fixed finite decider has an input-polynomial executed step count. -/
theorem executeDecider_inputPolynomiallyBounded
    (problem : DecisionProblem)
    (code : DeciderCode) :
    InputPolynomiallyBounded
      problem.inputSize
      (fun input =>
        (executeDecider
          code
          input).stats.steps) := by
  refine
    ⟨CostPolynomial.constant
        code.size,
      ?_⟩
  intro input
  change
    (executeDecider
        code
        input).stats.steps ≤
      (CostPolynomial.constant
        code.size).eval
          (problem.inputSize input)
  rw [
    executeDecider_steps
  ]
  exact
    Nat.le_refl _

/--
Correct deterministic decision procedure.

There is no cost field.  Complexity is derived from executeDecider.
-/
structure FiniteEqualityPolynomialDecider
    (problem : DecisionProblem) where
  code : DeciderCode
  correct :
    ∀ input : Nat,
      (executeDecider
        code
        input).result =
          true ↔
        problem.Accept input

/-- Executed cost function induced by a polynomial decider. -/
def FiniteEqualityPolynomialDecider.executedCost
    {problem : DecisionProblem}
    (decider : FiniteEqualityPolynomialDecider problem)
    (input : Nat) : Nat :=
  (executeDecider
    decider.code
    input).stats.steps

/-- Polynomial cost follows from the actual interpreter run. -/
theorem FiniteEqualityPolynomialDecider.executedCostPolynomial
    {problem : DecisionProblem}
    (decider : FiniteEqualityPolynomialDecider problem) :
    InputPolynomiallyBounded
      problem.inputSize
      decider.executedCost :=
  executeDecider_inputPolynomiallyBounded
    problem
    decider.code

/-- Membership in the historical finite-equality decider language. -/
def InFiniteEqualityP
    (problem : DecisionProblem) : Prop :=
  Nonempty
    (FiniteEqualityPolynomialDecider problem)

/--
Finite verifier syntax over Nat-coded input and Nat-coded certificate.

Again, no arbitrary callback constructor exists.
-/
inductive VerifierCode where
  | returnBool (value : Bool)
  | inputEq (expected : Nat)
  | witnessEq (expected : Nat)
  | inputEqWitness
  | negate (code : VerifierCode)
  | both (left right : VerifierCode)
  | either (left right : VerifierCode)

/-- Static source-level instruction count of one verifier code. -/
def VerifierCode.size : VerifierCode → Nat
  | .returnBool _ =>
      1
  | .inputEq _ =>
      1
  | .witnessEq _ =>
      1
  | .inputEqWitness =>
      1
  | .negate code =>
      code.size + 1
  | .both left right =>
      left.size + right.size + 1
  | .either left right =>
      left.size + right.size + 1

theorem VerifierCode.size_pos
    (code : VerifierCode) :
    0 < code.size := by
  induction code with
  | returnBool value =>
      exact Nat.zero_lt_succ 0
  | inputEq expected =>
      exact Nat.zero_lt_succ 0
  | witnessEq expected =>
      exact Nat.zero_lt_succ 0
  | inputEqWitness =>
      exact Nat.zero_lt_succ 0
  | negate code inductionHypothesis =>
      exact Nat.zero_lt_succ code.size
  | both left right leftIH rightIH =>
      exact Nat.zero_lt_succ (left.size + right.size)
  | either left right leftIH rightIH =>
      exact Nat.zero_lt_succ (left.size + right.size)

/-- Executable verifier semantics. -/
def executeVerifier :
    VerifierCode →
      Nat →
        Nat →
          DecisionExecutionRun
  | .returnBool value, _input, _witness =>
      { result := value
        stats := { steps := 1 } }
  | .inputEq expected, input, _witness =>
      { result :=
          if input = expected then
            true
          else
            false
        stats := { steps := 1 } }
  | .witnessEq expected, _input, witness =>
      { result :=
          if witness = expected then
            true
          else
            false
        stats := { steps := 1 } }
  | .inputEqWitness, input, witness =>
      { result :=
          if input = witness then
            true
          else
            false
        stats := { steps := 1 } }
  | .negate code, input, witness =>
      let run :=
        executeVerifier
          code
          input
          witness
      { result := !run.result
        stats :=
          { steps :=
              run.stats.steps + 1 } }
  | .both left right, input, witness =>
      let leftRun :=
        executeVerifier
          left
          input
          witness
      let rightRun :=
        executeVerifier
          right
          input
          witness
      { result :=
          leftRun.result &&
            rightRun.result
        stats :=
          { steps :=
              leftRun.stats.steps +
                rightRun.stats.steps +
                  1 } }
  | .either left right, input, witness =>
      let leftRun :=
        executeVerifier
          left
          input
          witness
      let rightRun :=
        executeVerifier
          right
          input
          witness
      { result :=
          leftRun.result ||
            rightRun.result
        stats :=
          { steps :=
              leftRun.stats.steps +
                rightRun.stats.steps +
                  1 } }

/-- Executed verifier cost is exactly syntax size. -/
theorem executeVerifier_steps
    (code : VerifierCode)
    (input witness : Nat) :
    (executeVerifier
      code
      input
      witness).stats.steps =
        code.size := by
  induction code with
  | returnBool value =>
      rfl
  | inputEq expected =>
      rfl
  | witnessEq expected =>
      rfl
  | inputEqWitness =>
      rfl
  | negate code inductionHypothesis =>
      change
        (executeVerifier code input witness).stats.steps + 1 =
          code.size + 1
      rw [inductionHypothesis]
  | both left right leftIH rightIH =>
      change
        (executeVerifier left input witness).stats.steps +
              (executeVerifier right input witness).stats.steps + 1 =
          left.size + right.size + 1
      rw [leftIH, rightIH]
  | either left right leftIH rightIH =>
      change
        (executeVerifier left input witness).stats.steps +
              (executeVerifier right input witness).stats.steps + 1 =
          left.size + right.size + 1
      rw [leftIH, rightIH]

/-- The analogous fictional zero-cost verifier probe is impossible. -/
theorem executeVerifier_steps_ne_zero
    (code : VerifierCode)
    (input witness : Nat) :
    (executeVerifier
      code
      input
      witness).stats.steps ≠
        0 := by
  rw [
    executeVerifier_steps
  ]
  exact
    Nat.ne_of_gt
      code.size_pos

/--
Polynomial verifier relative to Nat-coded certificates.

Certificate size is the concrete binary representation size.  Verification
cost is not supplied: it is the executed interpreter step count.
-/
structure FiniteEqualityPolynomialVerifier
    (problem : DecisionProblem) where
  code : VerifierCode
  certificateBound :
    CostPolynomial
  sound :
    ∀ (input witness : Nat),
      (executeVerifier
        code
        input
        witness).result =
          true →
        problem.Accept input
  complete :
    ∀ input : Nat,
      problem.Accept input →
        ∃ witness : Nat,
          BinaryRepresentation.natBitSize
              witness ≤
            certificateBound.eval
              (problem.inputSize input) ∧
          (executeVerifier
            code
            input
            witness).result =
              true

/-- Executed verifier cost function. -/
def FiniteEqualityPolynomialVerifier.executedCost
    {problem : DecisionProblem}
    (verifier : FiniteEqualityPolynomialVerifier problem)
    (input witness : Nat) : Nat :=
  (executeVerifier
    verifier.code
    input
    witness).stats.steps

/--
On every certificate, verifier execution cost is bounded by one constant
polynomial derived from the actual code syntax.
-/
theorem FiniteEqualityPolynomialVerifier.executedCostBound
    {problem : DecisionProblem}
    (verifier : FiniteEqualityPolynomialVerifier problem)
    (input witness : Nat) :
    verifier.executedCost
        input
        witness ≤
      (CostPolynomial.constant
        verifier.code.size).eval
          (problem.inputSize input) := by
  unfold FiniteEqualityPolynomialVerifier.executedCost
  rw [
    executeVerifier_steps
  ]
  exact
    Nat.le_refl _

/-- Membership in the historical finite-equality verifier language. -/
def InFiniteEqualityNP
    (problem : DecisionProblem) : Prop :=
  Nonempty
    (FiniteEqualityPolynomialVerifier problem)

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
Executable NP-like bridge.

The verifier code is fixed syntax.  Soundness and completeness connect its
Nat-coded certificates to accepted structural continuations.
-/
structure SearchSystemFiniteEqualityVerifier
    (system : SearchSystem.{uState,uContinuation})
    (stateAt : Nat → system.State)
    (inputSize : Nat → Nat) where
  code : VerifierCode
  certificateBound :
    CostPolynomial
  decode :
    (input witness : Nat) →
      Option
        (system.Continuation
          (stateAt input))
  verifySound :
    ∀ (input witness : Nat),
      (executeVerifier
        code
        input
        witness).result =
          true →
        ∃ continuation :
            system.Continuation
              (stateAt input),
          decode input witness =
              some continuation ∧
            system.Accept
              (stateAt input)
              continuation
  verifyComplete :
    ∀ input : Nat,
      system.Viable
          (stateAt input) →
        ∃ witness : Nat,
          BinaryRepresentation.natBitSize
              witness ≤
            certificateBound.eval
              (inputSize input) ∧
          (executeVerifier
            code
            input
            witness).result =
              true

def SearchSystemFiniteEqualityVerifier.toFiniteEqualityVerifier
    {system : SearchSystem.{uState,uContinuation}}
    {stateAt : Nat → system.State}
    {inputSize : Nat → Nat}
    (bridge :
      SearchSystemFiniteEqualityVerifier
        system
        stateAt
        inputSize) :
    FiniteEqualityPolynomialVerifier
      (searchSystemDecisionProblem
        system
        stateAt
        inputSize) :=
  { code :=
      bridge.code
    certificateBound :=
      bridge.certificateBound
    sound := by
      intro input witness verified
      rcases
          bridge.verifySound
            input
            witness
            verified with
        ⟨continuation,
          _decoded,
          accepted⟩
      exact
        ⟨continuation,
          accepted⟩
    complete := by
      intro input viable
      exact
        bridge.verifyComplete
          input
          viable }

theorem npLike_projects_to_finiteEqualityNP
    {system : SearchSystem.{uState,uContinuation}}
    {stateAt : Nat → system.State}
    {inputSize : Nat → Nat}
    (bridge :
      SearchSystemFiniteEqualityVerifier
        system
        stateAt
        inputSize) :
    InFiniteEqualityNP
      (searchSystemDecisionProblem
        system
        stateAt
        inputSize) :=
  ⟨bridge.toFiniteEqualityVerifier⟩

/-- Executable P-like bridge: only code and correctness are supplied. -/
structure SearchSystemFiniteEqualityDecider
    (system : SearchSystem.{uState,uContinuation})
    (stateAt : Nat → system.State)
    (inputSize : Nat → Nat) where
  code : DeciderCode
  correct :
    ∀ input : Nat,
      (executeDecider
        code
        input).result =
          true ↔
        system.Viable
          (stateAt input)

def SearchSystemFiniteEqualityDecider.toFiniteEqualityDecider
    {system : SearchSystem.{uState,uContinuation}}
    {stateAt : Nat → system.State}
    {inputSize : Nat → Nat}
    (bridge :
      SearchSystemFiniteEqualityDecider
        system
        stateAt
        inputSize) :
    FiniteEqualityPolynomialDecider
      (searchSystemDecisionProblem
        system
        stateAt
        inputSize) :=
  { code :=
      bridge.code
    correct :=
      bridge.correct }

theorem pLike_projects_to_finiteEqualityP
    {system : SearchSystem.{uState,uContinuation}}
    {stateAt : Nat → system.State}
    {inputSize : Nat → Nat}
    (bridge :
      SearchSystemFiniteEqualityDecider
        system
        stateAt
        inputSize) :
    InFiniteEqualityP
      (searchSystemDecisionProblem
        system
        stateAt
        inputSize) :=
  ⟨bridge.toFiniteEqualityDecider⟩

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
#print axioms ConstitutiveSearch.DecisionExecutionStats
#print axioms ConstitutiveSearch.DecisionExecutionRun
#print axioms ConstitutiveSearch.DeciderCode
#print axioms ConstitutiveSearch.DeciderCode.size
#print axioms ConstitutiveSearch.executeDecider
#print axioms ConstitutiveSearch.executeDecider_steps
#print axioms ConstitutiveSearch.executeDecider_steps_ne_zero
#print axioms ConstitutiveSearch.FiniteEqualityPolynomialDecider
#print axioms ConstitutiveSearch.FiniteEqualityPolynomialDecider.executedCost
#print axioms ConstitutiveSearch.FiniteEqualityPolynomialDecider.executedCostPolynomial
#print axioms ConstitutiveSearch.InFiniteEqualityP
#print axioms ConstitutiveSearch.VerifierCode
#print axioms ConstitutiveSearch.VerifierCode.size
#print axioms ConstitutiveSearch.executeVerifier
#print axioms ConstitutiveSearch.executeVerifier_steps
#print axioms ConstitutiveSearch.executeVerifier_steps_ne_zero
#print axioms ConstitutiveSearch.FiniteEqualityPolynomialVerifier
#print axioms ConstitutiveSearch.FiniteEqualityPolynomialVerifier.executedCost
#print axioms ConstitutiveSearch.FiniteEqualityPolynomialVerifier.executedCostBound
#print axioms ConstitutiveSearch.InFiniteEqualityNP
#print axioms ConstitutiveSearch.searchSystemDecisionProblem
#print axioms ConstitutiveSearch.SearchSystemFiniteEqualityVerifier
#print axioms ConstitutiveSearch.SearchSystemFiniteEqualityVerifier.toFiniteEqualityVerifier
#print axioms ConstitutiveSearch.npLike_projects_to_finiteEqualityNP
#print axioms ConstitutiveSearch.SearchSystemFiniteEqualityDecider
#print axioms ConstitutiveSearch.SearchSystemFiniteEqualityDecider.toFiniteEqualityDecider
#print axioms ConstitutiveSearch.pLike_projects_to_finiteEqualityP
#print axioms ConstitutiveSearch.frontierDecisionProblem
#print axioms ConstitutiveSearch.andOrTrajectory_projects_to_decision_equivalence
/- AXIOM_AUDIT_END -/
