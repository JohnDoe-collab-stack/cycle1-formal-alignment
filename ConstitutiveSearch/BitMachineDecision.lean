import ConstitutiveSearch.PolynomialCostEnvelope

/-!
# Executable bit-machine decision interface

This module supplies the post-second-audit reference machine for extensional
decision problems and certificate verification.  Programs are finite
instruction lists, execution is a fuel-bounded structural recursion, and the
reported cost is the number of instructions actually executed.  The machine
has separate one-way input and certificate streams plus an unbounded
bidirectional work tape.  The latter prevents the reference model from
collapsing to a finite-state recognizer.

Unlike the historical `DeciderCode`, one fixed program can traverse an input of
unbounded length.  Its executed cost may therefore depend genuinely on the
input.  The parity program at the end of the file is the mandatory minimal
anti-cheat regression.
-/

namespace ConstitutiveSearch

/-- Extensional decision problem over finite bit strings. -/
structure BitDecisionProblem where
  Accept : List Bool → Prop

/-- Instruction set of a small deterministic bit machine. -/
inductive BitMachineInstruction where
  | branchInputEmpty (emptyTarget nonemptyTarget : Nat)
  | xorHeadIntoAccumulator
  | dropHead
  | branchCertificateEmpty (emptyTarget nonemptyTarget : Nat)
  | xorCertificateHeadIntoAccumulator
  | dropCertificateHead
  | branchWorkCell (trueTarget falseTarget : Nat)
  | writeWorkCell (value : Bool)
  | moveWorkLeft
  | moveWorkRight
  | setAccumulator (value : Bool)
  | branchAccumulator (trueTarget falseTarget : Nat)
  | jump (target : Nat)
  | haltAccumulator
  | halt (value : Bool)
  deriving DecidableEq, Repr

/-- A machine program is finite syntax. -/
abbrev BitMachineProgram := List BitMachineInstruction

/-- Running, successfully halted, or stuck on an invalid operation/program counter. -/
inductive BitMachineStatus where
  | running
  | halted (result : Bool)
  | stuck
  deriving DecidableEq, Repr

/-- Complete state of the deterministic bit machine. -/
structure BitMachineState where
  remainingInput : List Bool
  remainingCertificate : List Bool
  workLeft : List Bool
  workCell : Bool
  workRight : List Bool
  accumulator : Bool
  programCounter : Nat
  status : BitMachineStatus
  deriving DecidableEq, Repr

/-- Statistics produced by the interpreter itself. -/
structure BitMachineStats where
  executedInstructions : Nat
  deriving DecidableEq, Repr

/-- Result, final state, and actual execution statistics. -/
structure BitMachineRun where
  result? : Option Bool
  finalState : BitMachineState
  stats : BitMachineStats
  deriving DecidableEq, Repr

/-- Boolean exclusive-or used by the accumulator instruction. -/
def bitXor (left right : Bool) : Bool :=
  if left then !right else right

/-- Initial machine state for one input. -/
def initialBitMachineStateWithCertificate
    (input certificate : List Bool) : BitMachineState :=
  { remainingInput := input
    remainingCertificate := certificate
    workLeft := []
    workCell := false
    workRight := []
    accumulator := false
    programCounter := 0
    status := .running }

/-- Initial decision state, with no certificate supplied. -/
def initialBitMachineState
    (input : List Bool) : BitMachineState :=
  initialBitMachineStateWithCertificate input []

/-- Result exposed by a stopped state. -/
def BitMachineState.result?
    (state : BitMachineState) : Option Bool :=
  match state.status with
  | .halted result => some result
  | .running => none
  | .stuck => none

/-- Structural list lookup used by the instruction fetch stage. -/
def bitMachineFetch :
    List BitMachineInstruction → Nat → Option BitMachineInstruction
  | [], _ => none
  | instruction :: _rest, 0 => some instruction
  | _instruction :: rest, index + 1 =>
      bitMachineFetch rest index

/-- Execute one instruction when the state is running. -/
def stepBitMachine
    (program : BitMachineProgram)
    (state : BitMachineState) : BitMachineState :=
  match state.status with
  | .halted _ => state
  | .stuck => state
  | .running =>
      match bitMachineFetch program state.programCounter with
      | none =>
          { state with status := .stuck }
      | some instruction =>
          match instruction with
          | .branchInputEmpty emptyTarget nonemptyTarget =>
              { state with
                programCounter :=
                  match state.remainingInput with
                  | [] => emptyTarget
                  | _ :: _ => nonemptyTarget }
          | .xorHeadIntoAccumulator =>
              match state.remainingInput with
              | [] =>
                  { state with status := .stuck }
              | head :: _ =>
                  { state with
                    accumulator := bitXor state.accumulator head
                    programCounter := state.programCounter + 1 }
          | .dropHead =>
              match state.remainingInput with
              | [] =>
                  { state with status := .stuck }
              | _ :: rest =>
                  { state with
                    remainingInput := rest
                    programCounter := state.programCounter + 1 }
          | .branchCertificateEmpty emptyTarget nonemptyTarget =>
              { state with
                programCounter :=
                  match state.remainingCertificate with
                  | [] => emptyTarget
                  | _ :: _ => nonemptyTarget }
          | .xorCertificateHeadIntoAccumulator =>
              match state.remainingCertificate with
              | [] =>
                  { state with status := .stuck }
              | head :: _ =>
                  { state with
                    accumulator := bitXor state.accumulator head
                    programCounter := state.programCounter + 1 }
          | .dropCertificateHead =>
              match state.remainingCertificate with
              | [] =>
                  { state with status := .stuck }
              | _ :: rest =>
                  { state with
                    remainingCertificate := rest
                    programCounter := state.programCounter + 1 }
          | .branchWorkCell trueTarget falseTarget =>
              { state with
                programCounter :=
                  if state.workCell then trueTarget else falseTarget }
          | .writeWorkCell value =>
              { state with
                workCell := value
                programCounter := state.programCounter + 1 }
          | .moveWorkLeft =>
              match state.workLeft with
              | [] =>
                  { state with
                    workCell := false
                    workRight := state.workCell :: state.workRight
                    programCounter := state.programCounter + 1 }
              | leftCell :: leftRest =>
                  { state with
                    workLeft := leftRest
                    workCell := leftCell
                    workRight := state.workCell :: state.workRight
                    programCounter := state.programCounter + 1 }
          | .moveWorkRight =>
              match state.workRight with
              | [] =>
                  { state with
                    workLeft := state.workCell :: state.workLeft
                    workCell := false
                    programCounter := state.programCounter + 1 }
              | rightCell :: rightRest =>
                  { state with
                    workLeft := state.workCell :: state.workLeft
                    workCell := rightCell
                    workRight := rightRest
                    programCounter := state.programCounter + 1 }
          | .setAccumulator value =>
              { state with
                accumulator := value
                programCounter := state.programCounter + 1 }
          | .branchAccumulator trueTarget falseTarget =>
              { state with
                programCounter :=
                  if state.accumulator then
                    trueTarget
                  else
                    falseTarget }
          | .jump target =>
              { state with programCounter := target }
          | .haltAccumulator =>
              { state with
                status := .halted state.accumulator }
          | .halt value =>
              { state with status := .halted value }

/-- Charge one actually executed instruction to a completed tail run. -/
def BitMachineRun.charge
    (run : BitMachineRun) : BitMachineRun :=
  { result? := run.result?
    finalState := run.finalState
    stats :=
      { executedInstructions :=
          run.stats.executedInstructions + 1 } }

/--
Fuel-bounded executable interpreter.

Recursion is structural on fuel.  A halted or stuck state short-circuits without
charging another instruction.
-/
def runBitMachineFrom
    (program : BitMachineProgram) :
    Nat → BitMachineState → BitMachineRun
  | 0, state =>
      { result? := state.result?
        finalState := state
        stats := { executedInstructions := 0 } }
  | fuel + 1, state =>
      match state.status with
      | .halted result =>
          { result? := some result
            finalState := state
            stats := { executedInstructions := 0 } }
      | .stuck =>
          { result? := none
            finalState := state
            stats := { executedInstructions := 0 } }
      | .running =>
          (runBitMachineFrom
            program
            fuel
            (stepBitMachine program state)).charge

/-- Execute a program from its canonical initial state. -/
def executeBitMachine
    (program : BitMachineProgram)
    (input : List Bool)
    (fuel : Nat) : BitMachineRun :=
  runBitMachineFrom
    program
    fuel
    (initialBitMachineState input)

/-- Execute the same machine with a separately supplied certificate stream. -/
def executeBitMachineWithCertificate
    (program : BitMachineProgram)
    (input certificate : List Bool)
    (fuel : Nat) : BitMachineRun :=
  runBitMachineFrom
    program
    fuel
    (initialBitMachineStateWithCertificate input certificate)

/-- Supplying the empty certificate is definitionally the decision execution. -/
theorem executeBitMachineWithCertificate_nil
    (program : BitMachineProgram)
    (input : List Bool)
    (fuel : Nat) :
    executeBitMachineWithCertificate program input [] fuel =
      executeBitMachine program input fuel :=
  rfl

/-- Actual interpreter work never exceeds the supplied fuel. -/
theorem runBitMachineFrom_steps_le_fuel
    (program : BitMachineProgram) :
    ∀ (fuel : Nat) (state : BitMachineState),
      (runBitMachineFrom
        program
        fuel
        state).stats.executedInstructions ≤ fuel
  | 0, _state =>
      Nat.zero_le 0
  | fuel + 1, state => by
      cases state with
      | mk remainingInput remainingCertificate workLeft workCell workRight
          accumulator programCounter status =>
        cases status with
        | running =>
            change
              (runBitMachineFrom
                program
                fuel
                (stepBitMachine program
                  { remainingInput := remainingInput
                    remainingCertificate := remainingCertificate
                    workLeft := workLeft
                    workCell := workCell
                    workRight := workRight
                    accumulator := accumulator
                    programCounter := programCounter
                    status := .running })).stats.executedInstructions + 1 ≤
                  fuel + 1
            exact
              Nat.succ_le_succ
                (runBitMachineFrom_steps_le_fuel
                  program
                  fuel
                  (stepBitMachine program
                    { remainingInput := remainingInput
                      remainingCertificate := remainingCertificate
                      workLeft := workLeft
                      workCell := workCell
                      workRight := workRight
                      accumulator := accumulator
                      programCounter := programCounter
                      status := .running }))
        | halted result =>
            exact Nat.zero_le _
        | stuck =>
            exact Nat.zero_le _

/-- Polynomial-time machine certificate relative to the actual interpreter. -/
structure PolynomialBitMachineDecider
    (problem : BitDecisionProblem) where
  program : BitMachineProgram
  fuelPolynomial : CostPolynomial
  halts :
    ∀ input : List Bool,
      ∃ result : Bool,
        (executeBitMachine
          program
          input
          (fuelPolynomial.eval input.length)).result? =
            some result
  correct :
    ∀ input : List Bool,
      (executeBitMachine
          program
          input
          (fuelPolynomial.eval input.length)).result? =
            some true ↔
        problem.Accept input

/-- Actual cost of the certified run on one input. -/
def PolynomialBitMachineDecider.executedCost
    {problem : BitDecisionProblem}
    (decider : PolynomialBitMachineDecider problem)
    (input : List Bool) : Nat :=
  (executeBitMachine
    decider.program
    input
    (decider.fuelPolynomial.eval input.length)).stats.executedInstructions

/-- Executed cost is bounded by the declared polynomial fuel. -/
theorem PolynomialBitMachineDecider.executedCost_le
    {problem : BitDecisionProblem}
    (decider : PolynomialBitMachineDecider problem)
    (input : List Bool) :
    decider.executedCost input ≤
      decider.fuelPolynomial.eval input.length :=
  runBitMachineFrom_steps_le_fuel
    decider.program
    (decider.fuelPolynomial.eval input.length)
    (initialBitMachineState input)

/-- Source-level polynomial decidability under the executable bit-machine model. -/
def InBitMachineP
    (problem : BitDecisionProblem) : Prop :=
  Nonempty (PolynomialBitMachineDecider problem)

/--
Polynomially bounded certificate verification on the same executable machine.

The certificate has its own stream, its length is bounded as a function of the
input length, and the actual verifier run is fuel-bounded by a polynomial of
the input length.  Both soundness and positive witness completeness refer to
that executed run.
-/
structure PolynomialBitMachineVerifier
    (problem : BitDecisionProblem) where
  program : BitMachineProgram
  certificateBound : CostPolynomial
  fuelPolynomial : CostPolynomial
  halts :
    ∀ (input certificate : List Bool),
      certificate.length ≤ certificateBound.eval input.length →
      ∃ result : Bool,
        (executeBitMachineWithCertificate
          program
          input
          certificate
          (fuelPolynomial.eval input.length)).result? =
            some result
  sound :
    ∀ (input certificate : List Bool),
      certificate.length ≤ certificateBound.eval input.length →
      (executeBitMachineWithCertificate
        program
        input
        certificate
        (fuelPolynomial.eval input.length)).result? =
          some true →
      problem.Accept input
  complete :
    ∀ input : List Bool,
      problem.Accept input →
      ∃ certificate : List Bool,
        certificate.length ≤ certificateBound.eval input.length /\
        (executeBitMachineWithCertificate
          program
          input
          certificate
          (fuelPolynomial.eval input.length)).result? =
            some true

/-- Actual interpreter work of a verifier on one concrete witness. -/
def PolynomialBitMachineVerifier.executedCost
    {problem : BitDecisionProblem}
    (verifier : PolynomialBitMachineVerifier problem)
    (input certificate : List Bool) : Nat :=
  (executeBitMachineWithCertificate
    verifier.program
    input
    certificate
    (verifier.fuelPolynomial.eval input.length)).stats.executedInstructions

/-- Executed verifier cost is bounded by its declared input polynomial. -/
theorem PolynomialBitMachineVerifier.executedCost_le
    {problem : BitDecisionProblem}
    (verifier : PolynomialBitMachineVerifier problem)
    (input certificate : List Bool) :
    verifier.executedCost input certificate ≤
      verifier.fuelPolynomial.eval input.length :=
  runBitMachineFrom_steps_le_fuel
    verifier.program
    (verifier.fuelPolynomial.eval input.length)
    (initialBitMachineStateWithCertificate input certificate)

/-- Source-level nondeterministic polynomial verification on the bit machine. -/
def InBitMachineNP
    (problem : BitDecisionProblem) : Prop :=
  Nonempty (PolynomialBitMachineVerifier problem)

/-- A bit list whose length is at most zero is empty. -/
theorem bitList_eq_nil_of_length_le_zero
    (bits : List Bool)
    (bounded : bits.length ≤ 0) :
    bits = [] := by
  cases bits with
  | nil =>
      rfl
  | cons head tail =>
      change Nat.succ tail.length ≤ 0 at bounded
      exact (Nat.not_succ_le_zero tail.length bounded).elim

/-- Every deterministic polynomial decider is a zero-certificate verifier. -/
def PolynomialBitMachineDecider.toVerifier
    {problem : BitDecisionProblem}
    (decider : PolynomialBitMachineDecider problem) :
    PolynomialBitMachineVerifier problem :=
  { program := decider.program
    certificateBound := .constant 0
    fuelPolynomial := decider.fuelPolynomial
    halts := by
      intro input certificate bounded
      have certificateEmpty : certificate = [] :=
        bitList_eq_nil_of_length_le_zero certificate bounded
      subst certificate
      rw [executeBitMachineWithCertificate_nil]
      exact decider.halts input
    sound := by
      intro input certificate bounded acceptedRun
      have certificateEmpty : certificate = [] :=
        bitList_eq_nil_of_length_le_zero certificate bounded
      subst certificate
      apply (decider.correct input).mp
      rw [← executeBitMachineWithCertificate_nil]
      exact acceptedRun
    complete := by
      intro input accepted
      refine ⟨[], Nat.zero_le 0, ?_⟩
      have acceptedRun := (decider.correct input).mpr accepted
      rw [executeBitMachineWithCertificate_nil]
      exact acceptedRun }

/-- Constructive inclusion of deterministic bit-machine P in its NP verifier class. -/
theorem bitMachineP_subset_bitMachineNP
    {problem : BitDecisionProblem}
    (decidable : InBitMachineP problem) :
    InBitMachineNP problem := by
  rcases decidable with ⟨decider⟩
  exact ⟨decider.toVerifier⟩

/-- Parity accumulated from one initial Boolean state. -/
def bitParityFrom : Bool → List Bool → Bool
  | accumulator, [] => accumulator
  | accumulator, head :: rest =>
      bitParityFrom (bitXor accumulator head) rest

/-- Parity of a finite bit string. -/
def bitParity (input : List Bool) : Bool :=
  bitParityFrom false input

/-- Mandatory nontrivial reference problem for the machine interface. -/
def bitParityProblem : BitDecisionProblem :=
  { Accept := fun input => bitParity input = true }

/--
Looping parity program:

* branch to halt when input is empty;
* xor the current head into the accumulator;
* consume the head;
* jump back to the branch.
-/
def bitParityProgram : BitMachineProgram :=
  [ .branchInputEmpty 4 1,
    .xorHeadIntoAccumulator,
    .dropHead,
    .jump 0,
    .haltAccumulator ]

/-- Exact fuel consumed by the parity loop. -/
def bitParityFuel : List Bool → Nat
  | [] => 2
  | _ :: rest => bitParityFuel rest + 4

/-- Closed form of the exact parity fuel. -/
theorem bitParityFuel_eq
    (input : List Bool) :
    bitParityFuel input = 4 * input.length + 2 := by
  induction input with
  | nil =>
      rfl
  | cons head rest inductionHypothesis =>
      unfold bitParityFuel
      rw [inductionHypothesis]
      change (4 * rest.length + 2) + 4 =
        4 * (rest.length + 1) + 2
      rw [Nat.mul_succ]

/-- Exact successful parity run from the loop head and an arbitrary accumulator. -/
theorem runBitParityProgram_exact
    (input : List Bool)
    (accumulator : Bool) :
    runBitMachineFrom
        bitParityProgram
        (bitParityFuel input)
        { remainingInput := input
          remainingCertificate := []
          workLeft := []
          workCell := false
          workRight := []
          accumulator := accumulator
          programCounter := 0
          status := .running } =
      { result? := some (bitParityFrom accumulator input)
        finalState :=
          { remainingInput := []
            remainingCertificate := []
            workLeft := []
            workCell := false
            workRight := []
            accumulator := bitParityFrom accumulator input
            programCounter := 4
            status := .halted (bitParityFrom accumulator input) }
        stats :=
          { executedInstructions := bitParityFuel input } } := by
  induction input generalizing accumulator with
  | nil =>
      rfl
  | cons head rest inductionHypothesis =>
      change
        ((((runBitMachineFrom
          bitParityProgram
          (bitParityFuel rest)
          { remainingInput := rest
            remainingCertificate := []
            workLeft := []
            workCell := false
            workRight := []
            accumulator := bitXor accumulator head
            programCounter := 0
            status := .running }).charge).charge).charge).charge =
          { result? :=
              some (bitParityFrom (bitXor accumulator head) rest)
            finalState :=
              { remainingInput := []
                remainingCertificate := []
                workLeft := []
                workCell := false
                workRight := []
                accumulator := bitParityFrom (bitXor accumulator head) rest
                programCounter := 4
                status :=
                  .halted (bitParityFrom (bitXor accumulator head) rest) }
            stats :=
              { executedInstructions := bitParityFuel rest + 4 } }
      rw [inductionHypothesis]
      rfl

/-- Polynomial fuel envelope used by the parity certificate. -/
def bitParityFuelPolynomial : CostPolynomial :=
  .add
    (.mul (.constant 4) .input)
    (.constant 2)

/-- The parity program returns the recursively specified parity result. -/
theorem executeBitParityProgram_result
    (input : List Bool) :
    (executeBitMachine
      bitParityProgram
      input
      (bitParityFuelPolynomial.eval input.length)).result? =
        some (bitParity input) := by
  have exactRun :=
    runBitParityProgram_exact
      input
      false
  have exactResult :=
    congrArg
      BitMachineRun.result?
      exactRun
  simpa [
    executeBitMachine,
    initialBitMachineState,
    initialBitMachineStateWithCertificate,
    bitParityFuelPolynomial,
    CostPolynomial.eval,
    bitParityFuel_eq,
    bitParity
  ] using exactResult

/-- The parity program performs exactly `4 * input.length + 2` instructions. -/
theorem executeBitParityProgram_steps
    (input : List Bool) :
    (executeBitMachine
      bitParityProgram
      input
      (bitParityFuelPolynomial.eval input.length)).stats.executedInstructions =
        4 * input.length + 2 := by
  have exactRun :=
    runBitParityProgram_exact
      input
      false
  have exactSteps :=
    congrArg
      (fun run : BitMachineRun =>
        run.stats.executedInstructions)
      exactRun
  simpa [
    executeBitMachine,
    initialBitMachineState,
    initialBitMachineStateWithCertificate,
    bitParityFuelPolynomial,
    CostPolynomial.eval,
    bitParityFuel_eq
  ] using exactSteps

/-- Local constructive length calculation, avoiding opaque library normalization. -/
theorem bitList_length_append_singleton
    (input : List Bool)
    (bit : Bool) :
    (input ++ [bit]).length = input.length + 1 := by
  induction input with
  | nil =>
      rfl
  | cons head rest inductionHypothesis =>
      change (rest ++ [bit]).length + 1 =
        (rest.length + 1) + 1
      rw [inductionHypothesis]

/-- Parity is decided by one fixed executable program with input-dependent cost. -/
def bitParityPolynomialDecider :
    PolynomialBitMachineDecider bitParityProblem :=
  { program := bitParityProgram
    fuelPolynomial := bitParityFuelPolynomial
    halts := by
      intro input
      exact
        ⟨bitParity input,
          executeBitParityProgram_result input⟩
    correct := by
      intro input
      rw [executeBitParityProgram_result]
      unfold bitParityProblem
      constructor
      · intro equalSome
        exact Option.some.inj equalSome
      · intro parityTrue
        rw [parityTrue] }

/-- Mandatory anti-cheat gate: parity inhabits the real executable P interface. -/
theorem bitParity_inBitMachineP :
    InBitMachineP bitParityProblem :=
  ⟨bitParityPolynomialDecider⟩

/-- The same concrete language also passes the certificate-verifier interface. -/
theorem bitParity_inBitMachineNP :
    InBitMachineNP bitParityProblem :=
  bitMachineP_subset_bitMachineNP bitParity_inBitMachineP

/-- Executed work genuinely grows when one more input bit is appended. -/
theorem bitParityProgram_cost_strict_append
    (input : List Bool)
    (bit : Bool) :
    bitParityPolynomialDecider.executedCost input <
      bitParityPolynomialDecider.executedCost (input ++ [bit]) := by
  unfold PolynomialBitMachineDecider.executedCost
  change
    (executeBitMachine
      bitParityProgram
      input
      (bitParityFuelPolynomial.eval input.length)).stats.executedInstructions <
    (executeBitMachine
      bitParityProgram
      (input ++ [bit])
      (bitParityFuelPolynomial.eval (input ++ [bit]).length)).stats.executedInstructions
  rw [
    executeBitParityProgram_steps,
    executeBitParityProgram_steps,
    bitList_length_append_singleton
  ]
  change
    4 * input.length + 2 <
      4 * (input.length + 1) + 2
  rw [Nat.mul_succ]
  exact
    Nat.add_lt_add_right
      (Nat.lt_add_of_pos_right (Nat.zero_lt_succ 3))
      2

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.BitDecisionProblem
#print axioms ConstitutiveSearch.BitMachineInstruction
#print axioms ConstitutiveSearch.BitMachineState
#print axioms ConstitutiveSearch.stepBitMachine
#print axioms ConstitutiveSearch.runBitMachineFrom
#print axioms ConstitutiveSearch.runBitMachineFrom_steps_le_fuel
#print axioms ConstitutiveSearch.executeBitMachineWithCertificate_nil
#print axioms ConstitutiveSearch.PolynomialBitMachineDecider
#print axioms ConstitutiveSearch.PolynomialBitMachineDecider.executedCost_le
#print axioms ConstitutiveSearch.PolynomialBitMachineVerifier
#print axioms ConstitutiveSearch.PolynomialBitMachineVerifier.executedCost_le
#print axioms ConstitutiveSearch.bitList_eq_nil_of_length_le_zero
#print axioms ConstitutiveSearch.PolynomialBitMachineDecider.toVerifier
#print axioms ConstitutiveSearch.bitMachineP_subset_bitMachineNP
#print axioms ConstitutiveSearch.bitParityFuel_eq
#print axioms ConstitutiveSearch.runBitParityProgram_exact
#print axioms ConstitutiveSearch.executeBitParityProgram_result
#print axioms ConstitutiveSearch.executeBitParityProgram_steps
#print axioms ConstitutiveSearch.bitList_length_append_singleton
#print axioms ConstitutiveSearch.bitParityPolynomialDecider
#print axioms ConstitutiveSearch.bitParity_inBitMachineP
#print axioms ConstitutiveSearch.bitParity_inBitMachineNP
#print axioms ConstitutiveSearch.bitParityProgram_cost_strict_append
/- AXIOM_AUDIT_END -/
