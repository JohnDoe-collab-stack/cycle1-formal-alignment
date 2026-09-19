import ConstitutiveSearch.BitMachineDecision

/-!
# Bit-machine adequacy stress gates

These executable gates strengthen the minimal parity regression without
claiming an equivalence theorem with every textbook presentation of P or NP.

* `certificateEchoProgram` proves that the certificate is a genuinely separate
  consumed channel whose contents affect the result.
* `workGrowthProgram` proves by an exact run equation that one fixed program
  creates an unbounded work-tape prefix while consuming unbounded input.

Together with parity, these facts rule out the finite-equality and finite-state
collapses found by the second audit.  A model-to-model simulation remains a
separate prerequisite for any future claim explicitly naming classical P/NP.
-/

namespace ConstitutiveSearch

/-! ## Separate certificate-channel gate -/

/-- Return the first certificate bit, or false when the certificate is empty. -/
def certificateEchoProgram : BitMachineProgram :=
  [ .branchCertificateEmpty 4 1,
    .setAccumulator false,
    .xorCertificateHeadIntoAccumulator,
    .haltAccumulator,
    .halt false ]

/-- Empty-certificate execution follows the explicit rejecting branch. -/
theorem certificateEcho_empty
    (input : List Bool) :
    (executeBitMachineWithCertificate
      certificateEchoProgram
      input
      []
      2).result? = some false := by
  rfl

/-- A true certificate head is observed and returned. -/
theorem certificateEcho_true
    (input tail : List Bool) :
    (executeBitMachineWithCertificate
      certificateEchoProgram
      input
      (true :: tail)
      4).result? = some true := by
  rfl

/-- A false certificate head is observed and returned. -/
theorem certificateEcho_false
    (input tail : List Bool) :
    (executeBitMachineWithCertificate
      certificateEchoProgram
      input
      (false :: tail)
      4).result? = some false := by
  rfl

/-- Changing only the certificate can change the result of the same program. -/
theorem certificateChannel_isOperational
    (input : List Bool) :
    (executeBitMachineWithCertificate
        certificateEchoProgram input [true] 4).result? ≠
      (executeBitMachineWithCertificate
        certificateEchoProgram input [false] 4).result? := by
  rw [certificateEcho_true, certificateEcho_false]
  intro impossible
  cases impossible

/-! ## Unbounded work-tape gate -/

/-- Repeatedly prepend true cells to an existing left work-tape segment. -/
def pushTrueCells : Nat → List Bool → List Bool
  | 0, tail => tail
  | count + 1, tail => pushTrueCells count (true :: tail)

/-- The produced work segment has exactly the requested additional length. -/
theorem pushTrueCells_length
    (count : Nat)
    (tail : List Bool) :
    (pushTrueCells count tail).length = count + tail.length := by
  induction count generalizing tail with
  | zero =>
      exact (Nat.zero_add tail.length).symm
  | succ count inductionHypothesis =>
      change
        (pushTrueCells count (true :: tail)).length =
          (count + 1) + tail.length
      rw [inductionHypothesis]
      exact
        Eq.trans
          (Nat.add_assoc count tail.length 1).symm
          (Nat.add_right_comm count tail.length 1)

/--
For every input bit: write true, move right, consume the input head, and loop.
The halt branch is taken only after the complete input has been consumed.
-/
def workGrowthProgram : BitMachineProgram :=
  [ .branchInputEmpty 5 1,
    .writeWorkCell true,
    .moveWorkRight,
    .dropHead,
    .jump 0,
    .halt true ]

/-- Exact fuel of the work-growth loop. -/
def workGrowthFuel : List Bool → Nat
  | [] => 2
  | _ :: rest => workGrowthFuel rest + 5

/-- Closed form for the exact work-growth fuel. -/
theorem workGrowthFuel_eq
    (input : List Bool) :
    workGrowthFuel input = 5 * input.length + 2 := by
  induction input with
  | nil =>
      rfl
  | cons head rest inductionHypothesis =>
      unfold workGrowthFuel
      rw [inductionHypothesis]
      change (5 * rest.length + 2) + 5 =
        5 * (rest.length + 1) + 2
      rw [Nat.mul_succ]

/-- Exact run from an arbitrary pre-existing left tape. -/
theorem runWorkGrowthProgram_exact
    (input : List Bool)
    (workLeft : List Bool) :
    runBitMachineFrom
        workGrowthProgram
        (workGrowthFuel input)
        { remainingInput := input
          remainingCertificate := []
          workLeft := workLeft
          workCell := false
          workRight := []
          accumulator := false
          programCounter := 0
          status := .running } =
      { result? := some true
        finalState :=
          { remainingInput := []
            remainingCertificate := []
            workLeft := pushTrueCells input.length workLeft
            workCell := false
            workRight := []
            accumulator := false
            programCounter := 5
            status := .halted true }
        stats :=
          { executedInstructions := workGrowthFuel input } } := by
  induction input generalizing workLeft with
  | nil =>
      rfl
  | cons head rest inductionHypothesis =>
      change
        (((((runBitMachineFrom
          workGrowthProgram
          (workGrowthFuel rest)
          { remainingInput := rest
            remainingCertificate := []
            workLeft := true :: workLeft
            workCell := false
            workRight := []
            accumulator := false
            programCounter := 0
            status := .running }).charge).charge).charge).charge).charge =
          { result? := some true
            finalState :=
              { remainingInput := []
                remainingCertificate := []
                workLeft :=
                  pushTrueCells (rest.length + 1) workLeft
                workCell := false
                workRight := []
                accumulator := false
                programCounter := 5
                status := .halted true }
            stats :=
              { executedInstructions := workGrowthFuel rest + 5 } }
      rw [inductionHypothesis]
      rfl

/-- Polynomial fuel expression for the work-growth program. -/
def workGrowthFuelPolynomial : CostPolynomial :=
  .add
    (.mul (.constant 5) .input)
    (.constant 2)

/-- The exact public run halts successfully on every input. -/
theorem executeWorkGrowthProgram_result
    (input : List Bool) :
    (executeBitMachine
      workGrowthProgram
      input
      (workGrowthFuelPolynomial.eval input.length)).result? =
        some true := by
  have exactRun := runWorkGrowthProgram_exact input []
  have exactResult := congrArg BitMachineRun.result? exactRun
  simpa [
    executeBitMachine,
    initialBitMachineState,
    initialBitMachineStateWithCertificate,
    workGrowthFuelPolynomial,
    CostPolynomial.eval,
    workGrowthFuel_eq
  ] using exactResult

/-- The final left work tape has exactly one produced cell per input bit. -/
theorem executeWorkGrowthProgram_workLength
    (input : List Bool) :
    (executeBitMachine
      workGrowthProgram
      input
      (workGrowthFuelPolynomial.eval input.length)).finalState.workLeft.length =
        input.length := by
  have exactRun := runWorkGrowthProgram_exact input []
  have exactTape :=
    congrArg
      (fun run : BitMachineRun => run.finalState.workLeft.length)
      exactRun
  rw [pushTrueCells_length] at exactTape
  simpa [
    executeBitMachine,
    initialBitMachineState,
    initialBitMachineStateWithCertificate,
    workGrowthFuelPolynomial,
    CostPolynomial.eval,
    workGrowthFuel_eq
  ] using exactTape

/-- Boolean input of an explicitly requested length. -/
def falseBits : Nat → List Bool
  | 0 => []
  | count + 1 => false :: falseBits count

/-- The explicit input constructor has the announced length. -/
theorem falseBits_length
    (count : Nat) :
    (falseBits count).length = count := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      change (falseBits count).length + 1 = count + 1
      exact congrArg (fun length => length + 1) inductionHypothesis

/-- No fixed bound contains the work tape produced by all inputs. -/
theorem workTapeGrowth_unbounded
    (bound : Nat) :
    exists input : List Bool,
      bound <
        (executeBitMachine
          workGrowthProgram
          input
          (workGrowthFuelPolynomial.eval input.length)).finalState.workLeft.length := by
  refine ⟨falseBits (bound + 1), ?_⟩
  rw [executeWorkGrowthProgram_workLength, falseBits_length]
  exact Nat.lt_succ_self bound

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.certificateEchoProgram
#print axioms ConstitutiveSearch.certificateChannel_isOperational
#print axioms ConstitutiveSearch.pushTrueCells_length
#print axioms ConstitutiveSearch.workGrowthProgram
#print axioms ConstitutiveSearch.workGrowthFuel_eq
#print axioms ConstitutiveSearch.runWorkGrowthProgram_exact
#print axioms ConstitutiveSearch.executeWorkGrowthProgram_result
#print axioms ConstitutiveSearch.executeWorkGrowthProgram_workLength
#print axioms ConstitutiveSearch.workTapeGrowth_unbounded
/- AXIOM_AUDIT_END -/
