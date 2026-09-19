import ConstitutiveSearch.BitMachineDecision

namespace ConstitutiveSearch.Tests.BitMachineDecisionRegression

open ConstitutiveSearch

/-- The anti-cheat language is admitted by the traversal-capable interface. -/
theorem parityAdmitted :
    InBitMachineP bitParityProblem :=
  bitParity_inBitMachineP

/-- The certificate interface is non-vacuous and receives deterministic P. -/
theorem parityAdmittedByVerifier :
    InBitMachineNP bitParityProblem :=
  bitParity_inBitMachineNP

/-- A concrete even number of set bits yields the parity bit `false`. -/
theorem evenExample :
    (executeBitMachine
      bitParityProgram
      [true, false, true]
      (bitParityFuelPolynomial.eval 3)).result? =
        some false := by
  change
    (executeBitMachine
      bitParityProgram
      [true, false, true]
      (bitParityFuelPolynomial.eval [true, false, true].length)).result? =
        some false
  rw [executeBitParityProgram_result]
  rfl

/-- A concrete odd number of set bits yields the parity bit `true`. -/
theorem oddExample :
    (executeBitMachine
      bitParityProgram
      [true, false]
      (bitParityFuelPolynomial.eval 2)).result? =
        some true := by
  change
    (executeBitMachine
      bitParityProgram
      [true, false]
      (bitParityFuelPolynomial.eval [true, false].length)).result? =
        some true
  rw [executeBitParityProgram_result]
  rfl

/-- The interpreter, rather than syntax size, reports the exact growing cost. -/
theorem exactExecutedCost
    (input : List Bool) :
    bitParityPolynomialDecider.executedCost input =
      4 * input.length + 2 :=
  executeBitParityProgram_steps input

/-- Appending an input bit strictly increases actual executed work. -/
theorem costGrows
    (input : List Bool)
    (bit : Bool) :
    bitParityPolynomialDecider.executedCost input <
      bitParityPolynomialDecider.executedCost (input ++ [bit]) :=
  bitParityProgram_cost_strict_append input bit

end ConstitutiveSearch.Tests.BitMachineDecisionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.BitMachineDecisionRegression.parityAdmitted
#print axioms ConstitutiveSearch.Tests.BitMachineDecisionRegression.parityAdmittedByVerifier
#print axioms ConstitutiveSearch.Tests.BitMachineDecisionRegression.evenExample
#print axioms ConstitutiveSearch.Tests.BitMachineDecisionRegression.oddExample
#print axioms ConstitutiveSearch.Tests.BitMachineDecisionRegression.exactExecutedCost
#print axioms ConstitutiveSearch.Tests.BitMachineDecisionRegression.costGrows
/- AXIOM_AUDIT_END -/
