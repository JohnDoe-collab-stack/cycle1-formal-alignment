import ConstitutiveSearch.BitMachineAdequacyStress

namespace ConstitutiveSearch.Tests.BitMachineAdequacyStressRegression

open ConstitutiveSearch

/-- Same input, distinct certificate heads, distinct executed results. -/
theorem certificateAffectsResult :
    (executeBitMachineWithCertificate
        certificateEchoProgram [false, true] [true] 4).result? ≠
      (executeBitMachineWithCertificate
        certificateEchoProgram [false, true] [false] 4).result? :=
  certificateChannel_isOperational [false, true]

/-- Ten input cells produce ten retained work-tape cells. -/
theorem tenWorkCells :
    (executeBitMachine
      workGrowthProgram
      (falseBits 10)
      (workGrowthFuelPolynomial.eval (falseBits 10).length)).finalState.workLeft.length =
        10 := by
  rw [executeWorkGrowthProgram_workLength, falseBits_length]

/-- The work-tape stress gate has no global finite bound. -/
theorem noFixedWorkBound
    (bound : Nat) :
    exists input : List Bool,
      bound <
        (executeBitMachine
          workGrowthProgram
          input
          (workGrowthFuelPolynomial.eval input.length)).finalState.workLeft.length :=
  workTapeGrowth_unbounded bound

end ConstitutiveSearch.Tests.BitMachineAdequacyStressRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.BitMachineAdequacyStressRegression.certificateAffectsResult
#print axioms ConstitutiveSearch.Tests.BitMachineAdequacyStressRegression.tenWorkCells
#print axioms ConstitutiveSearch.Tests.BitMachineAdequacyStressRegression.noFixedWorkBound
/- AXIOM_AUDIT_END -/
