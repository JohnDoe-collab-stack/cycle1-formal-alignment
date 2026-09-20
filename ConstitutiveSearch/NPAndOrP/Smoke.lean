import ConstitutiveSearch.NPAndOrP.Regression

/-!
Non-confirmatory executable smoke checks. These observations are not proofs.
The deterministic input list is fixed here before running the checks.
-/

namespace ConstitutiveSearch.NPAndOrP

def smokeInputs : List Nat := [0, 1, 2, 4]

def smokeRows : List (Nat × Bool × Nat × Nat × Nat × Option Bool × Option Bool) :=
  smokeInputs.map fun input =>
    let run := executeConstitutiveResolution input
    (input, run.decision, run.stats.generatedSteps, run.stats.discoveryAttempts,
      run.measuredComparisonWork.total,
      run.projectionExperiment.positiveRun.terminalBit,
      run.projectionExperiment.negativeRun.terminalBit)

#eval smokeRows

end ConstitutiveSearch.NPAndOrP

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.NPAndOrP.smokeRows
/- AXIOM_AUDIT_END -/
