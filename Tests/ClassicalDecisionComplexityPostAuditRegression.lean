import ConstitutiveSearch.ClassicalDecisionComplexity

/-!
Regression for the historical finite-equality code language.

The second audit showed that this interface must not be called classical P/NP.
These tests preserve only its exact executable facts.
-/

namespace ConstitutiveSearch.Tests.ClassicalDecisionComplexityPostAuditRegression

open ConstitutiveSearch

/-- Counterprobe 4 retained: fixed decider cost is independent of input. -/
theorem finiteEqualityDeciderCostIsInputIndependent
    (code : DeciderCode)
    (first second : Nat) :
    (executeDecider code first).stats.steps =
      (executeDecider code second).stats.steps := by
  rw [executeDecider_steps, executeDecider_steps]

/-- The exact cost is the finite syntax size. -/
theorem finiteEqualityDeciderCostIsSyntax
    (code : DeciderCode)
    (input : Nat) :
    (executeDecider code input).stats.steps = code.size :=
  executeDecider_steps code input

/-- The same limitation holds for the historical verifier code. -/
theorem finiteEqualityVerifierCostIsInputIndependent
    (code : VerifierCode)
    (firstInput secondInput witness : Nat) :
    (executeVerifier code firstInput witness).stats.steps =
      (executeVerifier code secondInput witness).stats.steps := by
  rw [executeVerifier_steps, executeVerifier_steps]

/-- Despite that limitation, fictional zero-cost annotations remain impossible. -/
theorem noFictionalZeroDeciderCost
    (code : DeciderCode)
    (input : Nat) :
    (executeDecider code input).stats.steps ≠ 0 :=
  executeDecider_steps_ne_zero code input

/-- Verifier runs likewise always charge their finite syntax. -/
theorem noFictionalZeroVerifierCost
    (code : VerifierCode)
    (input witness : Nat) :
    (executeVerifier code input witness).stats.steps ≠ 0 :=
  executeVerifier_steps_ne_zero code input witness

end ConstitutiveSearch.Tests.ClassicalDecisionComplexityPostAuditRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClassicalDecisionComplexityPostAuditRegression.finiteEqualityDeciderCostIsInputIndependent
#print axioms ConstitutiveSearch.Tests.ClassicalDecisionComplexityPostAuditRegression.finiteEqualityDeciderCostIsSyntax
#print axioms ConstitutiveSearch.Tests.ClassicalDecisionComplexityPostAuditRegression.finiteEqualityVerifierCostIsInputIndependent
#print axioms ConstitutiveSearch.Tests.ClassicalDecisionComplexityPostAuditRegression.noFictionalZeroDeciderCost
#print axioms ConstitutiveSearch.Tests.ClassicalDecisionComplexityPostAuditRegression.noFictionalZeroVerifierCost
/- AXIOM_AUDIT_END -/
