import ConstitutiveSearch.ClassicalDecisionComplexity

namespace ConstitutiveSearch.Tests.ClassicalDecisionComplexityPostAuditRegression

open ConstitutiveSearch

def zeroProblem : DecisionProblem :=
  { inputSize := fun input =>
      BinaryRepresentation.natBitSize input + 1
    Accept := fun input =>
      input = 0 }

def zeroDecider : PolynomialDecider zeroProblem :=
  { code := .inputEq 0
    correct := by
      intro input
      simp [executeDecider, zeroProblem] }

theorem positiveInP :
    InP zeroProblem :=
  ⟨zeroDecider⟩

theorem noFictionalZeroDeciderCost
    (code : DeciderCode)
    (input : Nat) :
    (executeDecider code input).stats.steps ≠ 0 :=
  executeDecider_steps_ne_zero code input

def zeroVerifier : PolynomialVerifier zeroProblem :=
  { code :=
      .both
        (.inputEq 0)
        (.witnessEq 0)
    certificateBound :=
      CostPolynomial.constant 1
    sound := by
      intro input witness verified
      by_cases inputZero : input = 0
      · exact inputZero
      · simp [
          executeVerifier,
          inputZero
        ] at verified
    complete := by
      intro input accepted
      subst input
      refine ⟨0, ?_, ?_⟩
      · decide
      · rfl }

theorem positiveInNP :
    InNP zeroProblem :=
  ⟨zeroVerifier⟩

theorem noFictionalZeroVerifierCost
    (code : VerifierCode)
    (input witness : Nat) :
    (executeVerifier
      code
      input
      witness).stats.steps ≠
        0 :=
  executeVerifier_steps_ne_zero
    code
    input
    witness

end ConstitutiveSearch.Tests.ClassicalDecisionComplexityPostAuditRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClassicalDecisionComplexityPostAuditRegression.zeroDecider
#print axioms ConstitutiveSearch.Tests.ClassicalDecisionComplexityPostAuditRegression.positiveInP
#print axioms ConstitutiveSearch.Tests.ClassicalDecisionComplexityPostAuditRegression.noFictionalZeroDeciderCost
#print axioms ConstitutiveSearch.Tests.ClassicalDecisionComplexityPostAuditRegression.zeroVerifier
#print axioms ConstitutiveSearch.Tests.ClassicalDecisionComplexityPostAuditRegression.positiveInNP
#print axioms ConstitutiveSearch.Tests.ClassicalDecisionComplexityPostAuditRegression.noFictionalZeroVerifierCost
/- AXIOM_AUDIT_END -/
