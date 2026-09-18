import ConstitutiveSearch.ClosureSearchFixedFuelPolynomial

namespace ConstitutiveSearch.Tests.ClosureSearchFixedFuelPolynomialRegression

open ConstitutiveSearch

theorem primitiveFuel3At2 :
    (closurePrimitiveFixedFuelPolynomial 3).eval 2 =
      closurePrimitiveQueryBudget 2 3 :=
  closurePrimitiveFixedFuelPolynomial_eval 3 2

theorem compositionFuel3At2 :
    (closureCompositionFixedFuelPolynomial 3).eval 2 =
      closureCompositionCandidateBudget 2 3 :=
  closureCompositionFixedFuelPolynomial_eval 3 2

theorem primitiveFuel4Polynomial :
    PolynomiallyBounded
      (fun candidateCount =>
        closurePrimitiveQueryBudget
          candidateCount
          4) :=
  closurePrimitiveFixedFuel_polynomiallyBounded 4

theorem compositionFuel4Polynomial :
    PolynomiallyBounded
      (fun candidateCount =>
        closureCompositionCandidateBudget
          candidateCount
          4) :=
  closureCompositionFixedFuel_polynomiallyBounded 4

theorem primitiveInputBound :
    closurePrimitiveQueryBudget 3 4 ≤
      (closurePrimitiveFixedFuelPolynomial 4).eval 5 :=
  closurePrimitiveFixedFuel_le_inputPolynomial
    4
    3
    5
    (by
      exact
        Nat.le_trans
          (Nat.le_succ 3)
          (Nat.le_succ 4))


def quadraticCandidateCount
    (inputBits : Nat) : Nat :=
  inputBits * inputBits

theorem quadraticCandidateCount_inputPolynomial :
    InputPolynomiallyBounded
      (fun n => n)
      quadraticCandidateCount :=
  ⟨CostPolynomial.mul
      CostPolynomial.input
      CostPolynomial.input,
    fun _ =>
      Nat.le_refl _⟩

theorem primitiveFuel4_quadraticCandidates :
    InputPolynomiallyBounded
      (fun n => n)
      (fun n =>
        closurePrimitiveQueryBudget
          (quadraticCandidateCount n)
          4) :=
  closurePrimitiveFixedFuel_of_candidateInputPolynomial
    4
    quadraticCandidateCount_inputPolynomial

def boundedFuel : Nat → Nat
  | 0 => 0
  | _ + 1 => 2

theorem boundedFuel_le_two
    (n : Nat) :
    boundedFuel n ≤ 2 := by
  cases n with
  | zero =>
      exact Nat.zero_le 2
  | succ n =>
      exact Nat.le_refl 2

theorem compositionBoundedFuel_quadraticCandidates :
    InputPolynomiallyBounded
      (fun n => n)
      (fun n =>
        closureCompositionCandidateBudget
          (quadraticCandidateCount n)
          (boundedFuel n)) :=
  closureCompositionBoundedFuel_of_candidateInputPolynomial
    2
    quadraticCandidateCount_inputPolynomial
    boundedFuel_le_two

end ConstitutiveSearch.Tests.ClosureSearchFixedFuelPolynomialRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchFixedFuelPolynomialRegression.primitiveFuel3At2
#print axioms ConstitutiveSearch.Tests.ClosureSearchFixedFuelPolynomialRegression.compositionFuel3At2
#print axioms ConstitutiveSearch.Tests.ClosureSearchFixedFuelPolynomialRegression.primitiveFuel4Polynomial
#print axioms ConstitutiveSearch.Tests.ClosureSearchFixedFuelPolynomialRegression.compositionFuel4Polynomial
#print axioms ConstitutiveSearch.Tests.ClosureSearchFixedFuelPolynomialRegression.primitiveInputBound
#print axioms ConstitutiveSearch.Tests.ClosureSearchFixedFuelPolynomialRegression.quadraticCandidateCount_inputPolynomial
#print axioms ConstitutiveSearch.Tests.ClosureSearchFixedFuelPolynomialRegression.primitiveFuel4_quadraticCandidates
#print axioms ConstitutiveSearch.Tests.ClosureSearchFixedFuelPolynomialRegression.boundedFuel_le_two
#print axioms ConstitutiveSearch.Tests.ClosureSearchFixedFuelPolynomialRegression.compositionBoundedFuel_quadraticCandidates
/- AXIOM_AUDIT_END -/
