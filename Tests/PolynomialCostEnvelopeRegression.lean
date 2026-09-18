import ConstitutiveSearch.PolynomialCostEnvelope

namespace ConstitutiveSearch.Tests.PolynomialCostEnvelopeRegression

open ConstitutiveSearch

def linearPolynomial : CostPolynomial :=
  .add
    .input
    (.constant 1)

def linearCost
    (inputBits : Nat) : Nat :=
  inputBits + 1

theorem linearEval
    (inputBits : Nat) :
    linearPolynomial.eval inputBits =
      linearCost inputBits := by
  rfl

theorem linearBounded :
    PolynomiallyBounded linearCost :=
  ⟨linearPolynomial,
    fun _ =>
      Nat.le_refl _⟩

def doubledCost
    (inputBits : Nat) : Nat :=
  inputBits + inputBits

theorem doubledBounded :
    PolynomiallyBounded doubledCost := by
  exact
    PolynomiallyBounded.add
      PolynomiallyBounded.input
      PolynomiallyBounded.input

theorem productBounded :
    PolynomiallyBounded
      (fun inputBits =>
        linearCost inputBits *
          doubledCost inputBits) :=
  PolynomiallyBounded.mul
    linearBounded
    doubledBounded

theorem linearDegree :
    linearPolynomial.degree = 1 := by
  rfl

end ConstitutiveSearch.Tests.PolynomialCostEnvelopeRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.PolynomialCostEnvelopeRegression.linearEval
#print axioms ConstitutiveSearch.Tests.PolynomialCostEnvelopeRegression.linearBounded
#print axioms ConstitutiveSearch.Tests.PolynomialCostEnvelopeRegression.doubledBounded
#print axioms ConstitutiveSearch.Tests.PolynomialCostEnvelopeRegression.productBounded
#print axioms ConstitutiveSearch.Tests.PolynomialCostEnvelopeRegression.linearDegree
/- AXIOM_AUDIT_END -/
