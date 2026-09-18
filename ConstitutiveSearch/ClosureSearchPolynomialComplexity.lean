import ConstitutiveSearch.PolynomialCostEnvelope
import ConstitutiveSearch.ClosureSearchPolynomialRegimes

/-!
# Polynomial witnesses for fixed-fuel closure search

ClosureSearchPolynomialRegimes gives explicit input-indexed event envelopes.
This module packages those envelopes in the generic PolynomiallyBounded
interface.

Thus the statement "fuel two with candidateCount <= inputBits is polynomial"
is represented by proof-carrying finite polynomial syntax rather than only by
an informal classification of the formulas.
-/

namespace ConstitutiveSearch

/-- Polynomial syntax for the fuel-two primitive-query envelope 2n+1. -/
def closureFuelTwoPrimitivePolynomial : CostPolynomial :=
  .add
    (.mul
      .input
      (.constant 2))
    (.constant 1)

/-- Polynomial syntax for the fuel-two composition envelope n(2n+1). -/
def closureFuelTwoCompositionPolynomial : CostPolynomial :=
  .mul
    .input
    (.add
      (.add
        .input
        .input)
      (.constant 1))

/-- Polynomial syntax for the combined fuel-two event envelope. -/
def closureFuelTwoTotalPolynomial : CostPolynomial :=
  .add
    closureFuelTwoPrimitivePolynomial
    closureFuelTwoCompositionPolynomial

/-- Primitive-query polynomial evaluates exactly to the declared input budget. -/
theorem closureFuelTwoPrimitivePolynomial_eval
    (inputBits : Nat) :
    closureFuelTwoPrimitivePolynomial.eval inputBits =
      closureFuelTwoPrimitiveInputBudget inputBits := by
  rfl

/-- Composition polynomial evaluates exactly to the declared input budget. -/
theorem closureFuelTwoCompositionPolynomial_eval
    (inputBits : Nat) :
    closureFuelTwoCompositionPolynomial.eval inputBits =
      closureFuelTwoCompositionInputBudget inputBits := by
  rfl

/-- Combined polynomial evaluates exactly to the declared total input budget. -/
theorem closureFuelTwoTotalPolynomial_eval
    (inputBits : Nat) :
    closureFuelTwoTotalPolynomial.eval inputBits =
      closureFuelTwoTotalInputBudget inputBits := by
  rfl

/-- The fixed-fuel-two primitive-query envelope is polynomially bounded. -/
theorem closureFuelTwoPrimitiveInputBudget_polynomiallyBounded :
    PolynomiallyBounded
      closureFuelTwoPrimitiveInputBudget :=
  ⟨closureFuelTwoPrimitivePolynomial,
    fun inputBits =>
      Nat.le_of_eq
        (closureFuelTwoPrimitivePolynomial_eval
          inputBits).symm⟩

/-- The fixed-fuel-two composition envelope is polynomially bounded. -/
theorem closureFuelTwoCompositionInputBudget_polynomiallyBounded :
    PolynomiallyBounded
      closureFuelTwoCompositionInputBudget :=
  ⟨closureFuelTwoCompositionPolynomial,
    fun inputBits =>
      Nat.le_of_eq
        (closureFuelTwoCompositionPolynomial_eval
          inputBits).symm⟩

/-- The combined fixed-fuel-two event envelope is polynomially bounded. -/
theorem closureFuelTwoTotalInputBudget_polynomiallyBounded :
    PolynomiallyBounded
      closureFuelTwoTotalInputBudget :=
  ⟨closureFuelTwoTotalPolynomial,
    fun inputBits =>
      Nat.le_of_eq
        (closureFuelTwoTotalPolynomial_eval
          inputBits).symm⟩

/--
Actual executable primitive-query count is covered directly by the polynomial
witness whenever the candidate-list length is bounded by inputBits.
-/
theorem searchTransportClosureFuelTwo_primitiveQueries_le_polynomial
    {State : Type}
    {Generator : State → State → Type}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (inputBits : Nat)
    (candidateLe :
      candidates.length ≤ inputBits)
    (source target : State) :
    (searchTransportClosureBounded
      primitive
      candidates
      2
      source
      target).stats.primitiveQueries ≤
      closureFuelTwoPrimitivePolynomial.eval inputBits := by
  rw [
    closureFuelTwoPrimitivePolynomial_eval
  ]
  exact
    searchTransportClosureFuelTwo_primitiveQueries_le_input
      primitive
      candidates
      inputBits
      candidateLe
      source
      target

/--
Actual executable composition-candidate count is covered by the quadratic
polynomial witness under the same regime.
-/
theorem searchTransportClosureFuelTwo_compositionCandidates_le_polynomial
    {State : Type}
    {Generator : State → State → Type}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (inputBits : Nat)
    (candidateLe :
      candidates.length ≤ inputBits)
    (source target : State) :
    (searchTransportClosureBounded
      primitive
      candidates
      2
      source
      target).stats.compositionCandidates ≤
      closureFuelTwoCompositionPolynomial.eval inputBits := by
  rw [
    closureFuelTwoCompositionPolynomial_eval
  ]
  exact
    searchTransportClosureFuelTwo_compositionCandidates_le_input
      primitive
      candidates
      inputBits
      candidateLe
      source
      target

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.closureFuelTwoPrimitivePolynomial
#print axioms ConstitutiveSearch.closureFuelTwoCompositionPolynomial
#print axioms ConstitutiveSearch.closureFuelTwoTotalPolynomial
#print axioms ConstitutiveSearch.closureFuelTwoPrimitivePolynomial_eval
#print axioms ConstitutiveSearch.closureFuelTwoCompositionPolynomial_eval
#print axioms ConstitutiveSearch.closureFuelTwoTotalPolynomial_eval
#print axioms ConstitutiveSearch.closureFuelTwoPrimitiveInputBudget_polynomiallyBounded
#print axioms ConstitutiveSearch.closureFuelTwoCompositionInputBudget_polynomiallyBounded
#print axioms ConstitutiveSearch.closureFuelTwoTotalInputBudget_polynomiallyBounded
#print axioms ConstitutiveSearch.searchTransportClosureFuelTwo_primitiveQueries_le_polynomial
#print axioms ConstitutiveSearch.searchTransportClosureFuelTwo_compositionCandidates_le_polynomial
/- AXIOM_AUDIT_END -/
