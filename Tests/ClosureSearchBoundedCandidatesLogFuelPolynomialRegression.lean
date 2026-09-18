import ConstitutiveSearch.ClosureSearchBoundedCandidatesLogFuelPolynomial

namespace ConstitutiveSearch.Tests.ClosureSearchBoundedCandidatesLogFuelPolynomialRegression

open ConstitutiveSearch

theorem geometricBaseTwo :
    closureGeometricBase 2 = 6 := by
  rfl

theorem boundedDegreeTwoThree :
    closureBoundedCandidateLogDegree
        2
        3 =
      18 := by
  rfl

theorem primitiveBudgetGeometric :
    ∀ fuel : Nat,
      closurePrimitiveQueryBudget
            2
            fuel +
          1 ≤
        6 ^ fuel := by
  intro fuel
  simpa only [
    geometricBaseTwo
  ] using
    closurePrimitiveQueryBudget_add_one_le_geometric
      2
      fuel

theorem compositionBudgetGeometric :
    ∀ fuel : Nat,
      closureCompositionCandidateBudget
            2
            fuel +
          1 ≤
        6 ^ fuel := by
  intro fuel
  simpa only [
    geometricBaseTwo
  ] using
    closureCompositionCandidateBudget_add_one_le_geometric
      2
      fuel

def candidateCountTwo
    (_n : Nat) : Nat :=
  2

theorem candidateCountTwoLe :
    ∀ n : Nat,
      candidateCountTwo n ≤ 2 := by
  intro n
  exact Nat.le_refl 2

theorem primitiveTwoCandidatesScaledLogPolynomial :
    InputPolynomiallyBounded
      logarithmicWitnessInputBits
      (fun n =>
        closurePrimitiveQueryBudget
          (candidateCountTwo n)
          (scaledLogarithmicWitnessFuel
            3
            n)) :=
  closurePrimitiveBoundedCandidates_scaledLogFuel_inputPolynomiallyBounded
    logarithmicWitnessInputBits
    candidateCountTwo
    (scaledLogarithmicWitnessFuel 3)
    2
    3
    logarithmicWitnessInputPositive
    candidateCountTwoLe
    (scaledLogarithmicWitnessFuel_le_scaledLog
      3)

theorem compositionTwoCandidatesScaledLogPolynomial :
    InputPolynomiallyBounded
      logarithmicWitnessInputBits
      (fun n =>
        closureCompositionCandidateBudget
          (candidateCountTwo n)
          (scaledLogarithmicWitnessFuel
            3
            n)) :=
  closureCompositionBoundedCandidates_scaledLogFuel_inputPolynomiallyBounded
    logarithmicWitnessInputBits
    candidateCountTwo
    (scaledLogarithmicWitnessFuel 3)
    2
    3
    logarithmicWitnessInputPositive
    candidateCountTwoLe
    (scaledLogarithmicWitnessFuel_le_scaledLog
      3)

abbrev DemoState
    (_n : Nat) : Type :=
  Nat

abbrev DemoGenerator
    (n : Nat)
    (_source _target : DemoState n) : Type :=
  Unit

def demoPrimitive
    (n : Nat) :
    RelationSearch
      (DemoGenerator n) :=
  { find := fun _source _target =>
      none }

def demoCandidates
    (n : Nat) :
    List (DemoState n) :=
  [0, 1]

def demoSource
    (n : Nat) :
    DemoState n :=
  0

def demoTarget
    (n : Nat) :
    DemoState n :=
  1

theorem demoCandidatesLe :
    ∀ n : Nat,
      (demoCandidates n).length ≤ 2 := by
  intro n
  change 2 ≤ 2
  exact Nat.le_refl 2

theorem executablePrimitiveScaledLogPolynomial :
    InputPolynomiallyBounded
      logarithmicWitnessInputBits
      (fun n =>
        (searchTransportClosureBounded
          (demoPrimitive n)
          (demoCandidates n)
          (scaledLogarithmicWitnessFuel
            3
            n)
          (demoSource n)
          (demoTarget n)).stats.primitiveQueries) :=
  searchTransportClosureBoundedCandidates_scaledLogFuel_primitiveQueries
    demoPrimitive
    demoCandidates
    (scaledLogarithmicWitnessFuel 3)
    logarithmicWitnessInputBits
    2
    3
    logarithmicWitnessInputPositive
    demoCandidatesLe
    (scaledLogarithmicWitnessFuel_le_scaledLog
      3)
    demoSource
    demoTarget

theorem executableCompositionScaledLogPolynomial :
    InputPolynomiallyBounded
      logarithmicWitnessInputBits
      (fun n =>
        (searchTransportClosureBounded
          (demoPrimitive n)
          (demoCandidates n)
          (scaledLogarithmicWitnessFuel
            3
            n)
          (demoSource n)
          (demoTarget n)).stats.compositionCandidates) :=
  searchTransportClosureBoundedCandidates_scaledLogFuel_compositionCandidates
    demoPrimitive
    demoCandidates
    (scaledLogarithmicWitnessFuel 3)
    logarithmicWitnessInputBits
    2
    3
    logarithmicWitnessInputPositive
    demoCandidatesLe
    (scaledLogarithmicWitnessFuel_le_scaledLog
      3)
    demoSource
    demoTarget

end ConstitutiveSearch.Tests.ClosureSearchBoundedCandidatesLogFuelPolynomialRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchBoundedCandidatesLogFuelPolynomialRegression.geometricBaseTwo
#print axioms ConstitutiveSearch.Tests.ClosureSearchBoundedCandidatesLogFuelPolynomialRegression.boundedDegreeTwoThree
#print axioms ConstitutiveSearch.Tests.ClosureSearchBoundedCandidatesLogFuelPolynomialRegression.primitiveBudgetGeometric
#print axioms ConstitutiveSearch.Tests.ClosureSearchBoundedCandidatesLogFuelPolynomialRegression.compositionBudgetGeometric
#print axioms ConstitutiveSearch.Tests.ClosureSearchBoundedCandidatesLogFuelPolynomialRegression.primitiveTwoCandidatesScaledLogPolynomial
#print axioms ConstitutiveSearch.Tests.ClosureSearchBoundedCandidatesLogFuelPolynomialRegression.compositionTwoCandidatesScaledLogPolynomial
#print axioms ConstitutiveSearch.Tests.ClosureSearchBoundedCandidatesLogFuelPolynomialRegression.executablePrimitiveScaledLogPolynomial
#print axioms ConstitutiveSearch.Tests.ClosureSearchBoundedCandidatesLogFuelPolynomialRegression.executableCompositionScaledLogPolynomial
/- AXIOM_AUDIT_END -/
