import ConstitutiveSearch.ClosureSearchPolynomialRegimes

namespace ConstitutiveSearch.Tests.ClosureSearchPolynomialRegimesRegression

open ConstitutiveSearch

inductive NoRelation : Nat → Nat → Type

def noSearch : RelationSearch NoRelation :=
  { find := fun _ _ => none }

def candidates : List Nat := [0, 1, 2]

theorem primitiveBudget3 :
    closureFuelTwoPrimitiveInputBudget 3 = 7 := by
  rfl

theorem compositionBudget3 :
    closureFuelTwoCompositionInputBudget 3 = 21 := by
  rfl

theorem totalBudget3 :
    closureFuelTwoTotalInputBudget 3 = 28 := by
  rfl

theorem candidateLength3 :
    candidates.length ≤ 3 := by
  exact Nat.le_refl 3

theorem actualPrimitive3 :
    (searchTransportClosureBounded
      noSearch
      candidates
      2
      0
      3).stats.primitiveQueries ≤
      closureFuelTwoPrimitiveInputBudget 3 :=
  searchTransportClosureFuelTwo_primitiveQueries_le_input
    noSearch
    candidates
    3
    candidateLength3
    0
    3

theorem actualComposition3 :
    (searchTransportClosureBounded
      noSearch
      candidates
      2
      0
      3).stats.compositionCandidates ≤
      closureFuelTwoCompositionInputBudget 3 :=
  searchTransportClosureFuelTwo_compositionCandidates_le_input
    noSearch
    candidates
    3
    candidateLength3
    0
    3

end ConstitutiveSearch.Tests.ClosureSearchPolynomialRegimesRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchPolynomialRegimesRegression.primitiveBudget3
#print axioms ConstitutiveSearch.Tests.ClosureSearchPolynomialRegimesRegression.compositionBudget3
#print axioms ConstitutiveSearch.Tests.ClosureSearchPolynomialRegimesRegression.totalBudget3
#print axioms ConstitutiveSearch.Tests.ClosureSearchPolynomialRegimesRegression.actualPrimitive3
#print axioms ConstitutiveSearch.Tests.ClosureSearchPolynomialRegimesRegression.actualComposition3
/- AXIOM_AUDIT_END -/
