import ConstitutiveSearch.ClosureSearchCosts

namespace ConstitutiveSearch.Tests.ClosureSearchCostsRegression

inductive DemoState where
  | a
  | b
  | c
  deriving DecidableEq

open DemoState

inductive PrimitiveRelation : DemoState → DemoState → Type where
  | aToB : PrimitiveRelation a b
  | bToC : PrimitiveRelation b c

def findPrimitive :
    (source target : DemoState) →
      Option (PrimitiveRelation source target)
  | .a, .a => none
  | .a, .b => some .aToB
  | .a, .c => none
  | .b, .a => none
  | .b, .b => none
  | .b, .c => some .bToC
  | .c, .a => none
  | .c, .b => none
  | .c, .c => none

def primitiveSearch : RelationSearch PrimitiveRelation :=
  { find := findPrimitive }

def fuelTwo :=
  searchTransportClosureBounded
    primitiveSearch
    [b]
    2
    a
    c

theorem primitiveBudget_fuelOne :
    closurePrimitiveQueryBudget 1 1 = 1 := by
  rfl

theorem primitiveBudget_fuelTwo :
    closurePrimitiveQueryBudget 1 2 = 3 := by
  rfl

theorem compositionBudget_fuelOne :
    closureCompositionCandidateBudget 1 1 = 1 := by
  rfl

theorem compositionBudget_fuelTwo :
    closureCompositionCandidateBudget 1 2 = 3 := by
  rfl

theorem fuelTwo_actual_primitive_queries :
    fuelTwo.stats.primitiveQueries = 3 := by
  rfl

theorem fuelTwo_actual_candidates :
    fuelTwo.stats.compositionCandidates = 1 := by
  rfl

theorem fuelTwo_primitive_within_budget :
    fuelTwo.stats.primitiveQueries ≤
      closurePrimitiveQueryBudget 1 2 := by
  exact
    searchTransportClosureBounded_primitiveQueries_le
      primitiveSearch
      [b]
      2
      a
      c

theorem fuelTwo_candidates_within_budget :
    fuelTwo.stats.compositionCandidates ≤
      closureCompositionCandidateBudget 1 2 := by
  exact
    searchTransportClosureBounded_compositionCandidates_le
      primitiveSearch
      [b]
      2
      a
      c

theorem fuelTwo_primitive_budget_tight :
    fuelTwo.stats.primitiveQueries =
      closurePrimitiveQueryBudget 1 2 := by
  rfl

end ConstitutiveSearch.Tests.ClosureSearchCostsRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchCostsRegression.PrimitiveRelation
#print axioms ConstitutiveSearch.Tests.ClosureSearchCostsRegression.primitiveSearch
#print axioms ConstitutiveSearch.Tests.ClosureSearchCostsRegression.primitiveBudget_fuelOne
#print axioms ConstitutiveSearch.Tests.ClosureSearchCostsRegression.primitiveBudget_fuelTwo
#print axioms ConstitutiveSearch.Tests.ClosureSearchCostsRegression.compositionBudget_fuelOne
#print axioms ConstitutiveSearch.Tests.ClosureSearchCostsRegression.compositionBudget_fuelTwo
#print axioms ConstitutiveSearch.Tests.ClosureSearchCostsRegression.fuelTwo_actual_primitive_queries
#print axioms ConstitutiveSearch.Tests.ClosureSearchCostsRegression.fuelTwo_actual_candidates
#print axioms ConstitutiveSearch.Tests.ClosureSearchCostsRegression.fuelTwo_primitive_within_budget
#print axioms ConstitutiveSearch.Tests.ClosureSearchCostsRegression.fuelTwo_candidates_within_budget
#print axioms ConstitutiveSearch.Tests.ClosureSearchCostsRegression.fuelTwo_primitive_budget_tight
/- AXIOM_AUDIT_END -/
