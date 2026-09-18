import ConstitutiveSearch.ClosureSearchBounds

namespace ConstitutiveSearch.Tests.ClosureSearchBoundsRegression

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

theorem oneCandidateFuelOneBound :
    closureSearchWorkBound [b] 1 = 2 := by
  rfl

theorem oneCandidateFuelTwoBound :
    closureSearchWorkBound [b] 2 = 6 := by
  rfl

theorem fuelTwo_actual_work :
    fuelTwo.stats.workUnits = 4 := by
  rfl

theorem fuelTwo_work_le_budget :
    fuelTwo.stats.workUnits ≤
      closureSearchWorkBound [b] 2 :=
  searchTransportClosureBounded_workUnits_le
    primitiveSearch
    [b]
    2
    a
    c

theorem fuelTwo_primitive_queries_le_budget :
    fuelTwo.stats.primitiveQueries ≤
      closureSearchWorkBound [b] 2 :=
  searchTransportClosureBounded_primitiveQueries_le
    primitiveSearch
    [b]
    2
    a
    c

theorem fuelTwo_composition_candidates_le_budget :
    fuelTwo.stats.compositionCandidates ≤
      closureSearchWorkBound [b] 2 :=
  searchTransportClosureBounded_compositionCandidates_le
    primitiveSearch
    [b]
    2
    a
    c

end ConstitutiveSearch.Tests.ClosureSearchBoundsRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchBoundsRegression.primitiveSearch
#print axioms ConstitutiveSearch.Tests.ClosureSearchBoundsRegression.oneCandidateFuelOneBound
#print axioms ConstitutiveSearch.Tests.ClosureSearchBoundsRegression.oneCandidateFuelTwoBound
#print axioms ConstitutiveSearch.Tests.ClosureSearchBoundsRegression.fuelTwo_actual_work
#print axioms ConstitutiveSearch.Tests.ClosureSearchBoundsRegression.fuelTwo_work_le_budget
#print axioms ConstitutiveSearch.Tests.ClosureSearchBoundsRegression.fuelTwo_primitive_queries_le_budget
#print axioms ConstitutiveSearch.Tests.ClosureSearchBoundsRegression.fuelTwo_composition_candidates_le_budget
/- AXIOM_AUDIT_END -/
