import ConstitutiveSearch.SAT.ParametricComposedClosure

namespace ConstitutiveSearch.Tests.SATParametricComposedClosureRegression

open ConstitutiveSearch
open SAT

theorem fuelOne3_not_found :
    (composedClosureFuelOne 3).code? = none :=
  composedClosureFuelOne_not_found 3

theorem fuelTwo3_found :
    (composedClosureFuelTwo 3).code? ≠ none :=
  composedClosureFuelTwo_found 3

theorem fuelTwo3_code_size :
    match (composedClosureFuelTwo 3).code? with
    | some code => code.size = 2
    | none => False :=
  composedClosureFuelTwo_code_size 3

theorem fuelTwo3_primitiveQueries :
    (composedClosureFuelTwo 3).stats.primitiveQueries = 3 :=
  composedClosureFuelTwo_primitiveQueries 3

theorem fuelTwo3_compositionCandidates :
    (composedClosureFuelTwo 3).stats.compositionCandidates = 1 :=
  composedClosureFuelTwo_compositionCandidates 3

theorem fuelTwo3_primitiveQueries_le_budget :
    (composedClosureFuelTwo 3).stats.primitiveQueries ≤
      closurePrimitiveQueryBudget 1 2 :=
  composedClosureFuelTwo_primitiveQueries_le_budget 3

theorem fuelTwo3_compositionCandidates_le_budget :
    (composedClosureFuelTwo 3).stats.compositionCandidates ≤
      closureCompositionCandidateBudget 1 2 :=
  composedClosureFuelTwo_compositionCandidates_le_budget 3

end ConstitutiveSearch.Tests.SATParametricComposedClosureRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATParametricComposedClosureRegression.fuelOne3_not_found
#print axioms ConstitutiveSearch.Tests.SATParametricComposedClosureRegression.fuelTwo3_found
#print axioms ConstitutiveSearch.Tests.SATParametricComposedClosureRegression.fuelTwo3_code_size
#print axioms ConstitutiveSearch.Tests.SATParametricComposedClosureRegression.fuelTwo3_primitiveQueries
#print axioms ConstitutiveSearch.Tests.SATParametricComposedClosureRegression.fuelTwo3_compositionCandidates
#print axioms ConstitutiveSearch.Tests.SATParametricComposedClosureRegression.fuelTwo3_primitiveQueries_le_budget
#print axioms ConstitutiveSearch.Tests.SATParametricComposedClosureRegression.fuelTwo3_compositionCandidates_le_budget
/- AXIOM_AUDIT_END -/
