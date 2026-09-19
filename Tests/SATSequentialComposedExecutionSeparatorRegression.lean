import ConstitutiveSearch.SAT.SequentialComposedExecutionSeparator

namespace ConstitutiveSearch.Tests.SATSequentialComposedExecutionSeparatorRegression

open ConstitutiveSearch
open SAT

theorem sequentialStats3 :
    (composedSequentialClosureStats 3).primitiveQueries = 2 ∧
      (composedSequentialClosureStats 3).compositionCandidates = 0 := by
  exact
    ⟨composedSequentialClosureStats_primitiveQueries 3,
      composedSequentialClosureStats_compositionCandidates 3⟩

theorem globalStats3 :
    (composedClosureFuelTwo 3).stats.primitiveQueries = 3 ∧
      (composedClosureFuelTwo 3).stats.compositionCandidates = 1 := by
  exact
    ⟨composedClosureFuelTwo_primitiveQueries 3,
      composedClosureFuelTwo_compositionCandidates 3⟩

theorem separator3 :
    SequentialComposedExecutionSeparator 3 :=
  composedSequentialGlobalExecutionSeparator 3

end ConstitutiveSearch.Tests.SATSequentialComposedExecutionSeparatorRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATSequentialComposedExecutionSeparatorRegression.sequentialStats3
#print axioms ConstitutiveSearch.Tests.SATSequentialComposedExecutionSeparatorRegression.globalStats3
#print axioms ConstitutiveSearch.Tests.SATSequentialComposedExecutionSeparatorRegression.separator3
/- AXIOM_AUDIT_END -/
