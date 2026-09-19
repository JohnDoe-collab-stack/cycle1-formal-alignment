import ConstitutiveSearch.SAT.ComposedPrimitiveHitPath

namespace ConstitutiveSearch.Tests.SATComposedPrimitiveHitPathRegression

open ConstitutiveSearch
open SAT

theorem required3 :
    PrimitiveHitPath.GlobalCompositionRequired
      (composedPrimitiveSearch 3)
      (composedSource 3)
      (composedTarget 3) :=
  composedGlobalCompositionRequired 3

theorem exactPath3 :
    ∃ path :
        PrimitiveHitPath
          (composedPrimitiveSearch 3)
          (composedSource 3)
          (composedTarget 3),
      path.length = 2 :=
  composedPrimitiveHitPath_length_two 3

theorem sequential3 :
    ∃ path :
        PrimitiveHitPath
          (composedPrimitiveSearch 3)
          (composedSource 3)
          (composedTarget 3),
      path.length = 2 ∧
        (path.sequentialStats
            [composedMiddle 3]
            2).primitiveQueries = 2 ∧
        (path.sequentialStats
            [composedMiddle 3]
            2).compositionCandidates = 0 :=
  composedPrimitiveHitPath_sequentialStats 3

theorem gap3 :
    ∃ path :
        PrimitiveHitPath
          (composedPrimitiveSearch 3)
          (composedSource 3)
          (composedTarget 3),
      path.length = 2 ∧
        (path.sequentialStats
            [composedMiddle 3]
            2).primitiveQueries <
          (composedClosureFuelTwo 3).stats.primitiveQueries ∧
        (path.sequentialStats
            [composedMiddle 3]
            2).compositionCandidates <
          (composedClosureFuelTwo 3).stats.compositionCandidates :=
  composedGlobalCompositionRequired_executionGap 3

end ConstitutiveSearch.Tests.SATComposedPrimitiveHitPathRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATComposedPrimitiveHitPathRegression.required3
#print axioms ConstitutiveSearch.Tests.SATComposedPrimitiveHitPathRegression.exactPath3
#print axioms ConstitutiveSearch.Tests.SATComposedPrimitiveHitPathRegression.sequential3
#print axioms ConstitutiveSearch.Tests.SATComposedPrimitiveHitPathRegression.gap3
/- AXIOM_AUDIT_END -/
