import ConstitutiveSearch.SAT.ComposedSearchableCode

namespace ConstitutiveSearch.Tests.SATComposedSearchableCodeRegression

open ConstitutiveSearch
open SAT

theorem codeSize3 :
    (composedConstitutedCode 3).size = 2 :=
  composedConstitutedCode_size 3

theorem searchable3 :
    (composedConstitutedCode 3).SearchableBy
      (composedPrimitiveSearch 3) :=
  composedConstitutedCode_searchable 3

theorem required3 :
    PrimitiveHitPath.GlobalCompositionRequired
      (composedPrimitiveSearch 3)
      (composedSource 3)
      (composedTarget 3) :=
  composedGlobalCompositionRequired_fromConstitutedCode 3

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
  composedConstitutedCode_executionGap 3

end ConstitutiveSearch.Tests.SATComposedSearchableCodeRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATComposedSearchableCodeRegression.codeSize3
#print axioms ConstitutiveSearch.Tests.SATComposedSearchableCodeRegression.searchable3
#print axioms ConstitutiveSearch.Tests.SATComposedSearchableCodeRegression.required3
#print axioms ConstitutiveSearch.Tests.SATComposedSearchableCodeRegression.gap3
/- AXIOM_AUDIT_END -/
