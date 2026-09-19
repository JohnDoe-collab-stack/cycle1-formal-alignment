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


theorem foundRunRequiresComposition3 :
    PrimitiveHitPath.GlobalCompositionRequired
      (composedPrimitiveSearch 3)
      (composedSource 3)
      (composedTarget 3) := by
  cases found :
      (composedClosureFuelTwo 3).code? with
  | none =>
      exact
        False.elim
          ((composedClosureFuelTwo_found 3)
            found)
  | some code =>
      exact
        PrimitiveHitPath.searchTransportClosureBounded_directMiss_found_requiresComposition
          (composedPrimitiveSearch 3)
          [composedMiddle 3]
          2
          (composedSource 3)
          (composedTarget 3)
          (composedPrimitiveSearch_source_target_none 3)
          found

theorem foundRunCodeSize3 :
    match (composedClosureFuelTwo 3).code? with
    | some code => 2 ≤ code.size
    | none => False := by
  cases found :
      (composedClosureFuelTwo 3).code? with
  | none =>
      exact
        False.elim
          ((composedClosureFuelTwo_found 3)
            found)
  | some code =>
      exact
        PrimitiveHitPath.searchTransportClosureBounded_directMiss_found_codeSize
          (composedPrimitiveSearch 3)
          [composedMiddle 3]
          2
          (composedSource 3)
          (composedTarget 3)
          (composedPrimitiveSearch_source_target_none 3)
          found


theorem foundRunUsesCompositionCandidate3 :
    0 <
      (composedClosureFuelTwo 3).stats.compositionCandidates := by
  cases found :
      (composedClosureFuelTwo 3).code? with
  | none =>
      exact
        False.elim
          ((composedClosureFuelTwo_found 3)
            found)
  | some code =>
      exact
        PrimitiveHitPath.searchTransportClosureBounded_directMiss_found_compositionCandidates_pos
          (composedPrimitiveSearch 3)
          [composedMiddle 3]
          2
          (composedSource 3)
          (composedTarget 3)
          (composedPrimitiveSearch_source_target_none 3)
          found


theorem foundRunSequentialReplacement3 :
    match (composedClosureFuelTwo 3).code? with
    | none => False
    | some code =>
        ∃ path :
            PrimitiveHitPath
              (composedPrimitiveSearch 3)
              (composedSource 3)
              (composedTarget 3),
          2 ≤ path.length ∧
            path.length = code.size ∧
            0 <
              (composedClosureFuelTwo 3).stats.compositionCandidates ∧
            (path.sequentialStats
                [composedMiddle 3]
                2).primitiveQueries =
              code.size ∧
            (path.sequentialStats
                [composedMiddle 3]
                2).compositionCandidates =
              0 := by
  cases found :
      (composedClosureFuelTwo 3).code? with
  | none =>
      exact
        False.elim
          ((composedClosureFuelTwo_found 3)
            found)
  | some code =>
      exact
        PrimitiveHitPath.searchTransportClosureBounded_directMiss_found_hasSequentialReplacement
          (composedPrimitiveSearch 3)
          [composedMiddle 3]
          2
          (composedSource 3)
          (composedTarget 3)
          (composedPrimitiveSearch_source_target_none 3)
          found
          [composedMiddle 3]
          2
          (by decide)

end ConstitutiveSearch.Tests.SATComposedPrimitiveHitPathRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATComposedPrimitiveHitPathRegression.required3
#print axioms ConstitutiveSearch.Tests.SATComposedPrimitiveHitPathRegression.exactPath3
#print axioms ConstitutiveSearch.Tests.SATComposedPrimitiveHitPathRegression.sequential3
#print axioms ConstitutiveSearch.Tests.SATComposedPrimitiveHitPathRegression.gap3
#print axioms ConstitutiveSearch.Tests.SATComposedPrimitiveHitPathRegression.foundRunRequiresComposition3
#print axioms ConstitutiveSearch.Tests.SATComposedPrimitiveHitPathRegression.foundRunCodeSize3
#print axioms ConstitutiveSearch.Tests.SATComposedPrimitiveHitPathRegression.foundRunUsesCompositionCandidate3
#print axioms ConstitutiveSearch.Tests.SATComposedPrimitiveHitPathRegression.foundRunSequentialReplacement3
/- AXIOM_AUDIT_END -/
