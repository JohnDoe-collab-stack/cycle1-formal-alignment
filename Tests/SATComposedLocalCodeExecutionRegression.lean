import ConstitutiveSearch.SAT.ComposedLocalCodeExecution

namespace ConstitutiveSearch.Tests.SATComposedLocalCodeExecutionRegression

open ConstitutiveSearch
open SAT

theorem localExecution3 :
    TransportCode.LocalSequentialExecution
      (composedPrimitiveSearch 3)
      (composedConstitutedCode 3) :=
  composedConstitutedCode_localSequentialExecution 3

theorem globalNeedAndLocal3 :
    TransportCode.GlobalNeedWithLocalExecution
      (composedPrimitiveSearch 3)
      (composedConstitutedCode 3) :=
  composedConstitutedCode_globalNeed_and_localExecution 3

theorem localStats3 :
    ∃ path :
        PrimitiveHitPath
          (composedPrimitiveSearch 3)
          (composedSource 3)
          (composedTarget 3),
      path.length = 2 ∧
        (path.sequentialStats [] 1).primitiveQueries = 2 ∧
        (path.sequentialStats [] 1).compositionCandidates = 0 :=
  composedConstitutedCode_localStats 3

theorem localGlobalGap3 :
    ∃ path :
        PrimitiveHitPath
          (composedPrimitiveSearch 3)
          (composedSource 3)
          (composedTarget 3),
      path.length = 2 ∧
        (path.sequentialStats [] 1).primitiveQueries <
          (composedClosureFuelTwo 3).stats.primitiveQueries ∧
        (path.sequentialStats [] 1).compositionCandidates <
          (composedClosureFuelTwo 3).stats.compositionCandidates :=
  composedConstitutedCode_localGlobalGap 3

end ConstitutiveSearch.Tests.SATComposedLocalCodeExecutionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATComposedLocalCodeExecutionRegression.localExecution3
#print axioms ConstitutiveSearch.Tests.SATComposedLocalCodeExecutionRegression.globalNeedAndLocal3
#print axioms ConstitutiveSearch.Tests.SATComposedLocalCodeExecutionRegression.localStats3
#print axioms ConstitutiveSearch.Tests.SATComposedLocalCodeExecutionRegression.localGlobalGap3
/- AXIOM_AUDIT_END -/
