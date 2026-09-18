import ConstitutiveSearch.SAT.ParametricComposedWidth

namespace ConstitutiveSearch.Tests.SATParametricComposedWidthRegression

open ConstitutiveSearch
open SAT

theorem direct3_irreducible :
    SearchIrreducible
      (composedPrimitiveSearch 3)
      (composedDirectFrontier 3) :=
  composedDirectFrontier_irreducible 3

theorem direct3_width :
    (composedDirectFrontier 3).length = 2 :=
  composedDirectFrontier_width 3

theorem code3_size :
    (composedSourceTargetCode 3).size = 2 :=
  composedSourceTargetCode_size 3

theorem closureSearch3_present :
    (composedBoundedClosureSearch 3).find
        (composedSource 3)
        (composedTarget 3) ≠
      none :=
  composedBoundedClosureSearch_source_target_present 3

theorem closure3_width :
    (composedClosureReduction 3).width = 1 :=
  composedClosureReduction_width 3

theorem closure3_strict :
    (composedClosureReduction 3).width <
      (composedDirectFrontier 3).length :=
  composedClosure_width_strictly_smaller 3

theorem closure3_viable_iff :
    FrontierViable
        (generatedStructuralBranchSystem
          (explicitStackedSymmetricFamily 3))
        [composedSource 3, composedTarget 3] ↔
      FrontierViable
        (generatedStructuralBranchSystem
          (explicitStackedSymmetricFamily 3))
        [composedTarget 3] :=
  composedClosureReduction_viable_iff 3

end ConstitutiveSearch.Tests.SATParametricComposedWidthRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATParametricComposedWidthRegression.direct3_irreducible
#print axioms ConstitutiveSearch.Tests.SATParametricComposedWidthRegression.direct3_width
#print axioms ConstitutiveSearch.Tests.SATParametricComposedWidthRegression.code3_size
#print axioms ConstitutiveSearch.Tests.SATParametricComposedWidthRegression.closureSearch3_present
#print axioms ConstitutiveSearch.Tests.SATParametricComposedWidthRegression.closure3_width
#print axioms ConstitutiveSearch.Tests.SATParametricComposedWidthRegression.closure3_strict
#print axioms ConstitutiveSearch.Tests.SATParametricComposedWidthRegression.closure3_viable_iff
/- AXIOM_AUDIT_END -/
