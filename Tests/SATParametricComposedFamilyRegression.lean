import ConstitutiveSearch.SAT.ParametricComposedFamily

namespace ConstitutiveSearch.Tests.SATParametricComposedFamilyRegression

open ConstitutiveSearch
open SAT

theorem direct3_none :
    (composedPrimitiveSearch 3).find
        (composedSource 3)
        (composedTarget 3) =
      none :=
  composedPrimitiveSearch_source_target_none 3

theorem firstEdge3_present :
    (composedPrimitiveSearch 3).find
        (composedSource 3)
        (composedMiddle 3) ≠
      none :=
  composedPrimitiveSearch_source_middle_present 3

theorem secondEdge3_present :
    (composedPrimitiveSearch 3).find
        (composedMiddle 3)
        (composedTarget 3) ≠
      none :=
  composedPrimitiveSearch_middle_target_present 3

end ConstitutiveSearch.Tests.SATParametricComposedFamilyRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATParametricComposedFamilyRegression.direct3_none
#print axioms ConstitutiveSearch.Tests.SATParametricComposedFamilyRegression.firstEdge3_present
#print axioms ConstitutiveSearch.Tests.SATParametricComposedFamilyRegression.secondEdge3_present
/- AXIOM_AUDIT_END -/
