import ConstitutiveSearch.SAT.WidthSeparators

namespace ConstitutiveSearch.Tests.SATWidthSeparatorsRegression

open ConstitutiveSearch
open SAT

def frontier3 :=
  isolatedFrontier 3

theorem frontier3_width :
    frontier3.length = 3 :=
  isolatedFrontier_length 3

theorem frontier3_irreducible :
    SearchIrreducible
      (generatedStructuralFlipAtSearch ([] : Cnf) 99)
      frontier3 :=
  isolatedFrontier_searchIrreducible 99 3

theorem frontier3_viable :
    FrontierViable
      (generatedStructuralBranchSystem ([] : Cnf))
      frontier3 := by
  exact isolatedFrontier_viable 2

end ConstitutiveSearch.Tests.SATWidthSeparatorsRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATWidthSeparatorsRegression.frontier3
#print axioms ConstitutiveSearch.Tests.SATWidthSeparatorsRegression.frontier3_width
#print axioms ConstitutiveSearch.Tests.SATWidthSeparatorsRegression.frontier3_irreducible
#print axioms ConstitutiveSearch.Tests.SATWidthSeparatorsRegression.frontier3_viable
/- AXIOM_AUDIT_END -/
