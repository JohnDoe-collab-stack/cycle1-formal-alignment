import ConstitutiveSearch.SAT.ExplicitFamilyRelationCosts

namespace ConstitutiveSearch.Tests.SATExplicitFamilyRelationCostsRegression

open ConstitutiveSearch
open SAT

def aligned3 :=
  explicitFamilyResourceTrajectory 3

theorem relationSurface3 :
    aligned3.trajectory.relationVerificationSurface ≤
      explicitFamilyRelationVerificationBudget 3 :=
  explicitFamilyRelationVerificationSurface_le 3

end ConstitutiveSearch.Tests.SATExplicitFamilyRelationCostsRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyRelationCostsRegression.aligned3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyRelationCostsRegression.relationSurface3
/- AXIOM_AUDIT_END -/
