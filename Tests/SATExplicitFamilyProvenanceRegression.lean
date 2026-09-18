import ConstitutiveSearch.SAT.ExplicitFamilyProvenance

namespace ConstitutiveSearch.Tests.SATExplicitFamilyProvenanceRegression

open ConstitutiveSearch
open SAT

def aligned3 :=
  explicitFamilyResourceTrajectory 3

theorem endpoint_provenance3 :
    aligned3.finish.provenanceSize = 3 :=
  explicitFamilyEndpoint_provenanceSize 3

theorem endpoint_decisions3 :
    aligned3.finish.context.decisions.length = 3 :=
  explicitFamilyEndpoint_decisions_length 3

theorem root_provenance3 :
    (explicitStackedRoot 3).provenanceSize = 0 :=
  GeneratedStructuralBranchContext.root_provenanceSize
    (explicitStackedSymmetricFamily 3)

end ConstitutiveSearch.Tests.SATExplicitFamilyProvenanceRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyProvenanceRegression.aligned3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyProvenanceRegression.endpoint_provenance3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyProvenanceRegression.endpoint_decisions3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyProvenanceRegression.root_provenance3
/- AXIOM_AUDIT_END -/
