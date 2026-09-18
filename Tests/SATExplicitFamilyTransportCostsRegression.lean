import ConstitutiveSearch.SAT.ExplicitFamilyTransportCosts

namespace ConstitutiveSearch.Tests.SATExplicitFamilyTransportCostsRegression

open ConstitutiveSearch
open SAT

def aligned3 :=
  explicitFamilyResourceTrajectory 3

theorem transportAtoms3 :
    aligned3.trajectory.transportCertificateAtomCount = 3 :=
  explicitFamilyTransportCertificateAtomCount 3

theorem certificateBundle3 :
    ExplicitFamilyCertificateSizes 3 :=
  explicitFamilyCertificateSizes 3

end ConstitutiveSearch.Tests.SATExplicitFamilyTransportCostsRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyTransportCostsRegression.aligned3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyTransportCostsRegression.transportAtoms3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyTransportCostsRegression.certificateBundle3
/- AXIOM_AUDIT_END -/
