import ConstitutiveSearch.SAT.NPAndOrPProgramClosure

namespace ConstitutiveSearch.Tests.SATNPAndOrPProgramClosureRegression

open ConstitutiveSearch
open SAT

theorem closed :
    NPAndOrPProgramClosed :=
  npAndOrPProgramClosed

end ConstitutiveSearch.Tests.SATNPAndOrPProgramClosureRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATNPAndOrPProgramClosureRegression.closed
/- AXIOM_AUDIT_END -/
