import ConstitutiveSearch.SAT.NPAndOrPClassicalBridge

namespace ConstitutiveSearch.Tests.SATNPAndOrPClassicalBridgeRegression

open ConstitutiveSearch
open SAT

theorem decisionProjection3 :
    explicitFamilyDecisionProblem.Accept
        3 ↔
      FrontierViable
        (generatedStructuralBranchSystem
          (explicitStackedSymmetricFamily 3))
        [(explicitFamilyResourceTrajectory
          3).finish] :=
  explicitFamilyDecisionProjection_preserved 3

theorem bridgeClosed :
    NPAndOrPClassicalBridgeClosed :=
  npAndOrPClassicalBridgeClosed

theorem objectiveComplete :
    NPAndPObjectiveComplete :=
  npAndPObjectiveComplete

end ConstitutiveSearch.Tests.SATNPAndOrPClassicalBridgeRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATNPAndOrPClassicalBridgeRegression.decisionProjection3
#print axioms ConstitutiveSearch.Tests.SATNPAndOrPClassicalBridgeRegression.bridgeClosed
#print axioms ConstitutiveSearch.Tests.SATNPAndOrPClassicalBridgeRegression.objectiveComplete
/- AXIOM_AUDIT_END -/
