import ConstitutiveSearch.SAT.ExplicitFamilyCosts

namespace ConstitutiveSearch.Tests.SATExplicitFamilyCostsRegression

open ConstitutiveSearch
open SAT

theorem certified3 :
    ExplicitFamilyCertifiedCounts 3 :=
  explicitFamilyCertifiedCounts 3

theorem work3 :
    explicitFamilyStructuralWorkUnits 3 = 13 := by
  exact explicitFamilyStructuralWorkUnits_eq 3

theorem literalCount3 :
    Cnf.literalCount
      (explicitStackedSymmetricFamily 3) =
        12 := by
  change
    Cnf.literalCount
      (stackedSymmetricBlocks 3 3) = 12
  exact stackedSymmetricBlocks_literalCount 3 3

theorem stepCount3 :
    (explicitFamilyResourceTrajectory 3).trajectory.stepCount =
      3 := by
  exact
    FlipSymmetricTrajectory.stepCount_eq_index
      (explicitFamilyResourceTrajectory 3).trajectory

theorem frontierSlots3 :
    (explicitFamilyResourceTrajectory 3).trajectory.frontierSlotCount =
      10 := by
  exact
    FlipSymmetricTrajectory.frontierSlotCount_eq
      (explicitFamilyResourceTrajectory 3).trajectory

end ConstitutiveSearch.Tests.SATExplicitFamilyCostsRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyCostsRegression.certified3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyCostsRegression.work3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyCostsRegression.literalCount3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyCostsRegression.stepCount3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyCostsRegression.frontierSlots3
/- AXIOM_AUDIT_END -/
