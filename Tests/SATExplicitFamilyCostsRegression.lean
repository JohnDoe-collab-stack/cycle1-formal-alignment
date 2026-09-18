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

theorem literalOccurrences3 :
    (Cnf.variableOccurrences
      (explicitStackedSymmetricFamily 3)).length =
        12 := by
  exact
    explicitStackedSymmetricFamily_variableOccurrences_length 3

theorem stepCount3 :
    (explicitFamilyResourceTrajectory 3).trajectory.stepCount =
      3 := by
  exact
    (explicitFamilyResourceTrajectory 3)
      .trajectory.stepCount_eq_index

theorem frontierSlots3 :
    (explicitFamilyResourceTrajectory 3).trajectory.frontierSlotCount =
      10 := by
  exact
    (explicitFamilyResourceTrajectory 3)
      .trajectory.frontierSlotCount_eq

end ConstitutiveSearch.Tests.SATExplicitFamilyCostsRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyCostsRegression.certified3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyCostsRegression.work3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyCostsRegression.literalOccurrences3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyCostsRegression.stepCount3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyCostsRegression.frontierSlots3
/- AXIOM_AUDIT_END -/
