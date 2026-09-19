import ConstitutiveSearch.SAT.TrajectoryScheduleComposition
import ConstitutiveSearch.SAT.ExplicitFamilyResources

namespace ConstitutiveSearch.Tests.SATTrajectoryScheduleCompositionRegression

open ConstitutiveSearch
open SAT

theorem explicitTwoStepScheduleNotEndpointComposable :
    ¬
      ConstitutedLocalSchedule.EndpointComposable
        (explicitFamilyResourceTrajectory
          2).trajectory.constitutedLocalWitnesses :=
  (explicitFamilyResourceTrajectory
    2).trajectory.constitutedLocalWitnesses_not_endpointComposable_of_two_le
      (by decide)

end ConstitutiveSearch.Tests.SATTrajectoryScheduleCompositionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATTrajectoryScheduleCompositionRegression.explicitTwoStepScheduleNotEndpointComposable
/- AXIOM_AUDIT_END -/
