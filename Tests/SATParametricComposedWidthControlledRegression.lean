import ConstitutiveSearch.SAT.ParametricComposedWidthControlled

namespace ConstitutiveSearch.Tests.SATParametricComposedWidthControlledRegression

open ConstitutiveSearch
open SAT

theorem candidateLength3 :
    (composedClosureWidthControlledSchedule.candidates 3).length = 1 := by
  rfl

theorem fuel3 :
    composedClosureWidthControlledSchedule.fuel 3 = 2 := by
  rfl

theorem run3 :
    searchTransportClosureBounded
        (composedPrimitiveSearch 3)
        (composedClosureWidthControlledSchedule.candidates 3)
        (composedClosureWidthControlledSchedule.fuel 3)
        (composedClosureWidthControlledSchedule.source 3)
        (composedClosureWidthControlledSchedule.target 3) =
      composedClosureFuelTwo 3 :=
  composedClosureWidthControlled_run_eq_fuelTwo 3

theorem countersPolynomial :
    WidthControlledClosureSchedule.InputPolynomialCounters
      (fun count =>
        composedPrimitiveSearch count)
      composedClosureWidthControlledSchedule :=
  composedClosureWidthControlledCounters

end ConstitutiveSearch.Tests.SATParametricComposedWidthControlledRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATParametricComposedWidthControlledRegression.candidateLength3
#print axioms ConstitutiveSearch.Tests.SATParametricComposedWidthControlledRegression.fuel3
#print axioms ConstitutiveSearch.Tests.SATParametricComposedWidthControlledRegression.run3
#print axioms ConstitutiveSearch.Tests.SATParametricComposedWidthControlledRegression.countersPolynomial
/- AXIOM_AUDIT_END -/
