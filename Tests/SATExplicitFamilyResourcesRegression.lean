import ConstitutiveSearch.SAT.ExplicitFamilyResources

namespace ConstitutiveSearch.Tests.SATExplicitFamilyResourcesRegression

open ConstitutiveSearch
open SAT

theorem resource3_exact :
    explicitFamilyDecisionResource 3 =
      [2, 1, 0] := by
  rfl

theorem resource3_length :
    (explicitFamilyDecisionResource 3).length = 3 :=
  explicitFamilyDecisionResource_length 3

def aligned3 :=
  explicitFamilyResourceTrajectory 3

theorem aligned3_depth :
    aligned3.finish.depth = 3 :=
  explicitFamilyEndpoint_depth 3

theorem aligned3_terminal :
    ResourceTerminal aligned3.finish [] :=
  explicitFamilyEndpoint_terminal 3

theorem aligned3_no_next :
    ResourceDecision aligned3.finish [] → False :=
  explicitFamilyEndpoint_no_next_decision 3

theorem aligned3_width_bound :
    ∀ width : Nat,
      width ∈ aligned3.trajectory.widthTrace →
        width ≤ 2 := by
  intro width member
  exact
    explicitFamilyResourceTrajectory_width_le_two
      3
      width
      member

theorem aligned3_trace_length :
    aligned3.trajectory.widthTrace.length = 7 := by
  exact aligned3.trajectory.widthTrace_length

end ConstitutiveSearch.Tests.SATExplicitFamilyResourcesRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyResourcesRegression.resource3_exact
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyResourcesRegression.resource3_length
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyResourcesRegression.aligned3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyResourcesRegression.aligned3_depth
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyResourcesRegression.aligned3_terminal
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyResourcesRegression.aligned3_no_next
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyResourcesRegression.aligned3_width_bound
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyResourcesRegression.aligned3_trace_length
/- AXIOM_AUDIT_END -/
