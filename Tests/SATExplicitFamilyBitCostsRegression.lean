import ConstitutiveSearch.SAT.ExplicitFamilyBitCosts

namespace ConstitutiveSearch.Tests.SATExplicitFamilyBitCostsRegression

open ConstitutiveSearch
open SAT

theorem formula3_vars_bounded :
    Cnf.VarsBoundedBy
      3
      (explicitStackedSymmetricFamily 3) :=
  explicitStackedSymmetricFamily_varsBoundedBy 3

theorem formula3_budget :
    explicitFamilyBinaryBudget 3 = 85 := by
  rfl

theorem formula3_size_le :
    Cnf.binarySize
        (explicitStackedSymmetricFamily 3) ≤
      explicitFamilyBinaryBudget 3 :=
  explicitFamily_binarySize_le_budget 3

theorem resource3_bounded :
    VarListBoundedBy
      3
      (stackedDecisionResource 3) :=
  stackedDecisionResource_bounded 3

theorem endpoint3_decisions_bounded :
    StructuralDecisionsVarsBoundedBy
      3
      (explicitFamilyResourceTrajectory 3)
        .finish.context.decisions :=
  explicitFamilyEndpoint_decisions_bounded 3

theorem endpoint3_history_budget :
    StructuralDecisionHistory.binaryBudget 3 3 = 19 := by
  rfl

theorem endpoint3_history_size_le :
    StructuralDecisionHistory.binarySize
        (explicitFamilyResourceTrajectory 3)
          .finish.context.decisions ≤
      StructuralDecisionHistory.binaryBudget 3 3 :=
  explicitFamilyEndpoint_historyBinarySize_le 3

end ConstitutiveSearch.Tests.SATExplicitFamilyBitCostsRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyBitCostsRegression.formula3_vars_bounded
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyBitCostsRegression.formula3_budget
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyBitCostsRegression.formula3_size_le
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyBitCostsRegression.resource3_bounded
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyBitCostsRegression.endpoint3_decisions_bounded
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyBitCostsRegression.endpoint3_history_budget
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyBitCostsRegression.endpoint3_history_size_le
/- AXIOM_AUDIT_END -/
