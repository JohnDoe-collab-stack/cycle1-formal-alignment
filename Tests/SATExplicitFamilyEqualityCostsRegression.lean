import ConstitutiveSearch.SAT.ExplicitFamilyEqualityCosts

namespace ConstitutiveSearch.Tests.SATExplicitFamilyEqualityCostsRegression

open ConstitutiveSearch
open SAT

abbrev formula3 : Cnf :=
  explicitStackedSymmetricFamily 3

abbrev root3 :
    GeneratedStructuralBranchContext formula3 :=
  explicitStackedRoot 3

theorem root3Var2Fresh :
    StructuralDecisionsAvoid
      2
      root3.context.decisions :=
  True.intro

abbrev left3 :
    GeneratedStructuralBranchContext formula3 :=
  GeneratedStructuralBranchContext.child
    root3 2 false root3Var2Fresh

abbrev right3 :
    GeneratedStructuralBranchContext formula3 :=
  GeneratedStructuralBranchContext.child
    root3 2 true root3Var2Fresh

theorem formulaBudget3 :
    explicitFamilyBinaryBudget 3 = 85 := by
  rfl

theorem historyBudget3 :
    StructuralDecisionHistory.binaryBudget 3 3 = 19 := by
  rfl

theorem equalityBudget3 :
    explicitFamilyRelationEqualityChargeBudget 3 =
      208 := by
  rfl

theorem leftFormulaLe :
    Cnf.binarySize left3.context.formula ≤
      explicitFamilyBinaryBudget 3 := by
  exact
    Nat.le_trans
      (Cnf.branchResidual_binarySize_le
        root3.context.formula
        2
        false)
      (explicitFamily_binarySize_le_budget 3)

theorem rightFormulaLe :
    Cnf.binarySize right3.context.formula ≤
      explicitFamilyBinaryBudget 3 := by
  exact
    Nat.le_trans
      (Cnf.branchResidual_binarySize_le
        root3.context.formula
        2
        true)
      (explicitFamily_binarySize_le_budget 3)

theorem leftHistoryLe :
    StructuralDecisionHistory.binarySize
        left3.context.decisions ≤
      StructuralDecisionHistory.binaryBudget 3 3 := by
  change 5 ≤ 19
  decide

theorem rightHistoryLe :
    StructuralDecisionHistory.binarySize
        right3.context.decisions ≤
      StructuralDecisionHistory.binaryBudget 3 3 := by
  change 5 ≤ 19
  decide

theorem rootSiblingEqualityChargeLe :
    generatedFlipEqualityCharge
        2
        left3
        right3 ≤
      explicitFamilyRelationEqualityChargeBudget 3 :=
  generatedFlipEqualityCharge_le
    2
    left3
    right3
    (explicitFamilyBinaryBudget 3)
    (StructuralDecisionHistory.binaryBudget 3 3)
    leftFormulaLe
    rightFormulaLe
    leftHistoryLe
    rightHistoryLe

end ConstitutiveSearch.Tests.SATExplicitFamilyEqualityCostsRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyEqualityCostsRegression.formulaBudget3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyEqualityCostsRegression.historyBudget3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyEqualityCostsRegression.equalityBudget3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyEqualityCostsRegression.leftFormulaLe
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyEqualityCostsRegression.rightFormulaLe
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyEqualityCostsRegression.leftHistoryLe
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyEqualityCostsRegression.rightHistoryLe
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyEqualityCostsRegression.rootSiblingEqualityChargeLe
/- AXIOM_AUDIT_END -/
