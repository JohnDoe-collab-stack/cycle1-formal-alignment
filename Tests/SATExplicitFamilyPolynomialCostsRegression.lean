import ConstitutiveSearch.SAT.ExplicitFamilyPolynomialCosts

namespace ConstitutiveSearch.Tests.SATExplicitFamilyPolynomialCostsRegression

open ConstitutiveSearch
open SAT

theorem formulaPolynomial3 :
    explicitFamilyFormulaPolynomialBudget 3 =
      85 := by
  rfl

theorem historyPolynomial3 :
    explicitFamilyHistoryPolynomialBudget 3 =
      19 := by
  rfl

theorem statePolynomial3 :
    explicitFamilyStatePolynomialBudget 3 =
      104 := by
  rfl

theorem relationPolynomial3 :
    explicitFamilyRelationPolynomialBudget 3 =
      208 := by
  rfl

theorem representationPolynomial3 :
    explicitFamilyRepresentationPolynomialBudget 3 =
      2355 := by
  rfl

theorem chargedCost3_le_polynomial :
    explicitFamilyRepresentationChargedCost 3 ≤
      explicitFamilyRepresentationPolynomialBudget 3 :=
  explicitFamilyRepresentationChargedCost_le_polynomial 3

end ConstitutiveSearch.Tests.SATExplicitFamilyPolynomialCostsRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyPolynomialCostsRegression.formulaPolynomial3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyPolynomialCostsRegression.historyPolynomial3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyPolynomialCostsRegression.statePolynomial3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyPolynomialCostsRegression.relationPolynomial3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyPolynomialCostsRegression.representationPolynomial3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyPolynomialCostsRegression.chargedCost3_le_polynomial
/- AXIOM_AUDIT_END -/
