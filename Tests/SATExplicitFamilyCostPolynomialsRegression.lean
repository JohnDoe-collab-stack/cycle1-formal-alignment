import ConstitutiveSearch.SAT.ExplicitFamilyCostPolynomials

namespace ConstitutiveSearch.Tests.SATExplicitFamilyCostPolynomialsRegression

open ConstitutiveSearch
open SAT

theorem localFormula3 :
    explicitFamilyFormulaCostPolynomial.eval 3 =
      explicitFamilyFormulaPolynomialBudget 3 :=
  explicitFamilyFormulaCostPolynomial_eval 3

theorem localRepresentation3 :
    explicitFamilyRepresentationCostPolynomial.eval 3 =
      explicitFamilyRepresentationPolynomialBudget 3 :=
  explicitFamilyRepresentationCostPolynomial_eval 3

theorem composedHistory3 :
    composedHistoryCostPolynomial.eval 3 =
      composedHistoryPolynomialBudget 3 :=
  composedHistoryCostPolynomial_eval 3

theorem composedRepresentation3 :
    composedClosurePhaseRepresentationCostPolynomial.eval 3 =
      composedClosurePhaseRepresentationPolynomialBudget 3 :=
  composedClosurePhaseRepresentationCostPolynomial_eval 3

end ConstitutiveSearch.Tests.SATExplicitFamilyCostPolynomialsRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyCostPolynomialsRegression.localFormula3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyCostPolynomialsRegression.localRepresentation3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyCostPolynomialsRegression.composedHistory3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyCostPolynomialsRegression.composedRepresentation3
/- AXIOM_AUDIT_END -/
