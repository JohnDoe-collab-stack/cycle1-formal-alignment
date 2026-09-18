import ConstitutiveSearch.SAT.ExplicitFamilyMachinePolynomial

namespace ConstitutiveSearch.Tests.SATExplicitFamilyMachinePolynomialRegression

open ConstitutiveSearch
open SAT

theorem localCountsPolynomial :
    ComplexityCountsFamilyInputPolynomiallyBounded
      explicitFamilyInputBitSize
      explicitFamilyComplexityCounts :=
  explicitFamilyComplexityCounts_inputPolynomiallyBounded

theorem compositionCountsPolynomial :
    ComplexityCountsFamilyInputPolynomiallyBounded
      explicitFamilyInputBitSize
      composedClosurePhaseCounts :=
  composedClosurePhaseCounts_inputPolynomiallyBounded

theorem localAtomicPolynomial :
    AtomicCostsFamilyInputPolynomiallyBounded
      explicitFamilyInputBitSize
      explicitFamilyRepresentationAtomicCosts :=
  explicitFamilyRepresentationAtomicCosts_inputPolynomiallyBounded

theorem compositionAtomicPolynomial :
    AtomicCostsFamilyInputPolynomiallyBounded
      explicitFamilyInputBitSize
      composedClosurePhaseRepresentationAtomicCosts :=
  composedClosurePhaseRepresentationAtomicCosts_inputPolynomiallyBounded

end ConstitutiveSearch.Tests.SATExplicitFamilyMachinePolynomialRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyMachinePolynomialRegression.localCountsPolynomial
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyMachinePolynomialRegression.compositionCountsPolynomial
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyMachinePolynomialRegression.localAtomicPolynomial
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyMachinePolynomialRegression.compositionAtomicPolynomial
/- AXIOM_AUDIT_END -/
