import ConstitutiveSearch.SAT.ExplicitFamilyBitComplexity

namespace ConstitutiveSearch.Tests.SATExplicitFamilyBitComplexityRegression

open ConstitutiveSearch
open SAT

theorem stateBudget3 :
    explicitFamilyStateBinaryBudget 3 = 104 := by
  rfl

theorem provenanceUnitBudget3 :
    explicitFamilyProvenanceUnitBinaryBudget 3 = 7 := by
  rfl

theorem certificateAtomBudget3 :
    explicitFamilyCertificateAtomBinaryBudget 3 = 3 := by
  rfl

theorem representationChargedCost3 :
    explicitFamilyRepresentationChargedCost 3 =
      2349 := by
  rfl

theorem relationAtomic3 :
    (explicitFamilyRepresentationAtomicCosts 3)
        .relationFindCall =
      208 :=
  explicitFamily_relationFind_atomicCost 3

theorem noClosureCharge3 :
    (explicitFamilyComplexityCounts 3)
          .closurePrimitiveQueries *
          (explicitFamilyRepresentationAtomicCosts 3)
            .closurePrimitiveQuery +
        (explicitFamilyComplexityCounts 3)
          .closureCompositionCandidates *
          (explicitFamilyRepresentationAtomicCosts 3)
            .closureCompositionCandidate =
      0 :=
  explicitFamily_localStrategy_noClosureCharge 3

end ConstitutiveSearch.Tests.SATExplicitFamilyBitComplexityRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyBitComplexityRegression.stateBudget3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyBitComplexityRegression.provenanceUnitBudget3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyBitComplexityRegression.certificateAtomBudget3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyBitComplexityRegression.representationChargedCost3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyBitComplexityRegression.relationAtomic3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyBitComplexityRegression.noClosureCharge3
/- AXIOM_AUDIT_END -/
