import ConstitutiveSearch.SAT.ExplicitFamilyComplexity

namespace ConstitutiveSearch.Tests.SATExplicitFamilyComplexityRegression

open ConstitutiveSearch
open SAT

def unitCosts : AtomicCosts :=
  { syntaxUnit := 1
    frontierSlot := 1
    provenanceUnit := 1
    certificateAtom := 1
    relationFindCall := 1
    closurePrimitiveQuery := 1
    closureCompositionCandidate := 1
    terminalCheck := 1 }

theorem evidence3 :
    ExplicitFamilyComplexityEvidence 3 :=
  explicitFamilyComplexityEvidence 3

theorem charged3 :
    explicitFamilyChargedCost 3 unitCosts = 35 := by
  rfl

def unitCostsBoundedByFour :
    UniformAtomicBound unitCosts 4 :=
  { syntaxLe := by decide
    frontierLe := by decide
    provenanceLe := by decide
    certificateLe := by decide
    relationLe := by decide
    closurePrimitiveLe := by decide
    closureCandidateLe := by decide
    terminalLe := by decide }

theorem uniformBudget3 :
    explicitFamilyUniformChargedBudget 3 4 = 140 := by
  rfl

theorem charged3_le_uniform :
    explicitFamilyChargedCost 3 unitCosts ≤
      explicitFamilyUniformChargedBudget 3 4 :=
  explicitFamilyChargedCost_le_uniform
    3
    unitCosts
    4
    unitCostsBoundedByFour

end ConstitutiveSearch.Tests.SATExplicitFamilyComplexityRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyComplexityRegression.unitCosts
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyComplexityRegression.evidence3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyComplexityRegression.charged3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyComplexityRegression.unitCostsBoundedByFour
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyComplexityRegression.uniformBudget3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyComplexityRegression.charged3_le_uniform
/- AXIOM_AUDIT_END -/
