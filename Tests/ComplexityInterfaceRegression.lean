import ConstitutiveSearch.ComplexityInterface

namespace ConstitutiveSearch.Tests.ComplexityInterfaceRegression

def counts : ComplexityCounts :=
  { syntaxUnits := 2
    frontierSlots := 3
    provenanceUnits := 1
    certificateAtoms := 1
    relationFindCalls := 2
    closurePrimitiveQueries := 0
    closureCompositionCandidates := 0
    terminalChecks := 1 }

def costs : AtomicCosts :=
  { syntaxUnit := 1
    frontierSlot := 2
    provenanceUnit := 1
    certificateAtom := 1
    relationFindCall := 3
    closurePrimitiveQuery := 4
    closureCompositionCandidate := 4
    terminalCheck := 1 }

theorem charged_exact :
    chargedCost counts costs = 17 := by
  rfl

def bounded :
    UniformAtomicBound costs 4 :=
  { syntaxLe := by decide
    frontierLe := by decide
    provenanceLe := by decide
    certificateLe := by decide
    relationLe := by decide
    closurePrimitiveLe := by decide
    closureCandidateLe := by decide
    terminalLe := by decide }

theorem charged_le_uniform :
    chargedCost counts costs ≤
      uniformChargedBudget counts 4 :=
  chargedCost_le_of_uniformBound
    counts
    costs
    4
    bounded

end ConstitutiveSearch.Tests.ComplexityInterfaceRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ComplexityInterfaceRegression.counts
#print axioms ConstitutiveSearch.Tests.ComplexityInterfaceRegression.costs
#print axioms ConstitutiveSearch.Tests.ComplexityInterfaceRegression.charged_exact
#print axioms ConstitutiveSearch.Tests.ComplexityInterfaceRegression.bounded
#print axioms ConstitutiveSearch.Tests.ComplexityInterfaceRegression.charged_le_uniform
/- AXIOM_AUDIT_END -/
