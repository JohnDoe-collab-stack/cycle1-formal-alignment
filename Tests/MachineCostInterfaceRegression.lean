import ConstitutiveSearch.MachineCostInterface

namespace ConstitutiveSearch.Tests.MachineCostInterfaceRegression

def counts : ComplexityCounts :=
  { syntaxUnits := 4
    frontierSlots := 3
    provenanceUnits := 2
    certificateAtoms := 1
    relationFindCalls := 2
    closurePrimitiveQueries := 3
    closureCompositionCandidates := 1
    terminalChecks := 1 }

def representation : AtomicCosts :=
  { syntaxUnit := 2
    frontierSlot := 4
    provenanceUnit := 3
    certificateAtom := 2
    relationFindCall := 5
    closurePrimitiveQuery := 6
    closureCompositionCandidate := 4
    terminalCheck := 2 }

def machine : MachineCostModel :=
  { atomic := representation }

theorem identityBridge :
    RepresentationMachineBridge
      representation
      machine
      1
      0 := by
  constructor
  unfold machine
  unfold affineAtomicEnvelope
  constructor
  · rw [Nat.one_mul, Nat.add_zero]
  · rw [Nat.one_mul, Nat.add_zero]
  · rw [Nat.one_mul, Nat.add_zero]
  · rw [Nat.one_mul, Nat.add_zero]
  · rw [Nat.one_mul, Nat.add_zero]
  · rw [Nat.one_mul, Nat.add_zero]
  · rw [Nat.one_mul, Nat.add_zero]
  · rw [Nat.one_mul, Nat.add_zero]

theorem aggregateMachineBound :
    machineChargedCost counts machine ≤
      representationCalibratedMachineBudget
        counts
        representation
        1
        0 :=
  machineChargedCost_le_calibrated
    counts
    representation
    machine
    1
    0
    identityBridge

end ConstitutiveSearch.Tests.MachineCostInterfaceRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.MachineCostInterfaceRegression.identityBridge
#print axioms ConstitutiveSearch.Tests.MachineCostInterfaceRegression.aggregateMachineBound
/- AXIOM_AUDIT_END -/
