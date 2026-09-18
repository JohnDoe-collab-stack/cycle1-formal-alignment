import ConstitutiveSearch.SAT.ExplicitFamilyMachineComplexity

namespace ConstitutiveSearch.Tests.SATExplicitFamilyMachineComplexityRegression

open ConstitutiveSearch
open SAT

def localMachine3 : MachineCostModel :=
  { atomic :=
      affineAtomicEnvelope
        (explicitFamilyRepresentationAtomicCosts 3)
        1
        0 }

def compositionMachine3 : MachineCostModel :=
  { atomic :=
      affineAtomicEnvelope
        (composedClosurePhaseRepresentationAtomicCosts 3)
        1
        0 }

theorem localBridge3 :
    RepresentationMachineBridge
      (explicitFamilyRepresentationAtomicCosts 3)
      localMachine3
      1
      0 := by
  constructor
  exact
    atomicCostPointwiseLe_refl
      (affineAtomicEnvelope
        (explicitFamilyRepresentationAtomicCosts 3)
        1
        0)

theorem compositionBridge3 :
    RepresentationMachineBridge
      (composedClosurePhaseRepresentationAtomicCosts 3)
      compositionMachine3
      1
      0 := by
  constructor
  exact
    atomicCostPointwiseLe_refl
      (affineAtomicEnvelope
        (composedClosurePhaseRepresentationAtomicCosts 3)
        1
        0)

theorem totalMachineBound3 :
    explicitFamilyWithCompositionMachineChargedCost
        3
        localMachine3
        compositionMachine3 ≤
      explicitFamilyWithCompositionCalibratedMachineBudget
        3
        1
        0
        1
        0 :=
  explicitFamilyWithCompositionMachineCost_le_calibrated
    3
    localMachine3
    compositionMachine3
    1
    0
    1
    0
    localBridge3
    compositionBridge3

end ConstitutiveSearch.Tests.SATExplicitFamilyMachineComplexityRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyMachineComplexityRegression.localBridge3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyMachineComplexityRegression.compositionBridge3
#print axioms ConstitutiveSearch.Tests.SATExplicitFamilyMachineComplexityRegression.totalMachineBound3
/- AXIOM_AUDIT_END -/
