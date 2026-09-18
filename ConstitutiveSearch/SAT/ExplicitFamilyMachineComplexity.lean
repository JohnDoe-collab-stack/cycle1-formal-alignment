import ConstitutiveSearch.SAT.ExplicitFamilyConstitutiveProfile
import ConstitutiveSearch.SAT.ParametricComposedBitComplexity

/-!
# Conditional machine-cost layer for the combined SAT profile

The local F(n) phase and the added composition phase use distinct
representation-level AtomicCosts assignments.  This module therefore requires
two explicit representation-to-machine bridges.

No concrete runtime model is assumed.  The theorem states exactly what follows
if both phase-level bridge obligations are discharged.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Machine charge for the local certified F(n) phase. -/
def explicitFamilyLocalMachineChargedCost
    (count : Nat)
    (machine : MachineCostModel) : Nat :=
  machineChargedCost
    (explicitFamilyComplexityCounts count)
    machine

/-- Machine charge for the added composition phase. -/
def composedClosurePhaseMachineChargedCost
    (count : Nat)
    (machine : MachineCostModel) : Nat :=
  machineChargedCost
    (composedClosurePhaseCounts count)
    machine

/-- Combined machine charge when each phase has its own machine model. -/
def explicitFamilyWithCompositionMachineChargedCost
    (count : Nat)
    (localMachine compositionMachine : MachineCostModel) :
    Nat :=
  explicitFamilyLocalMachineChargedCost
      count
      localMachine +
    composedClosurePhaseMachineChargedCost
      count
      compositionMachine

/-- Calibrated machine envelope for the local phase. -/
def explicitFamilyLocalCalibratedMachineBudget
    (count factor overhead : Nat) : Nat :=
  representationCalibratedMachineBudget
    (explicitFamilyComplexityCounts count)
    (explicitFamilyRepresentationAtomicCosts count)
    factor
    overhead

/-- Calibrated machine envelope for the composition phase. -/
def composedClosurePhaseCalibratedMachineBudget
    (count factor overhead : Nat) : Nat :=
  representationCalibratedMachineBudget
    (composedClosurePhaseCounts count)
    (composedClosurePhaseRepresentationAtomicCosts count)
    factor
    overhead

/-- Combined calibrated machine envelope for both phases. -/
def explicitFamilyWithCompositionCalibratedMachineBudget
    (count : Nat)
    (localFactor localOverhead : Nat)
    (compositionFactor compositionOverhead : Nat) :
    Nat :=
  explicitFamilyLocalCalibratedMachineBudget
      count
      localFactor
      localOverhead +
    composedClosurePhaseCalibratedMachineBudget
      count
      compositionFactor
      compositionOverhead

/--
Conditional machine-cost theorem for the complete announced local-plus-composed
execution.
-/
theorem explicitFamilyWithCompositionMachineCost_le_calibrated
    (count : Nat)
    (localMachine compositionMachine : MachineCostModel)
    (localFactor localOverhead : Nat)
    (compositionFactor compositionOverhead : Nat)
    (localBridge :
      RepresentationMachineBridge
        (explicitFamilyRepresentationAtomicCosts count)
        localMachine
        localFactor
        localOverhead)
    (compositionBridge :
      RepresentationMachineBridge
        (composedClosurePhaseRepresentationAtomicCosts count)
        compositionMachine
        compositionFactor
        compositionOverhead) :
    explicitFamilyWithCompositionMachineChargedCost
        count
        localMachine
        compositionMachine ≤
      explicitFamilyWithCompositionCalibratedMachineBudget
        count
        localFactor
        localOverhead
        compositionFactor
        compositionOverhead := by
  unfold explicitFamilyWithCompositionMachineChargedCost
  unfold explicitFamilyWithCompositionCalibratedMachineBudget
  exact
    Nat.add_le_add
      (machineChargedCost_le_calibrated
        (explicitFamilyComplexityCounts count)
        (explicitFamilyRepresentationAtomicCosts count)
        localMachine
        localFactor
        localOverhead
        localBridge)
      (machineChargedCost_le_calibrated
        (composedClosurePhaseCounts count)
        (composedClosurePhaseRepresentationAtomicCosts count)
        compositionMachine
        compositionFactor
        compositionOverhead
        compositionBridge)

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.explicitFamilyLocalMachineChargedCost
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseMachineChargedCost
#print axioms ConstitutiveSearch.SAT.explicitFamilyWithCompositionMachineChargedCost
#print axioms ConstitutiveSearch.SAT.explicitFamilyLocalCalibratedMachineBudget
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseCalibratedMachineBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyWithCompositionCalibratedMachineBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyWithCompositionMachineCost_le_calibrated
/- AXIOM_AUDIT_END -/
