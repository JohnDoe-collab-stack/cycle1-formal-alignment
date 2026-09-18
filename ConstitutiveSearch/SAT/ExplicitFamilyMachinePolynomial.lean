import ConstitutiveSearch.MachineCostPolynomial
import ConstitutiveSearch.SAT.ExplicitFamilyInputPolynomialProfile
import ConstitutiveSearch.SAT.ExplicitFamilyMachineComplexity

/-!
# Conditional input-polynomial machine cost for the explicit SAT family

The constitutive profile and representation layers are already proved
polynomially bounded in the concrete binary input size.  This module supplies
the remaining representation-atomic bounds needed by MachineCostPolynomial.

No concrete machine bridge is invented.  The final theorem is conditional on
two explicit families of RepresentationMachineBridge witnesses, one for the
local F(n) phase and one for the added composition phase, with fixed affine
calibration constants.
-/

namespace ConstitutiveSearch
namespace SAT

/--
Lift an explicit polynomial envelope in the family index to an input-indexed
envelope using n <= explicitFamilyInputBitSize n.
-/
theorem inputPolynomialBounded_of_indexEnvelope
    {cost : Nat → Nat}
    (envelope : CostPolynomial)
    (costLe :
      ∀ count : Nat,
        cost count ≤
          envelope.eval count) :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      cost :=
  ⟨envelope,
    fun count =>
      Nat.le_trans
        (costLe count)
        (envelope.eval_mono
          (explicitFamilyIndex_le_inputBitSize
            count))⟩

/-- One-decision composition provenance polynomial n+6. -/
def composedProvenanceUnitCostPolynomial :
    CostPolynomial :=
  .add
    (.add
      (costInputPlus 2)
      (.constant 3))
    (.constant 1)

/-- Exact evaluation of the one-decision composition provenance envelope. -/
theorem composedProvenanceUnitCostPolynomial_eval
    (count : Nat) :
    composedProvenanceUnitCostPolynomial.eval count =
      StructuralDecisionHistory.binaryBudget
        (count + 2)
        1 := by
  rw [
    StructuralDecisionHistory.binaryBudget_closed
      (count + 2)
      1
  ]
  rw [Nat.one_mul]
  rfl

/-- Event counts of the local F(n) phase are input-polynomially bounded. -/
theorem explicitFamilyComplexityCounts_inputPolynomiallyBounded :
    ComplexityCountsFamilyInputPolynomiallyBounded
      explicitFamilyInputBitSize
      explicitFamilyComplexityCounts := by
  simpa only [
    explicitFamilyConstitutiveProfile
  ] using
    ComplexityCountsFamilyInputPolynomiallyBounded.ofProfile
      explicitFamilyConstitutiveProfile_inputPolynomiallyBounded

/-- Event counts of the added composition phase are input-polynomially bounded. -/
theorem composedClosurePhaseCounts_inputPolynomiallyBounded :
    ComplexityCountsFamilyInputPolynomiallyBounded
      explicitFamilyInputBitSize
      composedClosurePhaseCounts := by
  simpa only [
    composedClosureConstitutivePhaseProfile
  ] using
    ComplexityCountsFamilyInputPolynomiallyBounded.ofProfile
      composedClosureConstitutivePhaseProfile_inputPolynomiallyBounded

/-- Every local representation-level atomic cost is polynomial in inputBits. -/
theorem explicitFamilyRepresentationAtomicCosts_inputPolynomiallyBounded :
    AtomicCostsFamilyInputPolynomiallyBounded
      explicitFamilyInputBitSize
      explicitFamilyRepresentationAtomicCosts :=
  { syntaxUnit :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        1
    frontierSlot :=
      inputPolynomialBounded_of_indexEnvelope
        explicitFamilyStateCostPolynomial
        (fun count => by
          calc
            explicitFamilyStateBinaryBudget count
                =
              explicitFamilyStatePolynomialBudget count :=
                explicitFamilyStateBinaryBudget_eq_polynomial
                  count
            _ =
              explicitFamilyStateCostPolynomial.eval count :=
                (explicitFamilyStateCostPolynomial_eval
                  count).symm)
    provenanceUnit :=
      inputPolynomialBounded_of_indexEnvelope
        explicitFamilyProvenanceCostPolynomial
        (fun count => by
          calc
            explicitFamilyProvenanceUnitBinaryBudget count
                =
              explicitFamilyProvenancePolynomialBudget count :=
                explicitFamilyProvenanceUnitBinaryBudget_eq_polynomial
                  count
            _ =
              explicitFamilyProvenanceCostPolynomial.eval count :=
                (explicitFamilyProvenanceCostPolynomial_eval
                  count).symm)
    certificateAtom :=
      inputPolynomialBounded_of_indexEnvelope
        explicitFamilyCertificateCostPolynomial
        (fun count =>
          Nat.le_trans
            (explicitFamilyCertificateAtomBinaryBudget_le_polynomial
              count)
            (Nat.le_of_eq
              (explicitFamilyCertificateCostPolynomial_eval
                count).symm))
    relationFindCall :=
      inputPolynomialBounded_of_indexEnvelope
        explicitFamilyRelationCostPolynomial
        (fun count => by
          calc
            explicitFamilyRelationEqualityChargeBudget count
                =
              explicitFamilyRelationPolynomialBudget count :=
                explicitFamilyRelationEqualityChargeBudget_eq_polynomial
                  count
            _ =
              explicitFamilyRelationCostPolynomial.eval count :=
                (explicitFamilyRelationCostPolynomial_eval
                  count).symm)
    closurePrimitiveQuery :=
      inputPolynomialBounded_of_indexEnvelope
        explicitFamilyRelationCostPolynomial
        (fun count => by
          calc
            explicitFamilyRelationEqualityChargeBudget count
                =
              explicitFamilyRelationPolynomialBudget count :=
                explicitFamilyRelationEqualityChargeBudget_eq_polynomial
                  count
            _ =
              explicitFamilyRelationCostPolynomial.eval count :=
                (explicitFamilyRelationCostPolynomial_eval
                  count).symm)
    closureCompositionCandidate :=
      inputPolynomialBounded_of_indexEnvelope
        explicitFamilyStateCostPolynomial
        (fun count => by
          calc
            explicitFamilyStateBinaryBudget count
                =
              explicitFamilyStatePolynomialBudget count :=
                explicitFamilyStateBinaryBudget_eq_polynomial
                  count
            _ =
              explicitFamilyStateCostPolynomial.eval count :=
                (explicitFamilyStateCostPolynomial_eval
                  count).symm)
    terminalCheck :=
      inputPolynomialBounded_of_indexEnvelope
        explicitFamilyHistoryCostPolynomial
        (fun count => by
          calc
            StructuralDecisionHistory.binaryBudget
                count
                count
                =
              explicitFamilyHistoryPolynomialBudget count :=
                explicitFamilyHistoryBinaryBudget_eq_polynomial
                  count
            _ =
              explicitFamilyHistoryCostPolynomial.eval count :=
                (explicitFamilyHistoryCostPolynomial_eval
                  count).symm) }

/-- Every representation-level atomic cost of the composition phase is polynomial. -/
theorem composedClosurePhaseRepresentationAtomicCosts_inputPolynomiallyBounded :
    AtomicCostsFamilyInputPolynomiallyBounded
      explicitFamilyInputBitSize
      composedClosurePhaseRepresentationAtomicCosts :=
  { syntaxUnit :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        1
    frontierSlot :=
      inputPolynomialBounded_of_indexEnvelope
        composedStateCostPolynomial
        (fun count => by
          calc
            composedStateBinaryBudget count
                =
              composedStatePolynomialBudget count :=
                composedStateBinaryBudget_eq_polynomial
                  count
            _ =
              composedStateCostPolynomial.eval count :=
                (composedStateCostPolynomial_eval
                  count).symm)
    provenanceUnit :=
      inputPolynomialBounded_of_indexEnvelope
        composedProvenanceUnitCostPolynomial
        (fun count =>
          Nat.le_of_eq
            (composedProvenanceUnitCostPolynomial_eval
              count).symm)
    certificateAtom :=
      inputPolynomialBounded_of_indexEnvelope
        composedCertificateAtomCostPolynomial
        (fun count => by
          calc
            composedCertificateAtomBinaryBudget count
                =
              composedCertificateAtomPolynomialBudget count :=
                composedCertificateAtomBinaryBudget_eq_polynomial
                  count
            _ =
              composedCertificateAtomCostPolynomial.eval count :=
                (composedCertificateAtomCostPolynomial_eval
                  count).symm)
    relationFindCall :=
      inputPolynomialBounded_of_indexEnvelope
        composedSingleFlipEqualityCostPolynomial
        (fun count => by
          calc
            composedSingleFlipEqualityBinaryBudget count
                =
              composedSingleFlipEqualityPolynomialBudget count :=
                composedSingleFlipEqualityBinaryBudget_eq_polynomial
                  count
            _ =
              composedSingleFlipEqualityCostPolynomial.eval count :=
                (composedSingleFlipEqualityCostPolynomial_eval
                  count).symm)
    closurePrimitiveQuery :=
      inputPolynomialBounded_of_indexEnvelope
        composedPrimitiveQueryCostPolynomial
        (fun count => by
          calc
            composedPrimitiveQueryBinaryBudget count
                =
              composedPrimitiveQueryPolynomialBudget count :=
                composedPrimitiveQueryBinaryBudget_eq_polynomial
                  count
            _ =
              composedPrimitiveQueryCostPolynomial.eval count :=
                (composedPrimitiveQueryCostPolynomial_eval
                  count).symm)
    closureCompositionCandidate :=
      inputPolynomialBounded_of_indexEnvelope
        composedStateCostPolynomial
        (fun count => by
          calc
            composedStateBinaryBudget count
                =
              composedStatePolynomialBudget count :=
                composedStateBinaryBudget_eq_polynomial
                  count
            _ =
              composedStateCostPolynomial.eval count :=
                (composedStateCostPolynomial_eval
                  count).symm)
    terminalCheck :=
      inputPolynomialBounded_of_indexEnvelope
        composedHistoryCostPolynomial
        (fun count => by
          calc
            composedHistoryBinaryBudget count
                =
              composedHistoryPolynomialBudget count :=
                composedHistoryBinaryBudget_eq_polynomial
                  count
            _ =
              composedHistoryCostPolynomial.eval count :=
                (composedHistoryCostPolynomial_eval
                  count).symm) }

/--
Local machine charge is polynomial in inputBits under one fixed calibration and
one explicit bridge per family member.
-/
theorem explicitFamilyLocalMachineCost_inputPolynomiallyBounded
    (machine : Nat → MachineCostModel)
    (factor overhead : Nat)
    (bridges :
      ∀ count : Nat,
        RepresentationMachineBridge
          (explicitFamilyRepresentationAtomicCosts count)
          (machine count)
          factor
          overhead) :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        explicitFamilyLocalMachineChargedCost
          count
          (machine count)) := by
  change
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        machineChargedCost
          (explicitFamilyComplexityCounts count)
          (machine count))
  exact
    machineChargedCost_inputPolynomiallyBounded
      explicitFamilyComplexityCounts_inputPolynomiallyBounded
      explicitFamilyRepresentationAtomicCosts_inputPolynomiallyBounded
      factor
      overhead
      bridges

/--
Composition-phase machine charge is polynomial in inputBits under the
corresponding fixed calibration bridge family.
-/
theorem composedClosurePhaseMachineCost_inputPolynomiallyBounded
    (machine : Nat → MachineCostModel)
    (factor overhead : Nat)
    (bridges :
      ∀ count : Nat,
        RepresentationMachineBridge
          (composedClosurePhaseRepresentationAtomicCosts count)
          (machine count)
          factor
          overhead) :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        composedClosurePhaseMachineChargedCost
          count
          (machine count)) := by
  change
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        machineChargedCost
          (composedClosurePhaseCounts count)
          (machine count))
  exact
    machineChargedCost_inputPolynomiallyBounded
      composedClosurePhaseCounts_inputPolynomiallyBounded
      composedClosurePhaseRepresentationAtomicCosts_inputPolynomiallyBounded
      factor
      overhead
      bridges

/--
The complete local-plus-composition machine charge is polynomially bounded in
the concrete binary input size whenever both fixed-calibration bridge families
are supplied.
-/
theorem explicitFamilyWithCompositionMachineCost_inputPolynomiallyBounded
    (localMachine compositionMachine :
      Nat → MachineCostModel)
    (localFactor localOverhead :
      Nat)
    (compositionFactor compositionOverhead :
      Nat)
    (localBridges :
      ∀ count : Nat,
        RepresentationMachineBridge
          (explicitFamilyRepresentationAtomicCosts count)
          (localMachine count)
          localFactor
          localOverhead)
    (compositionBridges :
      ∀ count : Nat,
        RepresentationMachineBridge
          (composedClosurePhaseRepresentationAtomicCosts count)
          (compositionMachine count)
          compositionFactor
          compositionOverhead) :
    InputPolynomiallyBounded
      explicitFamilyInputBitSize
      (fun count =>
        explicitFamilyWithCompositionMachineChargedCost
          count
          (localMachine count)
          (compositionMachine count)) := by
  unfold explicitFamilyWithCompositionMachineChargedCost
  exact
    InputPolynomiallyBounded.add_same
      (explicitFamilyLocalMachineCost_inputPolynomiallyBounded
        localMachine
        localFactor
        localOverhead
        localBridges)
      (composedClosurePhaseMachineCost_inputPolynomiallyBounded
        compositionMachine
        compositionFactor
        compositionOverhead
        compositionBridges)

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.inputPolynomialBounded_of_indexEnvelope
#print axioms ConstitutiveSearch.SAT.composedProvenanceUnitCostPolynomial
#print axioms ConstitutiveSearch.SAT.composedProvenanceUnitCostPolynomial_eval
#print axioms ConstitutiveSearch.SAT.explicitFamilyComplexityCounts_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseCounts_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.explicitFamilyRepresentationAtomicCosts_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseRepresentationAtomicCosts_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.explicitFamilyLocalMachineCost_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseMachineCost_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.explicitFamilyWithCompositionMachineCost_inputPolynomiallyBounded
/- AXIOM_AUDIT_END -/
