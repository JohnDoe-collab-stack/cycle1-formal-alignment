import ConstitutiveSearch.ConstitutiveComplexityInputPolynomial
import ConstitutiveSearch.SAT.ExplicitFamilyConstitutiveProfile

/-!
# Finite cost-polynomial syntax for the explicit SAT envelopes

Earlier SAT modules prove explicit polynomial budget functions by arithmetic on
Nat.  This module reifies those already-proved formulas into CostPolynomial
syntax.

The evaluation theorems are exact equalities.  No new asymptotic estimate is
introduced here.
-/

namespace ConstitutiveSearch
namespace SAT

/-- X + c. -/
def costInputPlus
    (constant : Nat) : CostPolynomial :=
  .add
    .input
    (.constant constant)

/-- c * X. -/
def costScaleInput
    (factor : Nat) : CostPolynomial :=
  .mul
    (.constant factor)
    .input

/-- c * X + d. -/
def costScaleInputPlus
    (factor offset : Nat) : CostPolynomial :=
  .add
    (costScaleInput factor)
    (.constant offset)

/-- Polynomial syntax for explicitFamilyFormulaPolynomialBudget. -/
def explicitFamilyFormulaCostPolynomial :
    CostPolynomial :=
  let tagged :=
    CostPolynomial.add
      (.mul
        (.constant 2)
        (costInputPlus 3))
      (.constant 1)
  .add
    (.mul
      .input
      (.add
        (.add
          (.add
            tagged
            tagged)
          (.constant 1))
        (.constant 1)))
    (.constant 1)

/-- Polynomial syntax for explicitFamilyHistoryPolynomialBudget. -/
def explicitFamilyHistoryCostPolynomial :
    CostPolynomial :=
  .add
    (.mul
      .input
      (costInputPlus 3))
    (.constant 1)

/-- Polynomial syntax for explicitFamilyStatePolynomialBudget. -/
def explicitFamilyStateCostPolynomial :
    CostPolynomial :=
  .add
    explicitFamilyFormulaCostPolynomial
    explicitFamilyHistoryCostPolynomial

/-- Polynomial syntax for explicitFamilyProvenancePolynomialBudget. -/
def explicitFamilyProvenanceCostPolynomial :
    CostPolynomial :=
  .add
    (.mul
      (.constant 1)
      (costInputPlus 3))
    (.constant 1)

/-- Polynomial syntax for explicitFamilyCertificatePolynomialBudget. -/
def explicitFamilyCertificateCostPolynomial :
    CostPolynomial :=
  .add
    (costInputPlus 1)
    (.constant 1)

/-- Polynomial syntax for explicitFamilyRelationPolynomialBudget. -/
def explicitFamilyRelationCostPolynomial :
    CostPolynomial :=
  .add
    (.add
      explicitFamilyFormulaCostPolynomial
      explicitFamilyFormulaCostPolynomial)
    (.add
      explicitFamilyHistoryCostPolynomial
      explicitFamilyHistoryCostPolynomial)

/-- Polynomial syntax for the complete local representation-cost envelope. -/
def explicitFamilyRepresentationCostPolynomial :
    CostPolynomial :=
  .add
    (costScaleInput 4)
    (.add
      (.mul
        (costScaleInputPlus 3 1)
        explicitFamilyStateCostPolynomial)
      (.add
        (.mul
          .input
          explicitFamilyProvenanceCostPolynomial)
        (.add
          (.mul
            .input
            explicitFamilyCertificateCostPolynomial)
          (.add
            (.mul
              (costScaleInput 2)
              explicitFamilyRelationCostPolynomial)
            explicitFamilyHistoryCostPolynomial))))

/-- Polynomial syntax for the n+2 decision-history composition budget. -/
def composedHistoryCostPolynomial :
    CostPolynomial :=
  let plusTwo :=
    costInputPlus 2
  .add
    (.mul
      plusTwo
      (.add
        plusTwo
        (.constant 3)))
    (.constant 1)

/-- Polynomial syntax for the composition-state budget. -/
def composedStateCostPolynomial :
    CostPolynomial :=
  .add
    explicitFamilyFormulaCostPolynomial
    composedHistoryCostPolynomial

/-- Polynomial syntax for one composition flip equality surface. -/
def composedSingleFlipEqualityCostPolynomial :
    CostPolynomial :=
  .add
    (.add
      explicitFamilyFormulaCostPolynomial
      explicitFamilyFormulaCostPolynomial)
    (.add
      composedHistoryCostPolynomial
      composedHistoryCostPolynomial)

/-- Polynomial syntax for one two-generator primitive closure query. -/
def composedPrimitiveQueryCostPolynomial :
    CostPolynomial :=
  .add
    composedSingleFlipEqualityCostPolynomial
    composedSingleFlipEqualityCostPolynomial

/-- Polynomial syntax for one composition certificate atom. -/
def composedCertificateAtomCostPolynomial :
    CostPolynomial :=
  .add
    (costInputPlus 2)
    (.constant 2)

/-- Polynomial syntax for the complete added composition phase. -/
def composedClosurePhaseRepresentationCostPolynomial :
    CostPolynomial :=
  .add
    (.mul
      (.constant 2)
      composedStateCostPolynomial)
    (.add
      (.mul
        (.constant 2)
        composedCertificateAtomCostPolynomial)
      (.add
        (.mul
          (.constant 3)
          composedPrimitiveQueryCostPolynomial)
        composedStateCostPolynomial))

theorem explicitFamilyFormulaCostPolynomial_eval
    (inputBits : Nat) :
    explicitFamilyFormulaCostPolynomial.eval inputBits =
      explicitFamilyFormulaPolynomialBudget inputBits := by
  rfl

theorem explicitFamilyHistoryCostPolynomial_eval
    (inputBits : Nat) :
    explicitFamilyHistoryCostPolynomial.eval inputBits =
      explicitFamilyHistoryPolynomialBudget inputBits := by
  rfl

theorem explicitFamilyStateCostPolynomial_eval
    (inputBits : Nat) :
    explicitFamilyStateCostPolynomial.eval inputBits =
      explicitFamilyStatePolynomialBudget inputBits := by
  rfl

theorem explicitFamilyProvenanceCostPolynomial_eval
    (inputBits : Nat) :
    explicitFamilyProvenanceCostPolynomial.eval inputBits =
      explicitFamilyProvenancePolynomialBudget inputBits := by
  rfl

theorem explicitFamilyCertificateCostPolynomial_eval
    (inputBits : Nat) :
    explicitFamilyCertificateCostPolynomial.eval inputBits =
      explicitFamilyCertificatePolynomialBudget inputBits := by
  rfl

theorem explicitFamilyRelationCostPolynomial_eval
    (inputBits : Nat) :
    explicitFamilyRelationCostPolynomial.eval inputBits =
      explicitFamilyRelationPolynomialBudget inputBits := by
  rfl

theorem explicitFamilyRepresentationCostPolynomial_eval
    (inputBits : Nat) :
    explicitFamilyRepresentationCostPolynomial.eval inputBits =
      explicitFamilyRepresentationPolynomialBudget inputBits := by
  rfl

theorem composedHistoryCostPolynomial_eval
    (inputBits : Nat) :
    composedHistoryCostPolynomial.eval inputBits =
      composedHistoryPolynomialBudget inputBits := by
  rfl

theorem composedStateCostPolynomial_eval
    (inputBits : Nat) :
    composedStateCostPolynomial.eval inputBits =
      composedStatePolynomialBudget inputBits := by
  rfl

theorem composedSingleFlipEqualityCostPolynomial_eval
    (inputBits : Nat) :
    composedSingleFlipEqualityCostPolynomial.eval inputBits =
      composedSingleFlipEqualityPolynomialBudget inputBits := by
  rfl

theorem composedPrimitiveQueryCostPolynomial_eval
    (inputBits : Nat) :
    composedPrimitiveQueryCostPolynomial.eval inputBits =
      composedPrimitiveQueryPolynomialBudget inputBits := by
  rfl

theorem composedCertificateAtomCostPolynomial_eval
    (inputBits : Nat) :
    composedCertificateAtomCostPolynomial.eval inputBits =
      composedCertificateAtomPolynomialBudget inputBits := by
  rfl

theorem composedClosurePhaseRepresentationCostPolynomial_eval
    (inputBits : Nat) :
    composedClosurePhaseRepresentationCostPolynomial.eval inputBits =
      composedClosurePhaseRepresentationPolynomialBudget inputBits := by
  rfl

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.costInputPlus
#print axioms ConstitutiveSearch.SAT.costScaleInput
#print axioms ConstitutiveSearch.SAT.costScaleInputPlus
#print axioms ConstitutiveSearch.SAT.explicitFamilyFormulaCostPolynomial
#print axioms ConstitutiveSearch.SAT.explicitFamilyHistoryCostPolynomial
#print axioms ConstitutiveSearch.SAT.explicitFamilyStateCostPolynomial
#print axioms ConstitutiveSearch.SAT.explicitFamilyProvenanceCostPolynomial
#print axioms ConstitutiveSearch.SAT.explicitFamilyCertificateCostPolynomial
#print axioms ConstitutiveSearch.SAT.explicitFamilyRelationCostPolynomial
#print axioms ConstitutiveSearch.SAT.explicitFamilyRepresentationCostPolynomial
#print axioms ConstitutiveSearch.SAT.composedHistoryCostPolynomial
#print axioms ConstitutiveSearch.SAT.composedStateCostPolynomial
#print axioms ConstitutiveSearch.SAT.composedSingleFlipEqualityCostPolynomial
#print axioms ConstitutiveSearch.SAT.composedPrimitiveQueryCostPolynomial
#print axioms ConstitutiveSearch.SAT.composedCertificateAtomCostPolynomial
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseRepresentationCostPolynomial
#print axioms ConstitutiveSearch.SAT.explicitFamilyFormulaCostPolynomial_eval
#print axioms ConstitutiveSearch.SAT.explicitFamilyHistoryCostPolynomial_eval
#print axioms ConstitutiveSearch.SAT.explicitFamilyStateCostPolynomial_eval
#print axioms ConstitutiveSearch.SAT.explicitFamilyProvenanceCostPolynomial_eval
#print axioms ConstitutiveSearch.SAT.explicitFamilyCertificateCostPolynomial_eval
#print axioms ConstitutiveSearch.SAT.explicitFamilyRelationCostPolynomial_eval
#print axioms ConstitutiveSearch.SAT.explicitFamilyRepresentationCostPolynomial_eval
#print axioms ConstitutiveSearch.SAT.composedHistoryCostPolynomial_eval
#print axioms ConstitutiveSearch.SAT.composedStateCostPolynomial_eval
#print axioms ConstitutiveSearch.SAT.composedSingleFlipEqualityCostPolynomial_eval
#print axioms ConstitutiveSearch.SAT.composedPrimitiveQueryCostPolynomial_eval
#print axioms ConstitutiveSearch.SAT.composedCertificateAtomCostPolynomial_eval
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseRepresentationCostPolynomial_eval
/- AXIOM_AUDIT_END -/
