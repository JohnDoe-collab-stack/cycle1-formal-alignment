import ConstitutiveSearch.SAT.TrajectoryConstitutedLocalSchedule
import ConstitutiveSearch.SAT.ExplicitFamilyConstitutiveProfile
import ConstitutiveSearch.SAT.ExplicitFamilyInputComplexity

/-!
# Accounting for trajectory-constituted local schedules

TrajectoryConstitutedLocalSchedule extracts one proof-relevant local sibling
relation per constitutive step of F(n), validates each relation with the exact
step-local generatedStructuralFlipAtSearch indexed by that step's own var, and
executes each relation by an actual candidate-free ClosureSearch run.

This module connects that schedule to the pre-existing complexity profile
without double counting.

Production is not introduced as a new phase:
* the produced local transport atoms are exactly the certificateAtoms already
  charged by explicitFamilyComplexityCounts;
* the schedule variable projection is exactly trajectory.decisionVars, whose
  length is already charged by provenanceUnits.

Validation and local execution are kept separate:
* validation contributes one direct relationFindCall per constituted step;
* local execution contributes one direct closurePrimitiveQuery per step and
  zero closureCompositionCandidates.

Because each schedule entry uses the exact var carried by that constitutive
step, there is no scan over future trajectory variables and no global provenance
search hidden inside these local calls.

The representation charge uses the existing direct-flip AtomicCosts model.  It
remains a representation-level charge, not a machine-runtime theorem.
-/

namespace ConstitutiveSearch
namespace SAT

/--
The endogenous schedule production count is exactly the certificateAtoms
coordinate already present in the local F(n) profile.
-/
theorem explicitFamilyConstitutedProduction_matchesCertificateAtoms
    (count : Nat) :
    (explicitFamilyComplexityCounts
        count).certificateAtoms =
      ConstitutedLocalSchedule.atomCount
        (explicitFamilyConstitutedLocalWitnesses
          count) := by
  change
    count =
      ConstitutedLocalSchedule.atomCount
        (explicitFamilyConstitutedLocalWitnesses
          count)
  exact
    (explicitFamilyConstitutedLocalAtomCount
      count).symm

/--
The extracted schedule records exactly the trajectory decision variables, in
the same order.
-/
theorem explicitFamilyConstitutedProduction_variablesExact
    (count : Nat) :
    (explicitFamilyConstitutedLocalWitnesses
      count).map
        (fun entry => entry.var) =
      (explicitFamilyResourceTrajectory
        count).trajectory.decisionVars :=
  explicitFamilyConstitutedLocalWitnesses_vars
    count

/--
The trajectory-derived provenance length is exactly the provenanceUnits already
charged by the local F(n) profile.
-/
theorem explicitFamilyConstitutedProduction_matchesProvenanceUnits
    (count : Nat) :
    (explicitFamilyComplexityCounts
        count).provenanceUnits =
      (explicitFamilyResourceTrajectory
        count).trajectory.decisionVars.length := by
  change
    count =
      (explicitFamilyResourceTrajectory
        count).trajectory.decisionVars.length
  exact
    ((explicitFamilyResourceTrajectory
      count).trajectory.decisionVars_length).symm

/--
Executable validation phase for the already-produced local schedule.

No syntax, frontier, provenance, or certificate production is charged again.
-/
def explicitFamilyConstitutedValidationCounts
    (count : Nat) :
    ComplexityCounts :=
  { syntaxUnits := 0
    frontierSlots := 0
    provenanceUnits := 0
    certificateAtoms := 0
    relationFindCalls :=
      ConstitutedLocalSchedule.validationPrimitiveQueries
        (explicitFamilyConstitutedLocalWitnesses
          count)
    closurePrimitiveQueries := 0
    closureCompositionCandidates := 0
    terminalChecks := 0 }

/--
Candidate-free local execution phase for the already-validated schedule.

These are actual ClosureSearch statistics aggregated from the step-local runs.
-/
def explicitFamilyConstitutedExecutionCounts
    (count : Nat) :
    ComplexityCounts :=
  { syntaxUnits := 0
    frontierSlots := 0
    provenanceUnits := 0
    certificateAtoms := 0
    relationFindCalls := 0
    closurePrimitiveQueries :=
      ConstitutedLocalSchedule.executionPrimitiveQueries
        (explicitFamilyConstitutedLocalWitnesses
          count)
    closureCompositionCandidates :=
      ConstitutedLocalSchedule.executionCompositionCandidates
        (explicitFamilyConstitutedLocalWitnesses
          count)
    terminalChecks := 0 }

/-- Validation performs exactly n direct step-local relation-find calls. -/
theorem explicitFamilyConstitutedValidationCounts_relationFindCalls
    (count : Nat) :
    (explicitFamilyConstitutedValidationCounts
      count).relationFindCalls =
      count := by
  change
    ConstitutedLocalSchedule.validationPrimitiveQueries
        (explicitFamilyConstitutedLocalWitnesses
          count) =
      count
  exact
    explicitFamilyConstitutedLocalValidationQueries
      count

/-- Local execution performs exactly n direct primitive queries. -/
theorem explicitFamilyConstitutedExecutionCounts_primitiveQueries
    (count : Nat) :
    (explicitFamilyConstitutedExecutionCounts
      count).closurePrimitiveQueries =
      count := by
  change
    ConstitutedLocalSchedule.executionPrimitiveQueries
        (explicitFamilyConstitutedLocalWitnesses
          count) =
      count
  exact
    explicitFamilyConstitutedLocalExecutionQueries
      count

/-- Local execution performs no composition-candidate inspections. -/
theorem explicitFamilyConstitutedExecutionCounts_compositionCandidates
    (count : Nat) :
    (explicitFamilyConstitutedExecutionCounts
      count).closureCompositionCandidates =
      0 := by
  change
    ConstitutedLocalSchedule.executionCompositionCandidates
        (explicitFamilyConstitutedLocalWitnesses
          count) =
      0
  exact
    explicitFamilyConstitutedLocalExecutionCompositionCandidates
      count

/-- Representation charge of executable step-local validation. -/
def explicitFamilyConstitutedValidationRepresentationCharge
    (count : Nat) :
    Nat :=
  chargedCost
    (explicitFamilyConstitutedValidationCounts
      count)
    (explicitFamilyRepresentationAtomicCosts
      count)

/-- Representation charge of actual candidate-free local execution. -/
def explicitFamilyConstitutedExecutionRepresentationCharge
    (count : Nat) :
    Nat :=
  chargedCost
    (explicitFamilyConstitutedExecutionCounts
      count)
    (explicitFamilyRepresentationAtomicCosts
      count)

/-- Validation charge is exactly n direct relation-query charges. -/
theorem explicitFamilyConstitutedValidationRepresentationCharge_eq
    (count : Nat) :
    explicitFamilyConstitutedValidationRepresentationCharge
        count =
      count *
        explicitFamilyRelationEqualityChargeBudget
          count := by
  unfold explicitFamilyConstitutedValidationRepresentationCharge
  unfold chargedCost
  unfold explicitFamilyConstitutedValidationCounts
  unfold explicitFamilyRepresentationAtomicCosts
  rw [
    explicitFamilyConstitutedLocalValidationQueries
  ]
  simp

/-- Local execution charge is exactly n direct primitive-query charges. -/
theorem explicitFamilyConstitutedExecutionRepresentationCharge_eq
    (count : Nat) :
    explicitFamilyConstitutedExecutionRepresentationCharge
        count =
      count *
        explicitFamilyRelationEqualityChargeBudget
          count := by
  unfold explicitFamilyConstitutedExecutionRepresentationCharge
  unfold chargedCost
  unfold explicitFamilyConstitutedExecutionCounts
  unfold explicitFamilyRepresentationAtomicCosts
  rw [
    explicitFamilyConstitutedLocalExecutionQueries,
    explicitFamilyConstitutedLocalExecutionCompositionCandidates
  ]
  simp

/--
Input-indexed polynomial envelope used for either validation or local execution
representation charge.
-/
def explicitFamilyConstitutedLocalQueryInputBudget
    (count : Nat) :
    Nat :=
  explicitFamilyInputBitSize count *
    explicitFamilyRelationPolynomialBudget
      (explicitFamilyInputBitSize count)

/-- Validation representation charge is polynomially bounded in actual input size. -/
theorem explicitFamilyConstitutedValidationRepresentationCharge_le_inputBudget
    (count : Nat) :
    explicitFamilyConstitutedValidationRepresentationCharge
        count ≤
      explicitFamilyConstitutedLocalQueryInputBudget
        count := by
  rw [
    explicitFamilyConstitutedValidationRepresentationCharge_eq,
    explicitFamilyRelationEqualityChargeBudget_eq_polynomial
  ]
  unfold explicitFamilyConstitutedLocalQueryInputBudget
  exact
    natMulLeMul
      (explicitFamilyIndex_le_inputBitSize
        count)
      (explicitFamilyRelationPolynomialBudget_mono
        (explicitFamilyIndex_le_inputBitSize
          count))

/-- Local execution representation charge is polynomially bounded in actual input size. -/
theorem explicitFamilyConstitutedExecutionRepresentationCharge_le_inputBudget
    (count : Nat) :
    explicitFamilyConstitutedExecutionRepresentationCharge
        count ≤
      explicitFamilyConstitutedLocalQueryInputBudget
        count := by
  rw [
    explicitFamilyConstitutedExecutionRepresentationCharge_eq,
    explicitFamilyRelationEqualityChargeBudget_eq_polynomial
  ]
  unfold explicitFamilyConstitutedLocalQueryInputBudget
  exact
    natMulLeMul
      (explicitFamilyIndex_le_inputBitSize
        count)
      (explicitFamilyRelationPolynomialBudget_mono
        (explicitFamilyIndex_le_inputBitSize
          count))

/--
Single evidence bundle tying endogenous production, executable validation, and
actual candidate-free local execution to the announced F(n) accounting
coordinates.
-/
structure ExplicitFamilyConstitutedLocalAccountingEvidence
    (count : Nat) : Prop where
  productionCertificateExact :
    (explicitFamilyComplexityCounts
        count).certificateAtoms =
      ConstitutedLocalSchedule.atomCount
        (explicitFamilyConstitutedLocalWitnesses
          count)
  productionVariablesExact :
    (explicitFamilyConstitutedLocalWitnesses
      count).map
        (fun entry => entry.var) =
      (explicitFamilyResourceTrajectory
        count).trajectory.decisionVars
  productionProvenanceExact :
    (explicitFamilyComplexityCounts
        count).provenanceUnits =
      (explicitFamilyResourceTrajectory
        count).trajectory.decisionVars.length
  validationSucceeds :
    ConstitutedLocalSchedule.ValidationSucceeds
      (explicitFamilyConstitutedLocalWitnesses
        count)
  validationFindExact :
    (explicitFamilyConstitutedValidationCounts
      count).relationFindCalls =
      count
  localExecutions :
    ConstitutedLocalSchedule.HasLocalExecutions
      (explicitFamilyConstitutedLocalWitnesses
        count)
  executionPrimitiveExact :
    (explicitFamilyConstitutedExecutionCounts
      count).closurePrimitiveQueries =
      count
  executionCompositionExact :
    (explicitFamilyConstitutedExecutionCounts
      count).closureCompositionCandidates =
      0

/-- Complete endogenous production/validation/execution evidence for every F(n). -/
theorem explicitFamilyConstitutedLocalAccountingEvidence
    (count : Nat) :
    ExplicitFamilyConstitutedLocalAccountingEvidence
      count :=
  { productionCertificateExact :=
      explicitFamilyConstitutedProduction_matchesCertificateAtoms
        count
    productionVariablesExact :=
      explicitFamilyConstitutedProduction_variablesExact
        count
    productionProvenanceExact :=
      explicitFamilyConstitutedProduction_matchesProvenanceUnits
        count
    validationSucceeds :=
      explicitFamilyConstitutedLocalValidationSucceeds
        count
    validationFindExact :=
      explicitFamilyConstitutedValidationCounts_relationFindCalls
        count
    localExecutions :=
      explicitFamilyConstitutedLocalHasLocalExecutions
        count
    executionPrimitiveExact :=
      explicitFamilyConstitutedExecutionCounts_primitiveQueries
        count
    executionCompositionExact :=
      explicitFamilyConstitutedExecutionCounts_compositionCandidates
        count }

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedProduction_matchesCertificateAtoms
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedProduction_variablesExact
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedProduction_matchesProvenanceUnits
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedValidationCounts
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedExecutionCounts
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedValidationCounts_relationFindCalls
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedExecutionCounts_primitiveQueries
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedExecutionCounts_compositionCandidates
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedValidationRepresentationCharge
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedExecutionRepresentationCharge
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedValidationRepresentationCharge_eq
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedExecutionRepresentationCharge_eq
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalQueryInputBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedValidationRepresentationCharge_le_inputBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedExecutionRepresentationCharge_le_inputBudget
#print axioms ConstitutiveSearch.SAT.ExplicitFamilyConstitutedLocalAccountingEvidence
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalAccountingEvidence
/- AXIOM_AUDIT_END -/
