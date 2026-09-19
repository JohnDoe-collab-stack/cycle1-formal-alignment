import ConstitutiveSearch.SAT.TrajectoryConstitutedLocalSchedule
import ConstitutiveSearch.SAT.ExplicitFamilyConstitutiveProfile
import ConstitutiveSearch.SAT.ExplicitFamilyInputComplexity

/-!
# Accounting for trajectory-constituted local schedules

TrajectoryConstitutedLocalSchedule extracts one proof-relevant local sibling
witness per constitutive step of F(n), validates those codes executably, and
admits candidate-free local execution.

This module connects that new schedule to the pre-existing complexity profile
without double counting.

Production is not introduced as a new phase:
* the produced local transport atoms are exactly the certificateAtoms already
  charged by explicitFamilyComplexityCounts;
* the provenance domain is exactly the trajectory decision-variable history
  already charged by provenanceUnits.

Validation and local execution are kept separate:
* validation contributes one relationFindCall per constituted local code;
* local execution contributes one closurePrimitiveQuery per local code and zero
  closureCompositionCandidates.

The representation charge of each additional phase is then derived from the
existing concrete AtomicCosts model.  This remains a representation-level
charge, not a machine-runtime theorem.
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
The trajectory-derived provenance domain has exactly the provenanceUnits already
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

Execution performs one primitive query per local code and no composition
candidate inspection.
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

/-- Validation contributes exactly n relation-find calls. -/
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

/-- Local execution contributes exactly n primitive queries. -/
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

/-- Local execution contributes no composition-candidate inspections. -/
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

/-- Representation charge of executable validation under the existing F(n) cost model. -/
def explicitFamilyConstitutedValidationRepresentationCharge
    (count : Nat) :
    Nat :=
  chargedCost
    (explicitFamilyConstitutedValidationCounts
      count)
    (explicitFamilyRepresentationAtomicCosts
      count)

/-- Representation charge of candidate-free local execution. -/
def explicitFamilyConstitutedExecutionRepresentationCharge
    (count : Nat) :
    Nat :=
  chargedCost
    (explicitFamilyConstitutedExecutionCounts
      count)
    (explicitFamilyRepresentationAtomicCosts
      count)

/-- Validation charge is exactly n relation-query charges. -/
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

/-- Local execution charge is exactly n primitive-query charges. -/
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

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedProduction_matchesCertificateAtoms
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
/- AXIOM_AUDIT_END -/
