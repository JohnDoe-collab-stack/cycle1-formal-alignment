import ConstitutiveSearch.SAT.TrajectoryConstitutedLocalSchedule
import ConstitutiveSearch.SAT.ProvenanceSearchCosts
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

A provenance-restricted primitive query may scan several trajectory variables.
That internal cost is exposed explicitly and bounded by the provenance length;
the validation/execution AtomicCosts therefore charge one top-level primitive
query by the full provenance-scan envelope rather than by one direct equality
test.  This remains a representation-level charge, not a machine-runtime
theorem.
-/

namespace ConstitutiveSearch
namespace SAT

namespace ConstitutedLocalSchedule

/--
Total number of variable-level generatedStructuralFlipAtSearch attempts made by
the provenance search while validating or executing one complete local schedule.
-/
def provenanceVariableQueries
    {rootFormula : Cnf}
    {vars : List Var} :
    List
      (ConstitutedLocalWitness
        rootFormula
        vars) →
      Nat
  | [] =>
      0
  | entry :: rest =>
      provenanceStructuralFlipSearchVariableQueries
          rootFormula
          vars
          entry.source
          entry.target +
        provenanceVariableQueries rest

/--
A schedule with k entries over a provenance domain of m variables performs at
most k*m variable-level generated flip searches.
-/
theorem provenanceVariableQueries_le_length_mul_varsLength
    {rootFormula : Cnf}
    {vars : List Var}
    (schedule :
      List
        (ConstitutedLocalWitness
          rootFormula
          vars)) :
    provenanceVariableQueries schedule ≤
      schedule.length * vars.length := by
  induction schedule with
  | nil =>
      rfl
  | cons entry rest inductionHypothesis =>
      have headLe :
          provenanceStructuralFlipSearchVariableQueries
              rootFormula
              vars
              entry.source
              entry.target ≤
            vars.length :=
        provenanceStructuralFlipSearchVariableQueries_le_length
          rootFormula
          vars
          entry.source
          entry.target
      calc
        provenanceVariableQueries
            (entry :: rest)
            =
          provenanceStructuralFlipSearchVariableQueries
              rootFormula
              vars
              entry.source
              entry.target +
            provenanceVariableQueries rest :=
              rfl
        _ ≤
          vars.length +
            rest.length * vars.length :=
              Nat.add_le_add
                headLe
                inductionHypothesis
        _ =
          (entry :: rest).length *
            vars.length := by
              rw [
                List.length_cons,
                Nat.succ_eq_add_one,
                Nat.add_mul,
                Nat.one_mul,
                Nat.add_comm
              ]

end ConstitutedLocalSchedule

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

/-- Variable-level provenance-search work of the endogenous F(n) schedule. -/
def explicitFamilyConstitutedProvenanceVariableQueries
    (count : Nat) :
    Nat :=
  ConstitutedLocalSchedule.provenanceVariableQueries
    (explicitFamilyConstitutedLocalWitnesses
      count)

/--
The internal provenance-search work is at most n^2: there are n local queries,
and each can inspect at most the n variables constituted by the trajectory.
-/
theorem explicitFamilyConstitutedProvenanceVariableQueries_le_square
    (count : Nat) :
    explicitFamilyConstitutedProvenanceVariableQueries
        count ≤
      count * count := by
  unfold explicitFamilyConstitutedProvenanceVariableQueries
  have bounded :=
    ConstitutedLocalSchedule.provenanceVariableQueries_le_length_mul_varsLength
      (explicitFamilyConstitutedLocalWitnesses
        count)
  rw [
    explicitFamilyConstitutedLocalWitnesses_length,
    (explicitFamilyResourceTrajectory
      count).trajectory.decisionVars_length
  ] at bounded
  exact bounded

/--
Representation envelope for one top-level provenance-restricted primitive
query.  One query examines at most n variable-specific structural flips.
-/
def explicitFamilyConstitutedProvenanceQueryRepresentationBudget
    (count : Nat) :
    Nat :=
  count *
    explicitFamilyRelationEqualityChargeBudget
      count

/--
Atomic-cost model for validation and local execution of the provenance-derived
schedule.  Only the two event classes used by these phases receive nonzero
charges.

Unlike the direct-flip F(n) profile, one top-level primitive query is charged by
the full provenance-scan envelope rather than by one equality test.
-/
def explicitFamilyConstitutedScheduleAtomicCosts
    (count : Nat) :
    AtomicCosts :=
  { syntaxUnit := 0
    frontierSlot := 0
    provenanceUnit := 0
    certificateAtom := 0
    relationFindCall :=
      explicitFamilyConstitutedProvenanceQueryRepresentationBudget
        count
    closurePrimitiveQuery :=
      explicitFamilyConstitutedProvenanceQueryRepresentationBudget
        count
    closureCompositionCandidate := 0
    terminalCheck := 0 }

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

/-- Representation charge of executable validation under the provenance-scan model. -/
def explicitFamilyConstitutedValidationRepresentationCharge
    (count : Nat) :
    Nat :=
  chargedCost
    (explicitFamilyConstitutedValidationCounts
      count)
    (explicitFamilyConstitutedScheduleAtomicCosts
      count)

/-- Representation charge of candidate-free local execution. -/
def explicitFamilyConstitutedExecutionRepresentationCharge
    (count : Nat) :
    Nat :=
  chargedCost
    (explicitFamilyConstitutedExecutionCounts
      count)
    (explicitFamilyConstitutedScheduleAtomicCosts
      count)

/-- Validation charge is n top-level queries, each charged by an n-variable scan. -/
theorem explicitFamilyConstitutedValidationRepresentationCharge_eq
    (count : Nat) :
    explicitFamilyConstitutedValidationRepresentationCharge
        count =
      count *
        (count *
          explicitFamilyRelationEqualityChargeBudget
            count) := by
  unfold explicitFamilyConstitutedValidationRepresentationCharge
  unfold chargedCost
  unfold explicitFamilyConstitutedValidationCounts
  unfold explicitFamilyConstitutedScheduleAtomicCosts
  unfold explicitFamilyConstitutedProvenanceQueryRepresentationBudget
  rw [
    explicitFamilyConstitutedLocalValidationQueries
  ]
  simp

/-- Local execution has the same conservative provenance-scan representation charge. -/
theorem explicitFamilyConstitutedExecutionRepresentationCharge_eq
    (count : Nat) :
    explicitFamilyConstitutedExecutionRepresentationCharge
        count =
      count *
        (count *
          explicitFamilyRelationEqualityChargeBudget
            count) := by
  unfold explicitFamilyConstitutedExecutionRepresentationCharge
  unfold chargedCost
  unfold explicitFamilyConstitutedExecutionCounts
  unfold explicitFamilyConstitutedScheduleAtomicCosts
  unfold explicitFamilyConstitutedProvenanceQueryRepresentationBudget
  rw [
    explicitFamilyConstitutedLocalExecutionQueries,
    explicitFamilyConstitutedLocalExecutionCompositionCandidates
  ]
  simp

/--
Input-indexed polynomial envelope used for either validation or local execution
representation charge.  The two inputBits factors respectively bound the number
of schedule entries and the provenance variables inspected by each query.
-/
def explicitFamilyConstitutedLocalQueryInputBudget
    (count : Nat) :
    Nat :=
  explicitFamilyInputBitSize count *
    (explicitFamilyInputBitSize count *
      explicitFamilyRelationPolynomialBudget
        (explicitFamilyInputBitSize count))

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
      (natMulLeMul
        (explicitFamilyIndex_le_inputBitSize
          count)
        (explicitFamilyRelationPolynomialBudget_mono
          (explicitFamilyIndex_le_inputBitSize
            count)))

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
      (natMulLeMul
        (explicitFamilyIndex_le_inputBitSize
          count)
        (explicitFamilyRelationPolynomialBudget_mono
          (explicitFamilyIndex_le_inputBitSize
            count)))

/--
Single evidence bundle tying endogenous production, executable validation, and
candidate-free local execution to the announced F(n) accounting coordinates.
-/
structure ExplicitFamilyConstitutedLocalAccountingEvidence
    (count : Nat) : Prop where
  productionCertificateExact :
    (explicitFamilyComplexityCounts
        count).certificateAtoms =
      ConstitutedLocalSchedule.atomCount
        (explicitFamilyConstitutedLocalWitnesses
          count)
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
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedProduction_matchesProvenanceUnits
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.provenanceVariableQueries
#print axioms ConstitutiveSearch.SAT.ConstitutedLocalSchedule.provenanceVariableQueries_le_length_mul_varsLength
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedProvenanceVariableQueries
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedProvenanceVariableQueries_le_square
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedProvenanceQueryRepresentationBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedScheduleAtomicCosts
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
