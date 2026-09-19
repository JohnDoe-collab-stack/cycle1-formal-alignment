import ConstitutiveSearch.SAT.TrajectoryConstitutedLocalAccounting
import ConstitutiveSearch.SAT.ExplicitFamilyInputPolynomialProfile
import ConstitutiveSearch.SAT.ExplicitFamilyCostPolynomials

/-!
# Quantitative synthesis of the closed constituted SAT trajectory

This module closes the quantitative chain for the explicit family F(n):

  constituted trajectory
  -> endogenous local schedule
  -> production already charged by the base constitutive profile
  -> executable validation
  -> actual candidate-free local execution
  -> one total constitutive complexity profile
  -> input-polynomial bounds.

Production, validation and execution remain distinct phases.

Production does not create a new accounting vector: its certificateAtoms and
provenanceUnits are exactly the coordinates already charged by
explicitFamilyComplexityCounts.

Validation and execution therefore set certificateAtoms and provenanceUnits to
zero.  They add only the counters they actually execute and their corresponding
representation charges.

No recursive ClosureSearch upper envelope is substituted for executed counters.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Validation-only profile for the already-produced constituted local schedule. -/
def explicitFamilyConstitutedValidationProfile
    (count : Nat) :
    ConstitutiveComplexityProfile :=
  { inputBits :=
      explicitFamilyInputBitSize count
    depth := 0
    maxFrontierWidth := 0
    events :=
      explicitFamilyConstitutedValidationCounts
        count
    representationCharge :=
      explicitFamilyConstitutedValidationRepresentationCharge
        count }

/-- Execution-only profile for the already-produced and validated local schedule. -/
def explicitFamilyConstitutedExecutionProfile
    (count : Nat) :
    ConstitutiveComplexityProfile :=
  { inputBits :=
      explicitFamilyInputBitSize count
    depth := 0
    maxFrontierWidth := 0
    events :=
      explicitFamilyConstitutedExecutionCounts
        count
    representationCharge :=
      explicitFamilyConstitutedExecutionRepresentationCharge
        count }

/--
Total closed profile.

The first phase is the existing local F(n) production/trajectory profile.
Validation and actual execution are appended without recharging provenance or
certificate production.
-/
def explicitFamilyConstitutedTotalProfile
    (count : Nat) :
    ConstitutiveComplexityProfile :=
  ConstitutiveComplexityProfile.compose
    (explicitFamilyConstitutiveProfile count)
    (ConstitutiveComplexityProfile.compose
      (explicitFamilyConstitutedValidationProfile
        count)
      (explicitFamilyConstitutedExecutionProfile
        count))

/-- Polynomial syntax for one complete pass of direct local relation queries. -/
def explicitFamilyConstitutedLocalQueryCostPolynomial :
    CostPolynomial :=
  CostPolynomial.mul
    CostPolynomial.input
    explicitFamilyRelationCostPolynomial

/-- The polynomial evaluates to the already-proved local-query input budget. -/
theorem explicitFamilyConstitutedLocalQueryCostPolynomial_eval
    (inputBits : Nat) :
    explicitFamilyConstitutedLocalQueryCostPolynomial.eval
        inputBits =
      inputBits *
        explicitFamilyRelationPolynomialBudget
          inputBits := by
  change
    inputBits *
        explicitFamilyRelationCostPolynomial.eval inputBits =
      inputBits *
        explicitFamilyRelationPolynomialBudget inputBits
  rw [
    explicitFamilyRelationCostPolynomial_eval
  ]

/-- Validation profile is input-polynomial in the concrete input size. -/
theorem explicitFamilyConstitutedValidationProfile_inputPolynomiallyBounded :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      explicitFamilyConstitutedValidationProfile :=
  { depth :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        0
    width :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        0
    syntaxUnits :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        0
    frontierSlots :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        0
    provenance :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        0
    certificates :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        0
    relationFind :=
      ⟨CostPolynomial.input,
        fun count => by
          change
            (explicitFamilyConstitutedValidationCounts
              count).relationFindCalls ≤
              explicitFamilyInputBitSize count
          rw [
            explicitFamilyConstitutedValidationCounts_relationFindCalls
          ]
          exact
            explicitFamilyIndex_le_inputBitSize
              count⟩
    closurePrimitive :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        0
    closureCandidates :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        0
    terminal :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        0
    representationCharge :=
      ⟨explicitFamilyConstitutedLocalQueryCostPolynomial,
        fun count => by
          change
            explicitFamilyConstitutedValidationRepresentationCharge
                count ≤
              explicitFamilyConstitutedLocalQueryCostPolynomial.eval
                (explicitFamilyInputBitSize count)
          rw [
            explicitFamilyConstitutedLocalQueryCostPolynomial_eval
          ]
          exact
            explicitFamilyConstitutedValidationRepresentationCharge_le_inputBudget
              count⟩ }

/-- Actual local-execution profile is input-polynomial in concrete input size. -/
theorem explicitFamilyConstitutedExecutionProfile_inputPolynomiallyBounded :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      explicitFamilyConstitutedExecutionProfile :=
  { depth :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        0
    width :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        0
    syntaxUnits :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        0
    frontierSlots :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        0
    provenance :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        0
    certificates :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        0
    relationFind :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        0
    closurePrimitive :=
      ⟨CostPolynomial.input,
        fun count => by
          change
            (explicitFamilyConstitutedExecutionCounts
              count).closurePrimitiveQueries ≤
              explicitFamilyInputBitSize count
          rw [
            explicitFamilyConstitutedExecutionCounts_primitiveQueries
          ]
          exact
            explicitFamilyIndex_le_inputBitSize
              count⟩
    closureCandidates :=
      ⟨CostPolynomial.constant 0,
        fun count => by
          change
            (explicitFamilyConstitutedExecutionCounts
              count).closureCompositionCandidates ≤
              0
          rw [
            explicitFamilyConstitutedExecutionCounts_compositionCandidates
          ]⟩
    terminal :=
      InputPolynomiallyBounded.constant
        explicitFamilyInputBitSize
        0
    representationCharge :=
      ⟨explicitFamilyConstitutedLocalQueryCostPolynomial,
        fun count => by
          change
            explicitFamilyConstitutedExecutionRepresentationCharge
                count ≤
              explicitFamilyConstitutedLocalQueryCostPolynomial.eval
                (explicitFamilyInputBitSize count)
          rw [
            explicitFamilyConstitutedLocalQueryCostPolynomial_eval
          ]
          exact
            explicitFamilyConstitutedExecutionRepresentationCharge_le_inputBudget
              count⟩ }

/-- The complete production+validation+execution profile is input-polynomial. -/
theorem explicitFamilyConstitutedTotalProfile_inputPolynomiallyBounded :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      explicitFamilyConstitutedTotalProfile := by
  exact
    ConstitutiveProfileFamilyInputPolynomiallyBounded.compose
      explicitFamilyConstitutiveProfile_inputPolynomiallyBounded
      (ConstitutiveProfileFamilyInputPolynomiallyBounded.compose
        explicitFamilyConstitutedValidationProfile_inputPolynomiallyBounded
        explicitFamilyConstitutedExecutionProfile_inputPolynomiallyBounded)

/-- Provenance is charged exactly once, in production. -/
theorem explicitFamilyConstitutedTotalProfile_provenance
    (count : Nat) :
    (explicitFamilyConstitutedTotalProfile
      count).events.provenanceUnits =
      count := by
  rfl

/-- Transport certificate atoms are charged exactly once, in production. -/
theorem explicitFamilyConstitutedTotalProfile_certificates
    (count : Nat) :
    (explicitFamilyConstitutedTotalProfile
      count).events.certificateAtoms =
      count := by
  rfl

/-- Existing trajectory relation-find work plus executable validation is recorded exactly. -/
theorem explicitFamilyConstitutedTotalProfile_relationFind
    (count : Nat) :
    (explicitFamilyConstitutedTotalProfile
      count).events.relationFindCalls =
      3 * count := by
  simp only [
    explicitFamilyConstitutedTotalProfile,
    ConstitutiveComplexityProfile.compose,
    ComplexityCounts.add,
    explicitFamilyConstitutiveProfile,
    explicitFamilyComplexityCounts,
    explicitFamilyConstitutedValidationProfile,
    explicitFamilyConstitutedValidationCounts,
    explicitFamilyConstitutedExecutionProfile,
    explicitFamilyConstitutedExecutionCounts,
    explicitFamilyConstitutedLocalValidationQueries
  ]
  omega

/-- Actual local execution contributes exactly n primitive closure queries. -/
theorem explicitFamilyConstitutedTotalProfile_closurePrimitive
    (count : Nat) :
    (explicitFamilyConstitutedTotalProfile
      count).events.closurePrimitiveQueries =
      count := by
  simp only [
    explicitFamilyConstitutedTotalProfile,
    ConstitutiveComplexityProfile.compose,
    ComplexityCounts.add,
    explicitFamilyConstitutiveProfile,
    explicitFamilyComplexityCounts,
    explicitFamilyConstitutedValidationProfile,
    explicitFamilyConstitutedValidationCounts,
    explicitFamilyConstitutedExecutionProfile,
    explicitFamilyConstitutedExecutionCounts,
    explicitFamilyConstitutedLocalExecutionQueries
  ]

/-- No actual local execution phase inspects a composition candidate. -/
theorem explicitFamilyConstitutedTotalProfile_closureCandidates
    (count : Nat) :
    (explicitFamilyConstitutedTotalProfile
      count).events.closureCompositionCandidates =
      0 := by
  simp only [
    explicitFamilyConstitutedTotalProfile,
    ConstitutiveComplexityProfile.compose,
    ComplexityCounts.add,
    explicitFamilyConstitutiveProfile,
    explicitFamilyComplexityCounts,
    explicitFamilyConstitutedValidationProfile,
    explicitFamilyConstitutedValidationCounts,
    explicitFamilyConstitutedExecutionProfile,
    explicitFamilyConstitutedExecutionCounts,
    explicitFamilyConstitutedLocalExecutionCompositionCandidates
  ]

/--
The total representation charge is the sum of the three distinct accounting
phases; production data themselves are not duplicated.
-/
theorem explicitFamilyConstitutedTotalProfile_representationCharge
    (count : Nat) :
    (explicitFamilyConstitutedTotalProfile
      count).representationCharge =
      explicitFamilyRepresentationChargedCost count +
        (explicitFamilyConstitutedValidationRepresentationCharge count +
          explicitFamilyConstitutedExecutionRepresentationCharge count) := by
  rfl

/--
One closed evidence package for the quantitative constitutive program on F(n).
-/
structure ExplicitFamilyQuantitativeSynthesis
    (count : Nat) : Prop where
  accounting :
    ExplicitFamilyConstitutedLocalAccountingEvidence
      count
  provenanceChargedOnce :
    (explicitFamilyConstitutedTotalProfile
      count).events.provenanceUnits =
      count
  certificatesChargedOnce :
    (explicitFamilyConstitutedTotalProfile
      count).events.certificateAtoms =
      count
  validationFindExact :
    (explicitFamilyConstitutedValidationCounts
      count).relationFindCalls =
      count
  executionPrimitiveExact :
    (explicitFamilyConstitutedExecutionCounts
      count).closurePrimitiveQueries =
      count
  executionCompositionExact :
    (explicitFamilyConstitutedExecutionCounts
      count).closureCompositionCandidates =
      0

/-- Quantitative synthesis is realized for every explicit family member. -/
theorem explicitFamilyQuantitativeSynthesis
    (count : Nat) :
    ExplicitFamilyQuantitativeSynthesis
      count :=
  { accounting :=
      explicitFamilyConstitutedLocalAccountingEvidence
        count
    provenanceChargedOnce :=
      explicitFamilyConstitutedTotalProfile_provenance
        count
    certificatesChargedOnce :=
      explicitFamilyConstitutedTotalProfile_certificates
        count
    validationFindExact :=
      explicitFamilyConstitutedValidationCounts_relationFindCalls
        count
    executionPrimitiveExact :=
      explicitFamilyConstitutedExecutionCounts_primitiveQueries
        count
    executionCompositionExact :=
      explicitFamilyConstitutedExecutionCounts_compositionCandidates
        count }

/-- Family-level closure of the quantitative synthesis obligation. -/
structure ExplicitFamilyQuantitativeProgramClosed : Prop where
  perInput :
    ∀ count : Nat,
      ExplicitFamilyQuantitativeSynthesis
        count
  totalProfileInputPolynomial :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      explicitFamilyConstitutedTotalProfile

/-- The complete announced quantitative program is closed on F(n). -/
theorem explicitFamilyQuantitativeProgramClosed :
    ExplicitFamilyQuantitativeProgramClosed :=
  { perInput :=
      explicitFamilyQuantitativeSynthesis
    totalProfileInputPolynomial :=
      explicitFamilyConstitutedTotalProfile_inputPolynomiallyBounded }

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedValidationProfile
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedExecutionProfile
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedTotalProfile
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalQueryCostPolynomial
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedLocalQueryCostPolynomial_eval
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedValidationProfile_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedExecutionProfile_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedTotalProfile_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedTotalProfile_provenance
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedTotalProfile_certificates
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedTotalProfile_relationFind
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedTotalProfile_closurePrimitive
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedTotalProfile_closureCandidates
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedTotalProfile_representationCharge
#print axioms ConstitutiveSearch.SAT.ExplicitFamilyQuantitativeSynthesis
#print axioms ConstitutiveSearch.SAT.explicitFamilyQuantitativeSynthesis
#print axioms ConstitutiveSearch.SAT.ExplicitFamilyQuantitativeProgramClosed
#print axioms ConstitutiveSearch.SAT.explicitFamilyQuantitativeProgramClosed
/- AXIOM_AUDIT_END -/
