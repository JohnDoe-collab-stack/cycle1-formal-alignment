import ConstitutiveSearch.SAT.TrajectoryConstitutedLocalAccounting
import ConstitutiveSearch.SAT.ExplicitFamilyInputPolynomialProfile
import ConstitutiveSearch.SAT.ExplicitFamilyCostPolynomials

/-!
# Quantitative synthesis of the closed constituted SAT trajectory

This module closes the quantitative chain for the explicit family F(n):

  constituted trajectory
  -> endogenous local schedule
  -> pure production charged from structural trajectory coordinates
  -> executable validation
  -> actual candidate-free local execution
  -> one total constitutive complexity profile
  -> input-polynomial bounds.

Production, validation and execution remain distinct phases.

Production reuses the already-certified structural coordinates for syntax,
frontier slots, provenance, certificate atoms and terminality, but deliberately
sets relation-search and closure counters to zero.  The older 2n
normalizationFindCallCount belongs to a different normalization execution and
is not folded into production.

Validation and execution set certificateAtoms and provenanceUnits to zero.
They add only the counters they actually execute and their corresponding
representation charges.

No recursive ClosureSearch upper envelope is substituted for executed counters.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Pure production counts for the constituted trajectory and its local schedule. -/
def explicitFamilyConstitutedProductionCounts
    (count : Nat) :
    ComplexityCounts :=
  { syntaxUnits := 4 * count
    frontierSlots := 3 * count + 1
    provenanceUnits := count
    certificateAtoms := count
    relationFindCalls := 0
    closurePrimitiveQueries := 0
    closureCompositionCandidates := 0
    terminalChecks := 1 }

/--
Representation charge of pure production under the already-audited atomic
representation model.
-/
def explicitFamilyConstitutedProductionRepresentationCharge
    (count : Nat) :
    Nat :=
  chargedCost
    (explicitFamilyConstitutedProductionCounts
      count)
    (explicitFamilyRepresentationAtomicCosts
      count)

/--
Pure production is bounded by the older complete local-strategy charge because
that older profile adds the nonnegative 2n normalization relation-find calls.
-/
theorem explicitFamilyConstitutedProductionRepresentationCharge_le_existing
    (count : Nat) :
    explicitFamilyConstitutedProductionRepresentationCharge
        count ≤
      explicitFamilyRepresentationChargedCost
        count := by
  unfold explicitFamilyConstitutedProductionRepresentationCharge
  unfold explicitFamilyRepresentationChargedCost
  unfold explicitFamilyChargedCost
  unfold chargedCost
  unfold explicitFamilyConstitutedProductionCounts
  unfold explicitFamilyComplexityCounts
  unfold explicitFamilyRepresentationAtomicCosts
  simp

/-- Production-only constitutive profile. -/
def explicitFamilyConstitutedProductionProfile
    (count : Nat) :
    ConstitutiveComplexityProfile :=
  { inputBits :=
      explicitFamilyInputBitSize count
    depth :=
      count
    maxFrontierWidth :=
      (explicitFamilyResourceTrajectory
        count).trajectory.widthTrace.foldl
          Nat.max
          0
    events :=
      explicitFamilyConstitutedProductionCounts
        count
    representationCharge :=
      explicitFamilyConstitutedProductionRepresentationCharge
        count }

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

The first phase is the pure production profile above.  Validation and actual
execution are appended without recharging provenance or certificate production
and without importing the older bidirectional normalization search.
-/
def explicitFamilyConstitutedTotalProfile
    (count : Nat) :
    ConstitutiveComplexityProfile :=
  ConstitutiveComplexityProfile.compose
    (explicitFamilyConstitutedProductionProfile count)
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

/-- Pure production profile is input-polynomial in concrete input size. -/
theorem explicitFamilyConstitutedProductionProfile_inputPolynomiallyBounded :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      explicitFamilyConstitutedProductionProfile := by
  let base :=
    explicitFamilyConstitutiveProfile_inputPolynomiallyBounded
  rcases base.representationCharge with
    ⟨envelope, baseChargeLe⟩
  exact
    { depth := by
        simpa [
          explicitFamilyConstitutedProductionProfile,
          explicitFamilyConstitutiveProfile
        ] using
          base.depth
      width := by
        simpa [
          explicitFamilyConstitutedProductionProfile,
          explicitFamilyConstitutiveProfile
        ] using
          base.width
      syntaxUnits := by
        simpa [
          explicitFamilyConstitutedProductionProfile,
          explicitFamilyConstitutedProductionCounts,
          explicitFamilyConstitutiveProfile,
          explicitFamilyComplexityCounts
        ] using
          base.syntaxUnits
      frontierSlots := by
        simpa [
          explicitFamilyConstitutedProductionProfile,
          explicitFamilyConstitutedProductionCounts,
          explicitFamilyConstitutiveProfile,
          explicitFamilyComplexityCounts
        ] using
          base.frontierSlots
      provenance := by
        simpa [
          explicitFamilyConstitutedProductionProfile,
          explicitFamilyConstitutedProductionCounts,
          explicitFamilyConstitutiveProfile,
          explicitFamilyComplexityCounts
        ] using
          base.provenance
      certificates := by
        simpa [
          explicitFamilyConstitutedProductionProfile,
          explicitFamilyConstitutedProductionCounts,
          explicitFamilyConstitutiveProfile,
          explicitFamilyComplexityCounts
        ] using
          base.certificates
      relationFind :=
        InputPolynomiallyBounded.constant
          explicitFamilyInputBitSize
          0
      closurePrimitive :=
        InputPolynomiallyBounded.constant
          explicitFamilyInputBitSize
          0
      closureCandidates :=
        InputPolynomiallyBounded.constant
          explicitFamilyInputBitSize
          0
      terminal := by
        simpa [
          explicitFamilyConstitutedProductionProfile,
          explicitFamilyConstitutedProductionCounts,
          explicitFamilyConstitutiveProfile,
          explicitFamilyComplexityCounts
        ] using
          base.terminal
      representationCharge :=
        ⟨envelope,
          fun count =>
            Nat.le_trans
              (explicitFamilyConstitutedProductionRepresentationCharge_le_existing
                count)
              (baseChargeLe count)⟩ }

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
          ]
          exact Nat.le_refl 0⟩
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
      explicitFamilyConstitutedProductionProfile_inputPolynomiallyBounded
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

/-- Executable validation is the only relation-find phase in the closed profile. -/
theorem explicitFamilyConstitutedTotalProfile_relationFind
    (count : Nat) :
    (explicitFamilyConstitutedTotalProfile
      count).events.relationFindCalls =
      count := by
  simp only [
    explicitFamilyConstitutedTotalProfile,
    ConstitutiveComplexityProfile.compose,
    ComplexityCounts.add,
    explicitFamilyConstitutedProductionProfile,
    explicitFamilyConstitutedProductionCounts,
    explicitFamilyConstitutedValidationProfile,
    explicitFamilyConstitutedValidationCounts,
    explicitFamilyConstitutedExecutionProfile,
    explicitFamilyConstitutedExecutionCounts,
    explicitFamilyConstitutedLocalValidationQueries
  ]
  simp

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
    explicitFamilyConstitutedProductionProfile,
    explicitFamilyConstitutedProductionCounts,
    explicitFamilyConstitutedValidationProfile,
    explicitFamilyConstitutedValidationCounts,
    explicitFamilyConstitutedExecutionProfile,
    explicitFamilyConstitutedExecutionCounts,
    explicitFamilyConstitutedLocalExecutionQueries
  ]
  simp

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
    explicitFamilyConstitutedProductionProfile,
    explicitFamilyConstitutedProductionCounts,
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
      explicitFamilyConstitutedProductionRepresentationCharge count +
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
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedProductionCounts
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedProductionRepresentationCharge
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedProductionRepresentationCharge_le_existing
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedProductionProfile
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutedProductionProfile_inputPolynomiallyBounded
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
