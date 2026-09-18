import ConstitutiveSearch.AcceptedFrontierNormalizationCosts
import ConstitutiveSearch.MachineCostPolynomial
import ConstitutiveSearch.SAT.ExplicitFamilyConstitutiveProfile
import ConstitutiveSearch.SAT.WidthSeparators

/-!
# Constitutive profile envelope for the SAT width separator

The width separator is a benchmark frontier, not an intrinsic SAT-hardness
claim.  Its root CNF is empty, so using only root-formula size would hide the
actual benchmark payload.  This module therefore indexes the profile by an
explicit serialization of the entire isolated frontier.

The event vector is an envelope for running the generic normalizer under one
fixed flip engine:
* exact frontier width/count;
* one provenance unit per isolated child;
* generic quadratic directed-find envelope 2 * width^2.

No closure search is charged.  Representation charge is induced from an
explicit atomic-cost assignment.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Concrete representation size of one isolated generated state. -/
def isolatedChildBinarySize
    (var : Var) : Nat :=
  Cnf.binarySize
      (isolatedChild var).context.formula +
    StructuralDecisionHistory.binarySize
      (isolatedChild var).context.decisions

/-- Prefix-tag serialization size of the complete separator frontier. -/
def isolatedFrontierInputBitSize : Nat → Nat
  | 0 =>
      1
  | count + 1 =>
      Nat.succ
        (isolatedChildBinarySize count +
          isolatedFrontierInputBitSize count)

/-- The family index is bounded by the serialized separator input itself. -/
theorem isolatedSeparatorIndex_le_inputBitSize :
    ∀ count : Nat,
      count ≤
        isolatedFrontierInputBitSize count
  | 0 =>
      Nat.zero_le 1
  | count + 1 => by
      change
        Nat.succ count ≤
          Nat.succ
            (isolatedChildBinarySize count +
              isolatedFrontierInputBitSize count)
      exact
        Nat.succ_le_succ
          (Nat.le_trans
            (isolatedSeparatorIndex_le_inputBitSize count)
            (Nat.le_add_left
              (isolatedFrontierInputBitSize count)
              (isolatedChildBinarySize count)))

/-- Maximum structural depth of the separator frontier. -/
def isolatedSeparatorDepth : Nat → Nat
  | 0 => 0
  | _ + 1 => 1

/-- Uniform one-decision history budget for separator variables below count. -/
def isolatedSeparatorHistoryBinaryBudget
    (count : Nat) : Nat :=
  StructuralDecisionHistory.binaryBudget
    count
    1

/-- Uniform generated-state representation envelope for the separator. -/
def isolatedSeparatorStateBinaryBudget
    (count : Nat) : Nat :=
  1 +
    isolatedSeparatorHistoryBinaryBudget count

/-- Uniform representation charge of one fixed-flip equality query. -/
def isolatedSeparatorRelationEqualityBudget
    (count : Nat) : Nat :=
  uniformGeneratedFlipEqualityCharge
    1
    (isolatedSeparatorHistoryBinaryBudget count)

/-- Exact cost polynomial for one separator history envelope. -/
def isolatedSeparatorHistoryCostPolynomial :
    CostPolynomial :=
  .add
    (.mul
      (.constant 1)
      (.add
        .input
        (.constant 3)))
    (.constant 1)

/-- Exact cost polynomial for one separator state envelope. -/
def isolatedSeparatorStateCostPolynomial :
    CostPolynomial :=
  .add
    (.constant 1)
    isolatedSeparatorHistoryCostPolynomial

/-- Exact cost polynomial for one separator fixed-flip equality envelope. -/
def isolatedSeparatorRelationCostPolynomial :
    CostPolynomial :=
  .add
    (.add
      (.constant 1)
      (.constant 1))
    (.add
      isolatedSeparatorHistoryCostPolynomial
      isolatedSeparatorHistoryCostPolynomial)

/-- Exact cost polynomial for the generic quadratic directed-find envelope. -/
def isolatedSeparatorFindCountCostPolynomial :
    CostPolynomial :=
  .mul
    (.constant 2)
    (.mul
      .input
      .input)

theorem isolatedSeparatorHistoryCostPolynomial_eval
    (count : Nat) :
    isolatedSeparatorHistoryCostPolynomial.eval count =
      isolatedSeparatorHistoryBinaryBudget count := by
  unfold isolatedSeparatorHistoryCostPolynomial
  unfold isolatedSeparatorHistoryBinaryBudget
  rw [
    StructuralDecisionHistory.binaryBudget_closed
      count
      1
  ]
  rfl

theorem isolatedSeparatorStateCostPolynomial_eval
    (count : Nat) :
    isolatedSeparatorStateCostPolynomial.eval count =
      isolatedSeparatorStateBinaryBudget count := by
  change
    1 +
        isolatedSeparatorHistoryCostPolynomial.eval count =
      1 +
        isolatedSeparatorHistoryBinaryBudget count
  rw [
    isolatedSeparatorHistoryCostPolynomial_eval
  ]

theorem isolatedSeparatorRelationCostPolynomial_eval
    (count : Nat) :
    isolatedSeparatorRelationCostPolynomial.eval count =
      isolatedSeparatorRelationEqualityBudget count := by
  change
    1 + 1 +
          (isolatedSeparatorHistoryCostPolynomial.eval count +
            isolatedSeparatorHistoryCostPolynomial.eval count) =
      1 + 1 +
          (isolatedSeparatorHistoryBinaryBudget count +
            isolatedSeparatorHistoryBinaryBudget count)
  rw [
    isolatedSeparatorHistoryCostPolynomial_eval
  ]

theorem isolatedSeparatorFindCountCostPolynomial_eval
    (count : Nat) :
    isolatedSeparatorFindCountCostPolynomial.eval count =
      normalizationFindCallQuadraticBudget count := by
  unfold isolatedSeparatorFindCountCostPolynomial
  unfold normalizationFindCallQuadraticBudget
  unfold normalizationPairClassificationQuadraticBudget
  rfl

/-- Event envelope for generic normalization of the isolated frontier. -/
def isolatedSeparatorEnvelopeCounts
    (count : Nat) : ComplexityCounts :=
  { syntaxUnits := 0
    frontierSlots := count
    provenanceUnits := count
    certificateAtoms := 0
    relationFindCalls :=
      normalizationFindCallQuadraticBudget count
    closurePrimitiveQueries := 0
    closureCompositionCandidates := 0
    terminalChecks := 0 }

/-- Representation-level atomic charges for the separator envelope. -/
def isolatedSeparatorRepresentationAtomicCosts
    (count : Nat) : AtomicCosts :=
  { syntaxUnit := 1
    frontierSlot :=
      isolatedSeparatorStateBinaryBudget count
    provenanceUnit :=
      isolatedSeparatorHistoryBinaryBudget count
    certificateAtom := 0
    relationFindCall :=
      isolatedSeparatorRelationEqualityBudget count
    closurePrimitiveQuery := 0
    closureCompositionCandidate := 0
    terminalCheck := 0 }

/-- Multidimensional envelope profile of the isolated width benchmark. -/
def isolatedSeparatorEnvelopeProfile
    (count : Nat) :
    ConstitutiveComplexityProfile :=
  { inputBits :=
      isolatedFrontierInputBitSize count
    depth :=
      isolatedSeparatorDepth count
    maxFrontierWidth :=
      count
    events :=
      isolatedSeparatorEnvelopeCounts count
    representationCharge :=
      chargedCost
        (isolatedSeparatorEnvelopeCounts count)
        (isolatedSeparatorRepresentationAtomicCosts count) }

/-- The separator envelope has exactly the requested width coordinate. -/
theorem isolatedSeparatorEnvelopeProfile_width
    (count : Nat) :
    (isolatedSeparatorEnvelopeProfile count).maxFrontierWidth =
      count := by
  rfl

/-- Every nonempty separator envelope has structural depth one. -/
theorem isolatedSeparatorEnvelopeProfile_depth_succ
    (count : Nat) :
    (isolatedSeparatorEnvelopeProfile
      (count + 1)).depth = 1 := by
  rfl

/-- Its representation charge is definitionally consistent with the declared costs. -/
theorem isolatedSeparatorEnvelopeProfile_representationConsistent
    (count : Nat) :
    RepresentationConsistent
      (isolatedSeparatorEnvelopeProfile count)
      (isolatedSeparatorRepresentationAtomicCosts count) := by
  rfl

/--
Lift any polynomial envelope in the separator index to the concrete serialized
frontier input size.
-/
theorem isolatedSeparatorInputPolynomialBounded_of_indexEnvelope
    {cost : Nat → Nat}
    (envelope : CostPolynomial)
    (costLe :
      ∀ count : Nat,
        cost count ≤
          envelope.eval count) :
    InputPolynomiallyBounded
      isolatedFrontierInputBitSize
      cost :=
  ⟨envelope,
    fun count =>
      Nat.le_trans
        (costLe count)
        (envelope.eval_mono
          (isolatedSeparatorIndex_le_inputBitSize
            count))⟩

/-- Every source-level event coordinate of the separator envelope is input-polynomial. -/
theorem isolatedSeparatorEnvelopeCounts_inputPolynomiallyBounded :
    ComplexityCountsFamilyInputPolynomiallyBounded
      isolatedFrontierInputBitSize
      isolatedSeparatorEnvelopeCounts :=
  { syntaxUnits := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          (fun _count => 0)
      exact
        InputPolynomiallyBounded.constant
          isolatedFrontierInputBitSize
          0
    frontierSlots := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          (fun count => count)
      exact
        ⟨CostPolynomial.input,
          isolatedSeparatorIndex_le_inputBitSize⟩
    provenanceUnits := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          (fun count => count)
      exact
        ⟨CostPolynomial.input,
          isolatedSeparatorIndex_le_inputBitSize⟩
    certificateAtoms := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          (fun _count => 0)
      exact
        InputPolynomiallyBounded.constant
          isolatedFrontierInputBitSize
          0
    relationFindCalls := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          normalizationFindCallQuadraticBudget
      exact
        isolatedSeparatorInputPolynomialBounded_of_indexEnvelope
          isolatedSeparatorFindCountCostPolynomial
          (fun count =>
            Nat.le_of_eq
              (isolatedSeparatorFindCountCostPolynomial_eval
                count).symm)
    closurePrimitiveQueries := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          (fun _count => 0)
      exact
        InputPolynomiallyBounded.constant
          isolatedFrontierInputBitSize
          0
    closureCompositionCandidates := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          (fun _count => 0)
      exact
        InputPolynomiallyBounded.constant
          isolatedFrontierInputBitSize
          0
    terminalChecks := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          (fun _count => 0)
      exact
        InputPolynomiallyBounded.constant
          isolatedFrontierInputBitSize
          0 }

/-- Every representation-level atomic charge of the separator is input-polynomial. -/
theorem isolatedSeparatorRepresentationAtomicCosts_inputPolynomiallyBounded :
    AtomicCostsFamilyInputPolynomiallyBounded
      isolatedFrontierInputBitSize
      isolatedSeparatorRepresentationAtomicCosts :=
  { syntaxUnit :=
      InputPolynomiallyBounded.constant
        isolatedFrontierInputBitSize
        1
    frontierSlot := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          isolatedSeparatorStateBinaryBudget
      exact
        isolatedSeparatorInputPolynomialBounded_of_indexEnvelope
          isolatedSeparatorStateCostPolynomial
          (fun count =>
            Nat.le_of_eq
              (isolatedSeparatorStateCostPolynomial_eval
                count).symm)
    provenanceUnit := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          isolatedSeparatorHistoryBinaryBudget
      exact
        isolatedSeparatorInputPolynomialBounded_of_indexEnvelope
          isolatedSeparatorHistoryCostPolynomial
          (fun count =>
            Nat.le_of_eq
              (isolatedSeparatorHistoryCostPolynomial_eval
                count).symm)
    certificateAtom :=
      InputPolynomiallyBounded.constant
        isolatedFrontierInputBitSize
        0
    relationFindCall := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          isolatedSeparatorRelationEqualityBudget
      exact
        isolatedSeparatorInputPolynomialBounded_of_indexEnvelope
          isolatedSeparatorRelationCostPolynomial
          (fun count =>
            Nat.le_of_eq
              (isolatedSeparatorRelationCostPolynomial_eval
                count).symm)
    closurePrimitiveQuery :=
      InputPolynomiallyBounded.constant
        isolatedFrontierInputBitSize
        0
    closureCompositionCandidate :=
      InputPolynomiallyBounded.constant
        isolatedFrontierInputBitSize
        0
    terminalCheck :=
      InputPolynomiallyBounded.constant
        isolatedFrontierInputBitSize
        0 }

/-- The complete separator representation charge is input-polynomial. -/
theorem isolatedSeparatorRepresentationCharge_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      isolatedFrontierInputBitSize
      (fun count =>
        (isolatedSeparatorEnvelopeProfile count).representationCharge) := by
  change
    InputPolynomiallyBounded
      isolatedFrontierInputBitSize
      (fun count =>
        chargedCost
          (isolatedSeparatorEnvelopeCounts count)
          (isolatedSeparatorRepresentationAtomicCosts count))
  exact
    chargedCost_inputPolynomiallyBounded
      isolatedSeparatorEnvelopeCounts_inputPolynomiallyBounded
      isolatedSeparatorRepresentationAtomicCosts_inputPolynomiallyBounded

/--
The width-separator family is polynomially bounded in every constitutive
coordinate relative to the concrete serialization of its full frontier.
-/
theorem isolatedSeparatorEnvelopeProfile_inputPolynomiallyBounded :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      isolatedSeparatorEnvelopeProfile :=
  { depth := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          isolatedSeparatorDepth
      refine
        ⟨CostPolynomial.constant 1, ?_⟩
      intro count
      cases count with
      | zero =>
          exact Nat.zero_le 1
      | succ count =>
          exact Nat.le_refl 1
    width := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          (fun count => count)
      exact
        ⟨CostPolynomial.input,
          isolatedSeparatorIndex_le_inputBitSize⟩
    syntaxUnits := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          (fun count =>
            (isolatedSeparatorEnvelopeCounts count).syntaxUnits)
      exact
        isolatedSeparatorEnvelopeCounts_inputPolynomiallyBounded.syntaxUnits
    frontierSlots := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          (fun count =>
            (isolatedSeparatorEnvelopeCounts count).frontierSlots)
      exact
        isolatedSeparatorEnvelopeCounts_inputPolynomiallyBounded.frontierSlots
    provenance := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          (fun count =>
            (isolatedSeparatorEnvelopeCounts count).provenanceUnits)
      exact
        isolatedSeparatorEnvelopeCounts_inputPolynomiallyBounded.provenanceUnits
    certificates := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          (fun count =>
            (isolatedSeparatorEnvelopeCounts count).certificateAtoms)
      exact
        isolatedSeparatorEnvelopeCounts_inputPolynomiallyBounded.certificateAtoms
    relationFind := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          (fun count =>
            (isolatedSeparatorEnvelopeCounts count).relationFindCalls)
      exact
        isolatedSeparatorEnvelopeCounts_inputPolynomiallyBounded.relationFindCalls
    closurePrimitive := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          (fun count =>
            (isolatedSeparatorEnvelopeCounts count).closurePrimitiveQueries)
      exact
        isolatedSeparatorEnvelopeCounts_inputPolynomiallyBounded.closurePrimitiveQueries
    closureCandidates := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          (fun count =>
            (isolatedSeparatorEnvelopeCounts count).closureCompositionCandidates)
      exact
        isolatedSeparatorEnvelopeCounts_inputPolynomiallyBounded.closureCompositionCandidates
    terminal := by
      change
        InputPolynomiallyBounded
          isolatedFrontierInputBitSize
          (fun count =>
            (isolatedSeparatorEnvelopeCounts count).terminalChecks)
      exact
        isolatedSeparatorEnvelopeCounts_inputPolynomiallyBounded.terminalChecks
    representationCharge :=
      isolatedSeparatorRepresentationCharge_inputPolynomiallyBounded }

/--
The actual generic normalizer directed-find count on the isolated frontier is
covered by the profile relationFindCalls coordinate.
-/
theorem isolatedSeparator_normalizationFindCalls_le_profile
    (anchor count : Nat) :
    normalizationFindCallCount
        (generatedStructuralFlipAtSearch
          ([] : Cnf)
          anchor)
        (generatedStructuralFlipAtAction
          ([] : Cnf)
          anchor)
        (isolatedFrontier count) ≤
      (isolatedSeparatorEnvelopeProfile count).events.relationFindCalls := by
  have generic :=
    normalizationFindCallCount_le_quadratic
      (generatedStructuralFlipAtSearch
        ([] : Cnf)
        anchor)
      (generatedStructuralFlipAtAction
        ([] : Cnf)
        anchor)
      (isolatedFrontier count)
  change
    normalizationFindCallCount
        (generatedStructuralFlipAtSearch
          ([] : Cnf)
          anchor)
        (generatedStructuralFlipAtAction
          ([] : Cnf)
          anchor)
        (isolatedFrontier count) ≤
      normalizationFindCallQuadraticBudget count
  simpa only [isolatedFrontier_length] using generic

/--
At count three, the separator and the two-step composition phase are not
pointwise ordered in the separator-to-composition direction: width already
fails (3 versus 2).
-/
theorem isolatedSeparator3_not_boundedBy_compositionPhase3 :
    ¬
      (isolatedSeparatorEnvelopeProfile 3).BoundedBy
        (composedClosureConstitutivePhaseProfile 3) := by
  intro bounded
  have widthLe := bounded.widthLe
  change 3 ≤ 2 at widthLe
  exact
    (Nat.not_succ_le_self 2)
      widthLe

/--
The converse pointwise ordering also fails: the composition phase has depth two
while the separator frontier has depth one.
-/
theorem compositionPhase3_not_boundedBy_isolatedSeparator3 :
    ¬
      (composedClosureConstitutivePhaseProfile 3).BoundedBy
        (isolatedSeparatorEnvelopeProfile 3) := by
  intro bounded
  have depthLe := bounded.depthLe
  change 2 ≤ 1 at depthLe
  exact
    (Nat.not_succ_le_self 1)
      depthLe

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.isolatedChildBinarySize
#print axioms ConstitutiveSearch.SAT.isolatedFrontierInputBitSize
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorIndex_le_inputBitSize
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorDepth
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorHistoryBinaryBudget
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorStateBinaryBudget
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorRelationEqualityBudget
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorHistoryCostPolynomial
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorStateCostPolynomial
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorRelationCostPolynomial
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorFindCountCostPolynomial
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorHistoryCostPolynomial_eval
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorStateCostPolynomial_eval
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorRelationCostPolynomial_eval
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorFindCountCostPolynomial_eval
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorEnvelopeCounts
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorRepresentationAtomicCosts
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorEnvelopeProfile
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorEnvelopeProfile_width
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorEnvelopeProfile_depth_succ
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorEnvelopeProfile_representationConsistent
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorInputPolynomialBounded_of_indexEnvelope
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorEnvelopeCounts_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorRepresentationAtomicCosts_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorRepresentationCharge_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorEnvelopeProfile_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.isolatedSeparator_normalizationFindCalls_le_profile
#print axioms ConstitutiveSearch.SAT.isolatedSeparator3_not_boundedBy_compositionPhase3
#print axioms ConstitutiveSearch.SAT.compositionPhase3_not_boundedBy_isolatedSeparator3
/- AXIOM_AUDIT_END -/
