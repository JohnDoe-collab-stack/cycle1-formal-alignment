import ConstitutiveSearch.AcceptedFrontierNormalizationCosts
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
  rw [← isolatedFrontier_length count]
  exact generic

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
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorDepth
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorHistoryBinaryBudget
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorStateBinaryBudget
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorRelationEqualityBudget
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorEnvelopeCounts
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorRepresentationAtomicCosts
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorEnvelopeProfile
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorEnvelopeProfile_width
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorEnvelopeProfile_depth_succ
#print axioms ConstitutiveSearch.SAT.isolatedSeparatorEnvelopeProfile_representationConsistent
#print axioms ConstitutiveSearch.SAT.isolatedSeparator_normalizationFindCalls_le_profile
#print axioms ConstitutiveSearch.SAT.isolatedSeparator3_not_boundedBy_compositionPhase3
#print axioms ConstitutiveSearch.SAT.compositionPhase3_not_boundedBy_isolatedSeparator3
/- AXIOM_AUDIT_END -/
