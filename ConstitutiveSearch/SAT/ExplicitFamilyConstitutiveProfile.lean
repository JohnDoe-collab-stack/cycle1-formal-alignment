import ConstitutiveSearch.ConstitutiveComplexityProfile
import ConstitutiveSearch.SAT.ExplicitFamilyInputComplexity
import ConstitutiveSearch.SAT.ParametricComposedPolynomialCosts

/-!
# Constitutive complexity profiles for the explicit SAT family

This module instantiates the multidimensional profile on two announced
executions:

1. the local certified trajectory of F(n);
2. that local trajectory followed by the separately accounted two-flip
   composition phase.

The total representation charge is the sum of the two already proved
phase-specific charges.  It is not obtained by pretending both phases use one
identical atomic-cost assignment.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Multidimensional profile of the local F(n) trajectory. -/
def explicitFamilyConstitutiveProfile
    (count : Nat) :
    ConstitutiveComplexityProfile :=
  { inputBits :=
      explicitFamilyInputBitSize count
    depth :=
      count
    maxFrontierWidth :=
      (explicitFamilyResourceTrajectory count).trajectory.widthTrace.foldl
        Nat.max
        0
    events :=
      explicitFamilyComplexityCounts count
    representationCharge :=
      explicitFamilyRepresentationChargedCost count }

/-- The local profile representation charge is induced by its declared costs. -/
theorem explicitFamilyConstitutiveProfile_representationConsistent
    (count : Nat) :
    RepresentationConsistent
      (explicitFamilyConstitutiveProfile count)
      (explicitFamilyRepresentationAtomicCosts count) := by
  rfl

/-- The local profile depth agrees with the certified endpoint depth. -/
theorem explicitFamilyConstitutiveProfile_depth
    (count : Nat) :
    (explicitFamilyConstitutiveProfile count).depth =
      (explicitFamilyResourceTrajectory count).finish.depth := by
  rw [explicitFamilyEndpoint_depth]
  rfl

/-- Every observed width of the local trajectory is bounded by two. -/
theorem explicitFamilyConstitutiveProfile_widthTrace_le_two
    (count width : Nat)
    (member :
      width ∈
        (explicitFamilyResourceTrajectory count).trajectory.widthTrace) :
    width ≤ 2 :=
  explicitFamilyResourceTrajectory_width_le_two
    count
    width
    member

/-- The local representation charge is polynomial in the concrete input size. -/
theorem explicitFamilyConstitutiveProfile_charge_le_inputPolynomial
    (count : Nat) :
    (explicitFamilyConstitutiveProfile count).representationCharge ≤
      explicitFamilyInputIndexedPolynomialBudget count :=
  explicitFamilyRepresentationChargedCost_le_inputIndexedPolynomial
    count

/-- Profile of only the added composition phase. -/
def composedClosureConstitutivePhaseProfile
    (count : Nat) :
    ConstitutiveComplexityProfile :=
  { inputBits :=
      explicitFamilyInputBitSize count
    depth :=
      2
    maxFrontierWidth :=
      2
    events :=
      composedClosurePhaseCounts count
    representationCharge :=
      composedClosurePhaseRepresentationChargedCost count }

/-- The composition phase has the certified source-level event coordinates. -/
theorem composedClosureConstitutivePhaseProfile_events
    (count : Nat) :
    (composedClosureConstitutivePhaseProfile count).events =
      composedClosurePhaseCounts count := by
  rfl

/-- The composition-phase representation charge has an input-indexed polynomial bound. -/
theorem composedClosureConstitutivePhaseProfile_charge_le_inputPolynomial
    (count : Nat) :
    (composedClosureConstitutivePhaseProfile count).representationCharge ≤
      composedClosurePhaseInputIndexedPolynomialBudget count :=
  composedClosurePhaseRepresentationChargedCost_le_inputIndexedPolynomial
    count

/--
Combined profile of F(n) followed by the separately charged composition phase.
-/
def explicitFamilyWithCompositionProfile
    (count : Nat) :
    ConstitutiveComplexityProfile :=
  { inputBits :=
      explicitFamilyInputBitSize count
    depth :=
      count + 2
    maxFrontierWidth :=
      Nat.max
        (explicitFamilyConstitutiveProfile count).maxFrontierWidth
        2
    events :=
      ComplexityCounts.add
        (explicitFamilyComplexityCounts count)
        (composedClosurePhaseCounts count)
    representationCharge :=
      explicitFamilyRepresentationChargedCost count +
        composedClosurePhaseRepresentationChargedCost count }

/-- Input-indexed polynomial budget for the combined representation charge. -/
def explicitFamilyWithCompositionInputPolynomialBudget
    (count : Nat) : Nat :=
  explicitFamilyInputIndexedPolynomialBudget count +
    composedClosurePhaseInputIndexedPolynomialBudget count

/-- The complete local-plus-composed representation charge remains polynomially bounded. -/
theorem explicitFamilyWithCompositionProfile_charge_le_inputPolynomial
    (count : Nat) :
    (explicitFamilyWithCompositionProfile count).representationCharge ≤
      explicitFamilyWithCompositionInputPolynomialBudget count := by
  exact
    Nat.add_le_add
      (explicitFamilyRepresentationChargedCost_le_inputIndexedPolynomial
        count)
      (composedClosurePhaseRepresentationChargedCost_le_inputIndexedPolynomial
        count)

/-- The total profile records exactly two additional certificate atoms. -/
theorem explicitFamilyWithCompositionProfile_certificateAtoms
    (count : Nat) :
    (explicitFamilyWithCompositionProfile count).events.certificateAtoms =
      count + 2 := by
  change
    count + 2 = count + 2
  rfl

/-- The total profile records the three closure primitive queries of the added phase. -/
theorem explicitFamilyWithCompositionProfile_closurePrimitiveQueries
    (count : Nat) :
    (explicitFamilyWithCompositionProfile count).events.closurePrimitiveQueries =
      3 := by
  rfl

/-- The total profile records one composition candidate. -/
theorem explicitFamilyWithCompositionProfile_closureCompositionCandidates
    (count : Nat) :
    (explicitFamilyWithCompositionProfile count).events.closureCompositionCandidates =
      1 := by
  rfl

/-- Direct relation-find calls remain the 2n calls of the local trajectory. -/
theorem explicitFamilyWithCompositionProfile_relationFindCalls
    (count : Nat) :
    (explicitFamilyWithCompositionProfile count).events.relationFindCalls =
      2 * count := by
  rw [show
    (explicitFamilyWithCompositionProfile count).events.relationFindCalls =
      2 * count + 0 from rfl]
  rw [Nat.add_zero]

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutiveProfile
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutiveProfile_representationConsistent
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutiveProfile_depth
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutiveProfile_widthTrace_le_two
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutiveProfile_charge_le_inputPolynomial
#print axioms ConstitutiveSearch.SAT.composedClosureConstitutivePhaseProfile
#print axioms ConstitutiveSearch.SAT.composedClosureConstitutivePhaseProfile_events
#print axioms ConstitutiveSearch.SAT.composedClosureConstitutivePhaseProfile_charge_le_inputPolynomial
#print axioms ConstitutiveSearch.SAT.explicitFamilyWithCompositionProfile
#print axioms ConstitutiveSearch.SAT.explicitFamilyWithCompositionInputPolynomialBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyWithCompositionProfile_charge_le_inputPolynomial
#print axioms ConstitutiveSearch.SAT.explicitFamilyWithCompositionProfile_certificateAtoms
#print axioms ConstitutiveSearch.SAT.explicitFamilyWithCompositionProfile_closurePrimitiveQueries
#print axioms ConstitutiveSearch.SAT.explicitFamilyWithCompositionProfile_closureCompositionCandidates
#print axioms ConstitutiveSearch.SAT.explicitFamilyWithCompositionProfile_relationFindCalls
/- AXIOM_AUDIT_END -/
