import ConstitutiveSearch.ComplexityInterface
import ConstitutiveSearch.SAT.ParametricComposedWidth

/-!
# Complexity profile for the parametric SAT composition phase

The construction of F(n) already has its own complete local event profile.
This module records only the additional composition phase above its certified
endpoint.

The phase begins with the direct two-state frontier and charges:
* two frontier-state slots;
* two primitive atoms in the explicit composed certificate;
* three primitive queries made by the successful bounded closure run;
* one tested composition candidate.

No extra syntax, provenance generation, direct relation-find calls, or terminal
checks are charged here.  Representation costs for the already-constituted
states are attached later through AtomicCosts.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Source-level event profile of the added composition phase. -/
def composedClosurePhaseCounts
    (_count : Nat) : ComplexityCounts :=
  { syntaxUnits := 0
    frontierSlots := 2
    provenanceUnits := 0
    certificateAtoms := 2
    relationFindCalls := 0
    closurePrimitiveQueries := 3
    closureCompositionCandidates := 1
    terminalChecks := 0 }

/-- Evidence tying the composition-phase counts to the certified SAT objects. -/
structure ComposedClosurePhaseEvidence
    (count : Nat) : Prop where
  frontierExact :
    (composedDirectFrontier count).length =
      (composedClosurePhaseCounts count).frontierSlots
  certificateExact :
    (composedSourceTargetCode count).size =
      (composedClosurePhaseCounts count).certificateAtoms
  primitiveQueriesExact :
    (composedClosureFuelTwo count).stats.primitiveQueries =
      (composedClosurePhaseCounts count).closurePrimitiveQueries
  compositionCandidatesExact :
    (composedClosureFuelTwo count).stats.compositionCandidates =
      (composedClosurePhaseCounts count).closureCompositionCandidates
  directIrreducible :
    SearchIrreducible
      (composedPrimitiveSearch count)
      (composedDirectFrontier count)
  closureSearchPresent :
    (composedBoundedClosureSearch count).find
        (composedSource count)
        (composedTarget count) ≠
      none
  closureWidthOne :
    (composedClosureReduction count).width = 1

/-- Complete event-count evidence for every parameter n. -/
theorem composedClosurePhaseEvidence
    (count : Nat) :
    ComposedClosurePhaseEvidence count :=
  { frontierExact :=
      composedDirectFrontier_width count
    certificateExact :=
      composedSourceTargetCode_size count
    primitiveQueriesExact :=
      composedClosureFuelTwo_primitiveQueries count
    compositionCandidatesExact :=
      composedClosureFuelTwo_compositionCandidates count
    directIrreducible :=
      composedDirectFrontier_irreducible count
    closureSearchPresent :=
      composedBoundedClosureSearch_source_target_present count
    closureWidthOne :=
      composedClosureReduction_width count }

/-- Charged cost of only the additional composition phase. -/
def composedClosurePhaseChargedCost
    (count : Nat)
    (costs : AtomicCosts) : Nat :=
  chargedCost
    (composedClosurePhaseCounts count)
    costs

/--
Expanded phase budget.  It exposes exactly the event classes that occur in the
composition benchmark.
-/
def composedClosurePhaseBudget
    (costs : AtomicCosts) : Nat :=
  2 * costs.frontierSlot +
    (2 * costs.certificateAtom +
      (3 * costs.closurePrimitiveQuery +
        costs.closureCompositionCandidate))

/-- The generic charged-cost interface reduces exactly to the phase budget. -/
theorem composedClosurePhaseChargedCost_eq_budget
    (count : Nat)
    (costs : AtomicCosts) :
    composedClosurePhaseChargedCost count costs =
      composedClosurePhaseBudget costs := by
  unfold composedClosurePhaseChargedCost
  unfold composedClosurePhaseCounts
  unfold chargedCost
  unfold composedClosurePhaseBudget
  rw [Nat.zero_mul]
  rw [Nat.zero_mul]
  rw [Nat.zero_mul]
  rw [Nat.zero_mul]
  rw [Nat.zero_mul]
  rw [Nat.one_mul]
  rw [Nat.zero_add]
  rw [Nat.zero_add]
  rw [Nat.zero_add]
  rw [Nat.zero_add]
  rw [Nat.zero_add]

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseCounts
#print axioms ConstitutiveSearch.SAT.ComposedClosurePhaseEvidence
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseEvidence
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseChargedCost
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseBudget
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseChargedCost_eq_budget
/- AXIOM_AUDIT_END -/
