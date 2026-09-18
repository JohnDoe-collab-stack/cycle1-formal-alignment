import ConstitutiveSearch.SAT.ExplicitFamilyEqualityCosts

/-!
# Concrete representation-charged cost model for F(n)

This module instantiates AtomicCosts with explicit binary representation charges.

The model is concrete:
* syntax unit: one bit;
* frontier slot: formula budget plus full-history budget;
* provenance unit: one encoded decision node;
* certificate atom: one tag plus the selected variable representation;
* relation query: the four-operand equality charge proved for structural flip;
* closure candidate: one encoded state envelope;
* terminal check: one encoded history envelope.

It is still a representation-charge model, not a theorem about wall-clock time
of Lean's runtime.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Uniform encoded state envelope for the explicit family. -/
def explicitFamilyStateBinaryBudget
    (count : Nat) : Nat :=
  explicitFamilyBinaryBudget count +
    StructuralDecisionHistory.binaryBudget
      count
      count

/-- Encoded envelope for one constituted decision/provenance unit. -/
def explicitFamilyProvenanceUnitBinaryBudget
    (count : Nat) : Nat :=
  StructuralDecisionHistory.binaryBudget
    count
    1

/-- Encoded charge of one local flip-certificate atom and its variable. -/
def explicitFamilyCertificateAtomBinaryBudget
    (count : Nat) : Nat :=
  Nat.succ
    (BinaryRepresentation.natBitSize count)

/--
Concrete representation charges assigned to the certified event profile of
F(n).
-/
def explicitFamilyRepresentationAtomicCosts
    (count : Nat) : AtomicCosts :=
  { syntaxUnit := 1
    frontierSlot :=
      explicitFamilyStateBinaryBudget count
    provenanceUnit :=
      explicitFamilyProvenanceUnitBinaryBudget count
    certificateAtom :=
      explicitFamilyCertificateAtomBinaryBudget count
    relationFindCall :=
      explicitFamilyRelationEqualityChargeBudget count
    closurePrimitiveQuery :=
      explicitFamilyRelationEqualityChargeBudget count
    closureCompositionCandidate :=
      explicitFamilyStateBinaryBudget count
    terminalCheck :=
      StructuralDecisionHistory.binaryBudget
        count
        count }

/-- Aggregate representation charge of the announced F(n) execution. -/
def explicitFamilyRepresentationChargedCost
    (count : Nat) : Nat :=
  explicitFamilyChargedCost
    count
    (explicitFamilyRepresentationAtomicCosts count)

/-- Relation calls are charged by the proved four-operand binary equality budget. -/
theorem explicitFamily_relationFind_atomicCost
    (count : Nat) :
    (explicitFamilyRepresentationAtomicCosts count)
        .relationFindCall =
      explicitFamilyRelationEqualityChargeBudget count := by
  rfl

/-- Closure primitive queries use the same equality charge when later enabled. -/
theorem explicitFamily_closurePrimitive_atomicCost
    (count : Nat) :
    (explicitFamilyRepresentationAtomicCosts count)
        .closurePrimitiveQuery =
      explicitFamilyRelationEqualityChargeBudget count := by
  rfl

/--
The local F(n) strategy pays zero closure-search charge because its certified
event profile contains no closure search.
-/
theorem explicitFamily_localStrategy_noClosureCharge
    (count : Nat) :
    (explicitFamilyComplexityCounts count)
          .closurePrimitiveQueries *
          (explicitFamilyRepresentationAtomicCosts count)
            .closurePrimitiveQuery +
        (explicitFamilyComplexityCounts count)
          .closureCompositionCandidates *
          (explicitFamilyRepresentationAtomicCosts count)
            .closureCompositionCandidate =
      0 := by
  rfl

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.explicitFamilyStateBinaryBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyProvenanceUnitBinaryBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyCertificateAtomBinaryBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyRepresentationAtomicCosts
#print axioms ConstitutiveSearch.SAT.explicitFamilyRepresentationChargedCost
#print axioms ConstitutiveSearch.SAT.explicitFamily_relationFind_atomicCost
#print axioms ConstitutiveSearch.SAT.explicitFamily_closurePrimitive_atomicCost
#print axioms ConstitutiveSearch.SAT.explicitFamily_localStrategy_noClosureCharge
/- AXIOM_AUDIT_END -/
