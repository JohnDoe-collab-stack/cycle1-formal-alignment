import ConstitutiveSearch.ClosureSearchGrowth

/-!
# Polynomial regimes for bounded transport-closure search

ClosureSearchGrowth exposes exact control-flow recurrences.  This module isolates
one first sufficient polynomial regime:

* composition fuel is fixed to two;
* the explicit candidate-list length is bounded by the concrete input-size
  index.

Under these hypotheses:
* primitive relation queries are bounded linearly in inputBits;
* composition candidates are bounded quadratically in inputBits.

The result concerns source-level search events.  It does not convert one event
into wall-clock machine time.
-/

namespace ConstitutiveSearch

universe uGenerator

/-- Generic product monotonicity for natural-number envelopes. -/
theorem closureNatMulLeMul
    {leftSmall leftLarge rightSmall rightLarge : Nat}
    (leftLe : leftSmall ≤ leftLarge)
    (rightLe : rightSmall ≤ rightLarge) :
    leftSmall * rightSmall ≤
      leftLarge * rightLarge := by
  have first :
      leftSmall * rightSmall ≤
        leftLarge * rightSmall := by
    calc
      leftSmall * rightSmall
          =
        rightSmall * leftSmall :=
          Nat.mul_comm leftSmall rightSmall
      _ ≤
        rightSmall * leftLarge :=
          Nat.mul_le_mul_left
            rightSmall
            leftLe
      _ =
        leftLarge * rightSmall :=
          Nat.mul_comm rightSmall leftLarge
  have second :
      leftLarge * rightSmall ≤
        leftLarge * rightLarge :=
    Nat.mul_le_mul_left
      leftLarge
      rightLe
  exact Nat.le_trans first second

/-- Linear primitive-query envelope for the fixed-fuel-two regime. -/
def closureFuelTwoPrimitiveInputBudget
    (inputBits : Nat) : Nat :=
  inputBits * 2 + 1

/-- Quadratic composition-candidate envelope for the fixed-fuel-two regime. -/
def closureFuelTwoCompositionInputBudget
    (inputBits : Nat) : Nat :=
  inputBits *
    (inputBits + inputBits + 1)

/-- Combined source-level closure-search event envelope. -/
def closureFuelTwoTotalInputBudget
    (inputBits : Nat) : Nat :=
  closureFuelTwoPrimitiveInputBudget inputBits +
    closureFuelTwoCompositionInputBudget inputBits

/--
If the candidate list is bounded by inputBits, the fuel-two primitive-query
budget is bounded by a linear expression in inputBits.
-/
theorem closurePrimitiveQueryBudget_fuel_two_le_input
    (candidateCount inputBits : Nat)
    (candidateLe :
      candidateCount ≤ inputBits) :
    closurePrimitiveQueryBudget candidateCount 2 ≤
      closureFuelTwoPrimitiveInputBudget inputBits := by
  rw [closurePrimitiveQueryBudget_fuel_two]
  unfold closureFuelTwoPrimitiveInputBudget
  have doubledLe :
      candidateCount * 2 ≤
        inputBits * 2 := by
    calc
      candidateCount * 2
          =
        2 * candidateCount :=
          Nat.mul_comm candidateCount 2
      _ ≤
        2 * inputBits :=
          Nat.mul_le_mul_left
            2
            candidateLe
      _ =
        inputBits * 2 :=
          Nat.mul_comm 2 inputBits
  exact
    Nat.add_le_add_right
      doubledLe
      1

/--
If the candidate list is bounded by inputBits, the fuel-two composition
candidate budget is bounded quadratically in inputBits.
-/
theorem closureCompositionCandidateBudget_fuel_two_le_input
    (candidateCount inputBits : Nat)
    (candidateLe :
      candidateCount ≤ inputBits) :
    closureCompositionCandidateBudget candidateCount 2 ≤
      closureFuelTwoCompositionInputBudget inputBits := by
  rw [closureCompositionCandidateBudget_fuel_two]
  unfold closureFuelTwoCompositionInputBudget
  have innerLe :
      candidateCount + candidateCount + 1 ≤
        inputBits + inputBits + 1 :=
    Nat.add_le_add_right
      (Nat.add_le_add
        candidateLe
        candidateLe)
      1
  exact
    closureNatMulLeMul
      candidateLe
      innerLe

/-- Combined fixed-fuel-two budget is bounded by the declared input envelope. -/
theorem closureFuelTwoBudgets_le_totalInput
    (candidateCount inputBits : Nat)
    (candidateLe :
      candidateCount ≤ inputBits) :
    closurePrimitiveQueryBudget candidateCount 2 +
        closureCompositionCandidateBudget candidateCount 2 ≤
      closureFuelTwoTotalInputBudget inputBits := by
  unfold closureFuelTwoTotalInputBudget
  exact
    Nat.add_le_add
      (closurePrimitiveQueryBudget_fuel_two_le_input
        candidateCount
        inputBits
        candidateLe)
      (closureCompositionCandidateBudget_fuel_two_le_input
        candidateCount
        inputBits
        candidateLe)

/--
Actual primitive-query count of the executable closure engine is linearly
bounded in inputBits under the fixed-fuel-two candidate regime.
-/
theorem searchTransportClosureFuelTwo_primitiveQueries_le_input
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (inputBits : Nat)
    (candidateLe :
      candidates.length ≤ inputBits)
    (source target : State) :
    (searchTransportClosureBounded
      primitive
      candidates
      2
      source
      target).stats.primitiveQueries ≤
      closureFuelTwoPrimitiveInputBudget inputBits := by
  exact
    Nat.le_trans
      (searchTransportClosureBounded_primitiveQueries_le
        primitive
        candidates
        2
        source
        target)
      (closurePrimitiveQueryBudget_fuel_two_le_input
        candidates.length
        inputBits
        candidateLe)

/--
Actual composition-candidate count of the executable closure engine is
quadratically bounded in inputBits under the same regime.
-/
theorem searchTransportClosureFuelTwo_compositionCandidates_le_input
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (inputBits : Nat)
    (candidateLe :
      candidates.length ≤ inputBits)
    (source target : State) :
    (searchTransportClosureBounded
      primitive
      candidates
      2
      source
      target).stats.compositionCandidates ≤
      closureFuelTwoCompositionInputBudget inputBits := by
  exact
    Nat.le_trans
      (searchTransportClosureBounded_compositionCandidates_le
        primitive
        candidates
        2
        source
        target)
      (closureCompositionCandidateBudget_fuel_two_le_input
        candidates.length
        inputBits
        candidateLe)

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.closureNatMulLeMul
#print axioms ConstitutiveSearch.closureFuelTwoPrimitiveInputBudget
#print axioms ConstitutiveSearch.closureFuelTwoCompositionInputBudget
#print axioms ConstitutiveSearch.closureFuelTwoTotalInputBudget
#print axioms ConstitutiveSearch.closurePrimitiveQueryBudget_fuel_two_le_input
#print axioms ConstitutiveSearch.closureCompositionCandidateBudget_fuel_two_le_input
#print axioms ConstitutiveSearch.closureFuelTwoBudgets_le_totalInput
#print axioms ConstitutiveSearch.searchTransportClosureFuelTwo_primitiveQueries_le_input
#print axioms ConstitutiveSearch.searchTransportClosureFuelTwo_compositionCandidates_le_input
/- AXIOM_AUDIT_END -/
