import ConstitutiveSearch.ClosureSearchCosts

/-!
# Growth laws for bounded transport-closure search

The recursive budgets in ClosureSearchCosts deliberately expose the search tree.
This module derives exact structural growth laws.

At one fixed recursive budget r:
* scanning m intermediate candidates costs exactly m * (r + r) primitive
  queries in the worst-case envelope;
* composition-candidate accounting costs exactly m * (r + r + 1).

For candidateCount = 1, both complete closure budgets satisfy the same binary
recurrence:

  B(0) = 0
  B(f+1) = B(f) + B(f) + 1

Thus increasing fuel by one doubles the preceding budget and adds one.  This is
an exact control-flow recurrence, not a machine-time lower bound.
-/

namespace ConstitutiveSearch

/-- Closed form of candidate scanning for primitive-query budget. -/
theorem viaPrimitiveQueryBudget_closed
    (recursiveBudget : Nat) :
    ∀ candidateCount : Nat,
      viaPrimitiveQueryBudget
          recursiveBudget
          candidateCount =
        candidateCount *
          (recursiveBudget + recursiveBudget) := by
  intro candidateCount
  induction candidateCount with
  | zero =>
      rfl
  | succ candidateCount inductionHypothesis =>
      rw [show
        viaPrimitiveQueryBudget
            recursiveBudget
            (candidateCount + 1) =
          recursiveBudget +
            (recursiveBudget +
              viaPrimitiveQueryBudget
                recursiveBudget
                candidateCount) from rfl]
      rw [inductionHypothesis]
      rw [Nat.succ_mul]
      calc
        recursiveBudget +
            (recursiveBudget +
              candidateCount *
                (recursiveBudget + recursiveBudget))
            =
          (recursiveBudget + recursiveBudget) +
            candidateCount *
              (recursiveBudget + recursiveBudget) :=
            (Nat.add_assoc
              recursiveBudget
              recursiveBudget
              (candidateCount *
                (recursiveBudget + recursiveBudget))).symm
        _ =
          candidateCount *
              (recursiveBudget + recursiveBudget) +
            (recursiveBudget + recursiveBudget) :=
              Nat.add_comm
                (recursiveBudget + recursiveBudget)
                (candidateCount *
                  (recursiveBudget + recursiveBudget))

/-- Closed form of candidate scanning for composition-candidate budget. -/
theorem viaCompositionCandidateBudget_closed
    (recursiveBudget : Nat) :
    ∀ candidateCount : Nat,
      viaCompositionCandidateBudget
          recursiveBudget
          candidateCount =
        candidateCount *
          (recursiveBudget + recursiveBudget + 1) := by
  intro candidateCount
  induction candidateCount with
  | zero =>
      rfl
  | succ candidateCount inductionHypothesis =>
      rw [show
        viaCompositionCandidateBudget
            recursiveBudget
            (candidateCount + 1) =
          recursiveBudget +
              (recursiveBudget +
                viaCompositionCandidateBudget
                  recursiveBudget
                  candidateCount) +
            1 from rfl]
      rw [inductionHypothesis]
      rw [Nat.succ_mul]
      calc
        recursiveBudget +
              (recursiveBudget +
                candidateCount *
                  (recursiveBudget + recursiveBudget + 1)) +
            1
            =
          ((recursiveBudget + recursiveBudget) +
              candidateCount *
                (recursiveBudget + recursiveBudget + 1)) +
            1 := by
              rw [
                Nat.add_assoc
                  recursiveBudget
                  recursiveBudget
                  (candidateCount *
                    (recursiveBudget + recursiveBudget + 1))
              ]
        _ =
          (candidateCount *
              (recursiveBudget + recursiveBudget + 1) +
            (recursiveBudget + recursiveBudget)) +
              1 := by
                rw [
                  Nat.add_comm
                    (recursiveBudget + recursiveBudget)
                    (candidateCount *
                      (recursiveBudget + recursiveBudget + 1))
                ]
        _ =
          candidateCount *
              (recursiveBudget + recursiveBudget + 1) +
            (recursiveBudget + recursiveBudget + 1) := by
              rw [
                Nat.add_assoc
                  (candidateCount *
                    (recursiveBudget + recursiveBudget + 1))
                  (recursiveBudget + recursiveBudget)
                  1
              ]

/-- Canonical binary-tree recurrence exposed by one closure candidate. -/
def binaryClosureBudget : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
      binaryClosureBudget fuel +
        binaryClosureBudget fuel +
        1

/-- With one candidate, primitive-query budget is exactly the binary recurrence. -/
theorem closurePrimitiveQueryBudget_one_eq_binary :
    ∀ fuel : Nat,
      closurePrimitiveQueryBudget 1 fuel =
        binaryClosureBudget fuel := by
  intro fuel
  induction fuel with
  | zero =>
      rfl
  | succ fuel inductionHypothesis =>
      rw [show
        closurePrimitiveQueryBudget 1 (fuel + 1) =
          viaPrimitiveQueryBudget
              (closurePrimitiveQueryBudget 1 fuel)
              1 +
            1 from rfl]
      rw [viaPrimitiveQueryBudget_closed]
      rw [Nat.one_mul]
      rw [inductionHypothesis]
      rfl

/-- With one candidate, composition-candidate budget obeys the same recurrence. -/
theorem closureCompositionCandidateBudget_one_eq_binary :
    ∀ fuel : Nat,
      closureCompositionCandidateBudget 1 fuel =
        binaryClosureBudget fuel := by
  intro fuel
  induction fuel with
  | zero =>
      rfl
  | succ fuel inductionHypothesis =>
      rw [show
        closureCompositionCandidateBudget 1 (fuel + 1) =
          viaCompositionCandidateBudget
            (closureCompositionCandidateBudget 1 fuel)
            1 from rfl]
      rw [viaCompositionCandidateBudget_closed]
      rw [Nat.one_mul]
      rw [inductionHypothesis]
      rfl

/-- One more fuel unit doubles the previous binary budget and adds one. -/
theorem binaryClosureBudget_succ
    (fuel : Nat) :
    binaryClosureBudget (fuel + 1) =
      binaryClosureBudget fuel +
        binaryClosureBudget fuel +
        1 := by
  rfl

/-- Primitive-query closure budget with one candidate doubles-plus-one per fuel step. -/
theorem closurePrimitiveQueryBudget_one_succ
    (fuel : Nat) :
    closurePrimitiveQueryBudget 1 (fuel + 1) =
      closurePrimitiveQueryBudget 1 fuel +
        closurePrimitiveQueryBudget 1 fuel +
        1 := by
  rw [
    closurePrimitiveQueryBudget_one_eq_binary,
    closurePrimitiveQueryBudget_one_eq_binary
  ]
  exact
    binaryClosureBudget_succ fuel

/-- Composition-candidate closure budget with one candidate doubles-plus-one too. -/
theorem closureCompositionCandidateBudget_one_succ
    (fuel : Nat) :
    closureCompositionCandidateBudget 1 (fuel + 1) =
      closureCompositionCandidateBudget 1 fuel +
        closureCompositionCandidateBudget 1 fuel +
        1 := by
  rw [
    closureCompositionCandidateBudget_one_eq_binary,
    closureCompositionCandidateBudget_one_eq_binary
  ]
  exact
    binaryClosureBudget_succ fuel

/-- Fuel one always performs at most one primitive query, independently of candidate count. -/
theorem closurePrimitiveQueryBudget_fuel_one
    (candidateCount : Nat) :
    closurePrimitiveQueryBudget candidateCount 1 = 1 := by
  change
    viaPrimitiveQueryBudget 0 candidateCount + 1 = 1
  rw [viaPrimitiveQueryBudget_closed]
  rw [Nat.zero_add]
  rw [Nat.mul_zero]
  rfl

/-- Fuel one tests exactly candidateCount composition candidates in the envelope. -/
theorem closureCompositionCandidateBudget_fuel_one
    (candidateCount : Nat) :
    closureCompositionCandidateBudget candidateCount 1 =
      candidateCount := by
  change
    viaCompositionCandidateBudget 0 candidateCount =
      candidateCount
  rw [viaCompositionCandidateBudget_closed]
  rw [Nat.zero_add]
  rw [Nat.zero_add]
  rw [Nat.mul_one]

/-- Fuel two primitive-query envelope is exactly 2m+1. -/
theorem closurePrimitiveQueryBudget_fuel_two
    (candidateCount : Nat) :
    closurePrimitiveQueryBudget candidateCount 2 =
      candidateCount * 2 + 1 := by
  change
    viaPrimitiveQueryBudget
        (closurePrimitiveQueryBudget candidateCount 1)
        candidateCount +
      1 =
        candidateCount * 2 + 1
  rw [closurePrimitiveQueryBudget_fuel_one]
  rw [viaPrimitiveQueryBudget_closed]
  rfl

/-- Fuel two composition envelope is exactly m(2m+1). -/
theorem closureCompositionCandidateBudget_fuel_two
    (candidateCount : Nat) :
    closureCompositionCandidateBudget candidateCount 2 =
      candidateCount *
        (candidateCount + candidateCount + 1) := by
  change
    viaCompositionCandidateBudget
        (closureCompositionCandidateBudget candidateCount 1)
        candidateCount =
      candidateCount *
        (candidateCount + candidateCount + 1)
  rw [closureCompositionCandidateBudget_fuel_one]
  exact
    viaCompositionCandidateBudget_closed
      candidateCount
      candidateCount

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.viaPrimitiveQueryBudget_closed
#print axioms ConstitutiveSearch.viaCompositionCandidateBudget_closed
#print axioms ConstitutiveSearch.binaryClosureBudget
#print axioms ConstitutiveSearch.closurePrimitiveQueryBudget_one_eq_binary
#print axioms ConstitutiveSearch.closureCompositionCandidateBudget_one_eq_binary
#print axioms ConstitutiveSearch.binaryClosureBudget_succ
#print axioms ConstitutiveSearch.closurePrimitiveQueryBudget_one_succ
#print axioms ConstitutiveSearch.closureCompositionCandidateBudget_one_succ
#print axioms ConstitutiveSearch.closurePrimitiveQueryBudget_fuel_one
#print axioms ConstitutiveSearch.closureCompositionCandidateBudget_fuel_one
#print axioms ConstitutiveSearch.closurePrimitiveQueryBudget_fuel_two
#print axioms ConstitutiveSearch.closureCompositionCandidateBudget_fuel_two
/- AXIOM_AUDIT_END -/
