import Init.Omega
import ConstitutiveSearch.ClosureSearchBoundedCandidatesLogFuelPolynomial
import ConstitutiveSearch.PolynomialExponentialSeparator

/-!
# Growing-candidate logarithmic-fuel separator

The bounded-candidate logarithmic theorem gives a polynomial regime when
candidate count has one uniform finite cap.

This module shows that the cap matters for the current ClosureSearch engine.

Consider the concrete family

  inputBits(n)      = 2^(n+1)
  candidateCount(n) = inputBits(n)
  fuel(n)           = n+1 = log2(inputBits(n)).

Thus:
* fuel grows only logarithmically in the concrete input size;
* candidate count grows linearly in that same input size.

Nevertheless the canonical recursive closure budgets are not
InputPolynomiallyBounded.

The proof is internal to CostPolynomial.  A lower geometric envelope for the
closure recurrence is compared against the structural monomial majorant already
available for every finite CostPolynomial.

This is a separator for the announced source-level ClosureSearch budgets.  It
is not a wall-clock machine-time lower bound.
-/

namespace ConstitutiveSearch

/--
Primitive-query closure budget contains at least one full geometric layer.
-/
theorem closurePrimitiveQueryBudget_geometric_lower
    (candidateCount : Nat) :
    ∀ fuel : Nat,
      (candidateCount +
          candidateCount) ^ fuel ≤
        closurePrimitiveQueryBudget
          candidateCount
          (fuel + 1) := by
  intro fuel
  induction fuel with
  | zero =>
      rw [
        Nat.pow_zero,
        closurePrimitiveQueryBudget_fuel_one
      ]
      exact Nat.le_refl 1
  | succ fuel inductionHypothesis =>
      let recursive :=
        closurePrimitiveQueryBudget
          candidateCount
          (fuel + 1)
      let multiplier :=
        candidateCount +
          candidateCount
      have lifted :
          multiplier *
              (multiplier ^ fuel) ≤
            multiplier *
              recursive :=
        Nat.mul_le_mul_left
          multiplier
          inductionHypothesis
      have recurrenceProduct :
          candidateCount *
              (recursive + recursive) =
            multiplier * recursive := by
        unfold multiplier
        rw [
          Nat.mul_add,
          Nat.add_mul
        ]
      rw [show
        closurePrimitiveQueryBudget
            candidateCount
            ((fuel + 1) + 1) =
          viaPrimitiveQueryBudget
              recursive
              candidateCount +
            1 from rfl]
      rw [
        viaPrimitiveQueryBudget_closed
      ]
      change
        multiplier ^ (fuel + 1) ≤
          candidateCount *
              (recursive + recursive) +
            1
      calc
        multiplier ^ (fuel + 1)
            =
          multiplier ^ fuel *
            multiplier := by
              rw [Nat.pow_succ]
        _ =
          multiplier *
            multiplier ^ fuel :=
              Nat.mul_comm _ _
        _ ≤
          multiplier * recursive :=
            lifted
        _ =
          candidateCount *
            (recursive + recursive) :=
              recurrenceProduct.symm
        _ ≤
          candidateCount *
                (recursive + recursive) +
              1 :=
            Nat.le_add_right _ _

/--
Composition-candidate closure budget has a corresponding geometric lower layer.
-/
theorem closureCompositionCandidateBudget_geometric_lower
    (candidateCount : Nat) :
    ∀ fuel : Nat,
      candidateCount *
          (candidateCount +
            candidateCount) ^ fuel ≤
        closureCompositionCandidateBudget
          candidateCount
          (fuel + 1) := by
  intro fuel
  induction fuel with
  | zero =>
      rw [
        Nat.pow_zero,
        Nat.mul_one,
        closureCompositionCandidateBudget_fuel_one
      ]
      exact Nat.le_refl candidateCount
  | succ fuel inductionHypothesis =>
      let recursive :=
        closureCompositionCandidateBudget
          candidateCount
          (fuel + 1)
      let multiplier :=
        candidateCount +
          candidateCount
      have lifted :
          multiplier *
              (candidateCount *
                multiplier ^ fuel) ≤
            multiplier *
              recursive :=
        Nat.mul_le_mul_left
          multiplier
          inductionHypothesis
      have recurrenceExpanded :
          candidateCount *
              (recursive +
                recursive +
                1) =
            multiplier * recursive +
              candidateCount := by
        unfold multiplier
        rw [
          Nat.mul_add,
          Nat.mul_add,
          Nat.mul_one,
          Nat.add_mul
        ]
      rw [show
        closureCompositionCandidateBudget
            candidateCount
            ((fuel + 1) + 1) =
          viaCompositionCandidateBudget
            recursive
            candidateCount from rfl]
      rw [
        viaCompositionCandidateBudget_closed
      ]
      change
        candidateCount *
              multiplier ^ (fuel + 1) ≤
          candidateCount *
            (recursive + recursive + 1)
      calc
        candidateCount *
              multiplier ^ (fuel + 1)
            =
          multiplier *
            (candidateCount *
              multiplier ^ fuel) := by
                rw [Nat.pow_succ]
                ac_rfl
        _ ≤
          multiplier * recursive :=
            lifted
        _ ≤
          multiplier * recursive +
            candidateCount :=
              Nat.le_add_right _ _
        _ =
          candidateCount *
            (recursive + recursive + 1) :=
              recurrenceExpanded.symm

/--
For candidateCount >= 1, composition budget dominates primitive-query budget at
every fuel.
-/
theorem closurePrimitiveQueryBudget_le_compositionCandidateBudget
    (candidateCount : Nat)
    (candidatePositive :
      1 ≤ candidateCount) :
    ∀ fuel : Nat,
      closurePrimitiveQueryBudget
          candidateCount
          fuel ≤
        closureCompositionCandidateBudget
          candidateCount
          fuel := by
  intro fuel
  induction fuel with
  | zero =>
      exact Nat.le_refl 0
  | succ fuel inductionHypothesis =>
      let primitiveRecursive :=
        closurePrimitiveQueryBudget
          candidateCount
          fuel
      let compositionRecursive :=
        closureCompositionCandidateBudget
          candidateCount
          fuel
      have doubledLe :
          primitiveRecursive +
              primitiveRecursive ≤
            compositionRecursive +
              compositionRecursive :=
        Nat.add_le_add
          inductionHypothesis
          inductionHypothesis
      have multipliedLe :
          candidateCount *
              (primitiveRecursive +
                primitiveRecursive) ≤
            candidateCount *
              (compositionRecursive +
                compositionRecursive) :=
        Nat.mul_le_mul_left
          candidateCount
          doubledLe
      have withTailLe :
          candidateCount *
                (primitiveRecursive +
                  primitiveRecursive) +
              1 ≤
            candidateCount *
                (compositionRecursive +
                  compositionRecursive) +
              candidateCount :=
        Nat.add_le_add
          multipliedLe
          candidatePositive
      rw [show
        closurePrimitiveQueryBudget
            candidateCount
            (fuel + 1) =
          viaPrimitiveQueryBudget
              primitiveRecursive
              candidateCount +
            1 from rfl]
      rw [show
        closureCompositionCandidateBudget
            candidateCount
            (fuel + 1) =
          viaCompositionCandidateBudget
            compositionRecursive
            candidateCount from rfl]
      rw [
        viaPrimitiveQueryBudget_closed,
        viaCompositionCandidateBudget_closed
      ]
      change
        candidateCount *
              (primitiveRecursive +
                primitiveRecursive) +
            1 ≤
          candidateCount *
            (compositionRecursive +
              compositionRecursive +
              1)
      calc
        candidateCount *
              (primitiveRecursive +
                primitiveRecursive) +
            1
            ≤
          candidateCount *
                (compositionRecursive +
                  compositionRecursive) +
              candidateCount :=
                withTailLe
        _ =
          candidateCount *
            (compositionRecursive +
              compositionRecursive +
              1) := by
                simp only [
                  Nat.mul_add,
                  Nat.mul_one
                ]

/-- Concrete input size for the growing-candidate logarithmic separator. -/
def growingCandidatesLogInputBits
    (n : Nat) : Nat :=
  2 ^ (n + 1)

/-- Candidate count grows linearly with the concrete input size. -/
def growingCandidatesLogCandidateCount
    (n : Nat) : Nat :=
  growingCandidatesLogInputBits n

/-- Fuel grows logarithmically with concrete input size. -/
def growingCandidatesLogFuel
    (n : Nat) : Nat :=
  n + 1

theorem growingCandidatesLogInputPositive :
    ∀ n : Nat,
      0 <
        growingCandidatesLogInputBits n := by
  intro n
  unfold growingCandidatesLogInputBits
  exact
    Nat.pow_pos
      Nat.zero_lt_two

theorem growingCandidatesLogFuel_eq_log :
    ∀ n : Nat,
      growingCandidatesLogFuel n =
        Nat.log2
          (growingCandidatesLogInputBits n) := by
  intro n
  unfold
    growingCandidatesLogFuel
    growingCandidatesLogInputBits
  exact
    (Nat.log2_two_pow).symm

theorem growingCandidatesLogFuel_unbounded :
    ∀ cap : Nat,
      ∃ n : Nat,
        cap <
          growingCandidatesLogFuel n := by
  intro cap
  exact
    ⟨cap,
      by
        unfold growingCandidatesLogFuel
        exact Nat.lt_succ_self cap⟩

/-- Candidate count itself is exactly the concrete input-size coordinate. -/
theorem growingCandidatesLogCandidateCount_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      growingCandidatesLogInputBits
      growingCandidatesLogCandidateCount := by
  change
    InputPolynomiallyBounded
      growingCandidatesLogInputBits
      growingCandidatesLogInputBits
  exact
    InputPolynomiallyBounded.self
      growingCandidatesLogInputBits

/--
Every finite CostPolynomial envelope is beaten by the primitive closure budget
somewhere on the growing-candidate logarithmic family.
-/
theorem growingCandidatesLogPrimitive_escapes
    (envelope : CostPolynomial) :
    ∃ n : Nat,
      envelope.eval
          (growingCandidatesLogInputBits n) <
        closurePrimitiveQueryBudget
          (growingCandidatesLogCandidateCount n)
          (growingCandidatesLogFuel n) := by
  let n :=
    envelope.escapeExponent
  let input :=
    growingCandidatesLogInputBits n
  let mass :=
    envelope.majorantMass
  let rank :=
    envelope.majorantRank
  refine
    ⟨n, ?_⟩
  have inputPositive :
      0 < input := by
    unfold input growingCandidatesLogInputBits
    exact
      Nat.pow_pos
        Nat.zero_lt_two
  have inputOneLe :
      1 ≤ input :=
    inputPositive
  have envelopeLeMajorant :
      envelope.eval input ≤
        mass *
          input ^ rank := by
    simpa only [
      mass,
      rank
    ] using
      envelope.eval_le_majorant
        input
        inputOneLe
  have massLePower :
      mass ≤
        2 ^ mass :=
    Nat.le_of_lt
      Nat.lt_two_pow_self
  have coefficientLift :
      mass *
          input ^ rank ≤
        2 ^ mass *
          input ^ rank :=
    Nat.mul_le_mul_right
      (input ^ rank)
      massLePower
  have inputEq :
      input =
        2 ^ (n + 1) := by
    rfl
  have majorantPowerEq :
      2 ^ mass *
          input ^ rank =
        2 ^
          (mass +
            (n + 1) * rank) := by
    rw [
      inputEq,
      ← Nat.pow_mul,
      ← Nat.pow_add
    ]
  have envelopeLePower :
      envelope.eval input ≤
        2 ^
          (mass +
            (n + 1) * rank) := by
    calc
      envelope.eval input
          ≤
        mass *
          input ^ rank :=
            envelopeLeMajorant
      _ ≤
        2 ^ mass *
          input ^ rank :=
            coefficientLift
      _ =
        2 ^
          (mass +
            (n + 1) * rank) :=
              majorantPowerEq
  have massLtN :
      mass < n := by
    simpa only [
      mass,
      n
    ] using
      envelope.majorantMass_lt_escapeExponent
  have coreLtN :
      envelope.escapeCore < n := by
    dsimp [n]
    unfold CostPolynomial.escapeExponent
    exact
      Nat.lt_two_pow_self
  have rankSuccLeCore :
      envelope.majorantRank + 1 ≤
        envelope.escapeCore :=
    envelope.majorantRank_succ_le_escapeCore
  have rankLeN :
      rank ≤ n := by
    have rankLtN :
        envelope.majorantRank < n := by
      omega
    simpa only [rank] using
      Nat.le_of_lt rankLtN
  have rankProductLe :
      (n + 1) * rank ≤
        (n + 1) * n :=
    Nat.mul_le_mul_left
      (n + 1)
      rankLeN
  have exponentIntermediate :
      mass +
          (n + 1) * rank <
        n +
          (n + 1) * n := by
    have first :
        mass +
            (n + 1) * rank <
          n +
            (n + 1) * rank :=
      Nat.add_lt_add_right
        massLtN
        ((n + 1) * rank)
    have second :
        n +
            (n + 1) * rank ≤
          n +
            (n + 1) * n :=
      Nat.add_le_add_left
        rankProductLe
        n
    exact
      Nat.lt_of_lt_of_le
        first
        second
  have targetEq :
      n +
          (n + 1) * n =
        (n + 2) * n := by
    simp only [
      Nat.add_mul,
      Nat.one_mul
    ]
    omega
  have exponentLt :
      mass +
          (n + 1) * rank <
        (n + 2) * n := by
    rw [← targetEq]
    exact
      exponentIntermediate
  have majorantPowerLt :
      2 ^
          (mass +
            (n + 1) * rank) <
        2 ^ ((n + 2) * n) :=
    Nat.pow_lt_pow_right
      Nat.one_lt_two
      exponentLt
  have doubledInputEq :
      input + input =
        2 ^ (n + 2) := by
    calc
      input + input
          =
        input * 2 :=
          (Nat.mul_two input).symm
      _ =
        2 ^ (n + 1) * 2 := by
          rw [inputEq]
      _ =
        2 ^ ((n + 1) + 1) :=
          (Nat.pow_succ
            2
            (n + 1)).symm
      _ =
        2 ^ (n + 2) := by
          congr 1
  have lowerPowerEq :
      (input + input) ^ n =
        2 ^ ((n + 2) * n) := by
    rw [
      doubledInputEq,
      ← Nat.pow_mul
    ]
  have lowerBudget :
      (input + input) ^ n ≤
        closurePrimitiveQueryBudget
          input
          (n + 1) :=
    closurePrimitiveQueryBudget_geometric_lower
      input
      n
  change
    envelope.eval input <
      closurePrimitiveQueryBudget
        input
        (n + 1)
  calc
    envelope.eval input
        ≤
      2 ^
        (mass +
          (n + 1) * rank) :=
            envelopeLePower
    _ <
      2 ^ ((n + 2) * n) :=
        majorantPowerLt
    _ =
      (input + input) ^ n :=
        lowerPowerEq.symm
    _ ≤
      closurePrimitiveQueryBudget
        input
        (n + 1) :=
          lowerBudget

/--
Primitive-query source-level closure budget is not input-polynomial when
candidate count is linear in input size and fuel is logarithmic.
-/
theorem growingCandidatesLogPrimitive_not_inputPolynomiallyBounded :
    ¬
      InputPolynomiallyBounded
        growingCandidatesLogInputBits
        (fun n =>
          closurePrimitiveQueryBudget
            (growingCandidatesLogCandidateCount n)
            (growingCandidatesLogFuel n)) := by
  intro bounded
  rcases bounded with
    ⟨envelope, budgetLe⟩
  rcases
      growingCandidatesLogPrimitive_escapes
        envelope with
    ⟨n, envelopeLt⟩
  have impossible :
      envelope.eval
          (growingCandidatesLogInputBits n) <
        envelope.eval
          (growingCandidatesLogInputBits n) :=
    Nat.lt_of_lt_of_le
      envelopeLt
      (budgetLe n)
  exact
    (Nat.lt_irrefl
      (envelope.eval
        (growingCandidatesLogInputBits n)))
      impossible

/--
Composition-candidate source-level closure budget is also not input-polynomial
on the same family.
-/
theorem growingCandidatesLogComposition_not_inputPolynomiallyBounded :
    ¬
      InputPolynomiallyBounded
        growingCandidatesLogInputBits
        (fun n =>
          closureCompositionCandidateBudget
            (growingCandidatesLogCandidateCount n)
            (growingCandidatesLogFuel n)) := by
  intro bounded
  rcases bounded with
    ⟨envelope, compositionLe⟩
  have primitiveBounded :
      InputPolynomiallyBounded
        growingCandidatesLogInputBits
        (fun n =>
          closurePrimitiveQueryBudget
            (growingCandidatesLogCandidateCount n)
            (growingCandidatesLogFuel n)) := by
    refine
      ⟨envelope, ?_⟩
    intro n
    have candidatePositive :
        1 ≤
          growingCandidatesLogCandidateCount n := by
      unfold
        growingCandidatesLogCandidateCount
        growingCandidatesLogInputBits
      exact
        Nat.pow_pos
          Nat.zero_lt_two
    exact
      Nat.le_trans
        (closurePrimitiveQueryBudget_le_compositionCandidateBudget
          (growingCandidatesLogCandidateCount n)
          candidatePositive
          (growingCandidatesLogFuel n))
        (compositionLe n)
  exact
    growingCandidatesLogPrimitive_not_inputPolynomiallyBounded
      primitiveBounded

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.closurePrimitiveQueryBudget_geometric_lower
#print axioms ConstitutiveSearch.closureCompositionCandidateBudget_geometric_lower
#print axioms ConstitutiveSearch.closurePrimitiveQueryBudget_le_compositionCandidateBudget
#print axioms ConstitutiveSearch.growingCandidatesLogInputBits
#print axioms ConstitutiveSearch.growingCandidatesLogCandidateCount
#print axioms ConstitutiveSearch.growingCandidatesLogFuel
#print axioms ConstitutiveSearch.growingCandidatesLogInputPositive
#print axioms ConstitutiveSearch.growingCandidatesLogFuel_eq_log
#print axioms ConstitutiveSearch.growingCandidatesLogFuel_unbounded
#print axioms ConstitutiveSearch.growingCandidatesLogCandidateCount_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.growingCandidatesLogPrimitive_escapes
#print axioms ConstitutiveSearch.growingCandidatesLogPrimitive_not_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.growingCandidatesLogComposition_not_inputPolynomiallyBounded
/- AXIOM_AUDIT_END -/
