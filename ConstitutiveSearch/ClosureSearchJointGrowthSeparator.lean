import Init.Omega
import ConstitutiveSearch.ClosureSearchWidthGrowthPolynomial
import ConstitutiveSearch.PolynomialExponentialSeparator

/-!
# Joint-growth negative separator for closure budgets

Positive joint-growth theorems show that logarithmic fuel can remain
polynomial when candidate growth is sufficiently controlled.

This module gives a complementary negative benchmark for the recursive
ClosureSearch budget functions.

Consider the concrete family

  inputBits(n)      = 2^(n+4)
  candidateCount(n) = inputBits(n)
  fuel(n)           = n+4 = log2(inputBits(n)).

Thus candidate count is linear in the concrete input size and fuel is exactly
logarithmic.  Nevertheless the canonical recursive budget grows too fast to
admit any finite CostPolynomial envelope in inputBits.

The proof is internal:
* primitive-query budget is strictly above a power of (2*candidateCount);
* every CostPolynomial has the structural monomial majorant already proved in
  PolynomialExponentialSeparator;
* an explicit index derived from the envelope syntax separates the exponents.

The result concerns the announced recursive budget functions.  Since those
budgets are upper bounds on executable counters, this module does not infer an
execution-time lower bound.
-/

namespace ConstitutiveSearch

/--
For every positive candidate count, primitive budget at fuel f+2 strictly
exceeds (2*m)^(f+1).
-/
theorem closurePrimitiveQueryBudget_doublePower_lt
    (candidateCount : Nat)
    (candidatePositive :
      0 < candidateCount) :
    ∀ fuel : Nat,
      (candidateCount +
          candidateCount) ^
          (fuel + 1) <
        closurePrimitiveQueryBudget
          candidateCount
          (fuel + 2) := by
  intro fuel
  induction fuel with
  | zero =>
      rw [
        closurePrimitiveQueryBudget_fuel_two,
        Nat.pow_one
      ]
      omega
  | succ fuel inductionHypothesis =>
      let recursive :=
        closurePrimitiveQueryBudget
          candidateCount
          (fuel + 2)
      let base :=
        candidateCount +
          candidateCount
      have basePositive :
          0 < base := by
        unfold base
        omega
      have scaled :
          base ^ (fuel + 1) * base <
            recursive * base := by
        exact
          (Nat.mul_lt_mul_right
            basePositive).2
            inductionHypothesis
      rw [show
        closurePrimitiveQueryBudget
            candidateCount
            ((fuel + 1) + 2) =
          viaPrimitiveQueryBudget
              recursive
              candidateCount +
            1 from rfl]
      rw [viaPrimitiveQueryBudget_closed]
      change
        base ^ ((fuel + 1) + 1) <
          candidateCount *
              (recursive + recursive) +
            1
      rw [Nat.pow_succ]
      have recursiveExact :
          recursive * base =
            candidateCount *
              (recursive + recursive) := by
        unfold base
        calc
          recursive *
                (candidateCount + candidateCount)
              =
            recursive * candidateCount +
              recursive * candidateCount :=
                Nat.mul_add
                  recursive
                  candidateCount
                  candidateCount
          _ =
            candidateCount * recursive +
              candidateCount * recursive := by
                rw [
                  Nat.mul_comm
                    recursive
                    candidateCount
                ]
          _ =
            candidateCount *
              (recursive + recursive) :=
                (Nat.mul_add
                  candidateCount
                  recursive
                  recursive).symm
      calc
        base ^ (fuel + 1) * base
            <
          recursive * base :=
            scaled
        _ =
          candidateCount *
            (recursive + recursive) :=
              recursiveExact
        _ <
          candidateCount *
                (recursive + recursive) +
              1 :=
            Nat.lt_succ_self _

/--
For a positive candidate count, primitive-query budget is pointwise below the
composition-candidate budget.
-/
theorem closurePrimitiveQueryBudget_le_composition
    (candidateCount : Nat)
    (candidatePositive :
      0 < candidateCount) :
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
      let base :=
        candidateCount +
          candidateCount
      have oneLeCandidate :
          1 ≤ candidateCount := by
        omega
      have scaled :
          base * primitiveRecursive ≤
            base * compositionRecursive :=
        Nat.mul_le_mul_left
          base
          inductionHypothesis
      have primitiveStep :
          closurePrimitiveQueryBudget
              candidateCount
              (fuel + 1) =
            base * primitiveRecursive +
              1 := by
        rw [show
          closurePrimitiveQueryBudget
              candidateCount
              (fuel + 1) =
            viaPrimitiveQueryBudget
                primitiveRecursive
                candidateCount +
              1 from rfl]
        rw [viaPrimitiveQueryBudget_closed]
        unfold base
        rw [
          Nat.mul_add,
          Nat.add_mul
        ]
      have compositionStep :
          closureCompositionCandidateBudget
              candidateCount
              (fuel + 1) =
            base * compositionRecursive +
              candidateCount := by
        rw [show
          closureCompositionCandidateBudget
              candidateCount
              (fuel + 1) =
            viaCompositionCandidateBudget
              compositionRecursive
              candidateCount from rfl]
        rw [viaCompositionCandidateBudget_closed]
        unfold base
        rw [
          Nat.mul_add,
          Nat.mul_add,
          Nat.mul_one,
          Nat.add_mul
        ]
      rw [
        primitiveStep,
        compositionStep
      ]
      exact
        Nat.add_le_add
          scaled
          oneLeCandidate

/-! ## Concrete joint-growth family -/

/-- Concrete binary input size of the negative joint-growth witness. -/
def jointHardInputBits
    (n : Nat) : Nat :=
  2 ^ (n + 4)

/-- Candidate count is exactly linear in the concrete input size. -/
def jointHardCandidateCount
    (n : Nat) : Nat :=
  jointHardInputBits n

/-- Fuel is exactly logarithmic in the concrete input size. -/
def jointHardFuel
    (n : Nat) : Nat :=
  n + 4

/-- Candidate count equals input size definitionally. -/
theorem jointHardCandidateCount_eq_input
    (n : Nat) :
    jointHardCandidateCount n =
      jointHardInputBits n := by
  rfl

/-- Fuel is exactly log2(inputBits). -/
theorem jointHardFuel_eq_log2Input
    (n : Nat) :
    jointHardFuel n =
      Nat.log2
        (jointHardInputBits n) := by
  unfold
    jointHardFuel
    jointHardInputBits
  rw [Nat.log2_two_pow]

/-- Concrete input size is positive. -/
theorem jointHardInputBits_positive
    (n : Nat) :
    0 < jointHardInputBits n := by
  unfold jointHardInputBits
  exact
    Nat.pow_pos
      Nat.zero_lt_two

/-- Candidate count is therefore positive. -/
theorem jointHardCandidateCount_positive
    (n : Nat) :
    0 < jointHardCandidateCount n := by
  rw [jointHardCandidateCount_eq_input]
  exact
    jointHardInputBits_positive n

/-- Both candidate count and fuel are unbounded. -/
theorem jointHardFuel_unbounded :
    ∀ cap : Nat,
      ∃ n : Nat,
        cap <
          jointHardFuel n := by
  intro cap
  refine
    ⟨cap + 1, ?_⟩
  unfold jointHardFuel
  omega

theorem jointHardCandidateCount_unbounded :
    ∀ cap : Nat,
      ∃ n : Nat,
        cap <
          jointHardCandidateCount n := by
  intro cap
  refine
    ⟨cap, ?_⟩
  unfold
    jointHardCandidateCount
    jointHardInputBits
  exact
    Nat.lt_trans
      (Nat.lt_two_pow_self
        (n := cap))
      (Nat.pow_lt_pow_right
        Nat.one_lt_two
        (by omega))

/--
Finite syntax parameters leave a strict exponent gap for the chosen hard-family
index.
-/
theorem jointHard_exponent_gap
    (mass rank : Nat) :
    mass +
          (mass + rank + 4) *
            rank <
      (mass + rank + 5) *
        (mass + rank + 3) := by
  have massLtScale :
      mass <
        mass + rank + 4 := by
    omega
  have rankSuccLe :
      rank + 1 ≤
        mass + rank + 3 := by
    omega
  have rightPositive :
      0 < mass + rank + 3 := by
    omega
  calc
    mass +
          (mass + rank + 4) *
            rank
        <
      (mass + rank + 4) +
          (mass + rank + 4) *
            rank :=
        Nat.add_lt_add_right
          massLtScale
          ((mass + rank + 4) * rank)
    _ =
      (mass + rank + 4) *
        (rank + 1) := by
          rw [
            Nat.mul_add,
            Nat.mul_one,
            Nat.add_comm
          ]
    _ ≤
      (mass + rank + 4) *
        (mass + rank + 3) :=
          Nat.mul_le_mul_left
            (mass + rank + 4)
            rankSuccLe
    _ <
      (mass + rank + 5) *
        (mass + rank + 3) := by
          apply
            (Nat.mul_lt_mul_right
              rightPositive).2
          omega

/-- Any structural monomial majorant at a power-of-two input is a power of two. -/
theorem costPolynomialMajorant_le_twoPow
    (polynomial : CostPolynomial)
    (scale : Nat) :
    polynomial.majorantMass *
          (2 ^ scale) ^
            polynomial.majorantRank ≤
      2 ^
        (polynomial.majorantMass +
          scale *
            polynomial.majorantRank) := by
  have massLe :
      polynomial.majorantMass ≤
        2 ^ polynomial.majorantMass :=
    Nat.le_of_lt
      Nat.lt_two_pow_self
  calc
    polynomial.majorantMass *
          (2 ^ scale) ^
            polynomial.majorantRank
        ≤
      2 ^ polynomial.majorantMass *
        (2 ^ scale) ^
          polynomial.majorantRank :=
        Nat.mul_le_mul_right
          ((2 ^ scale) ^
            polynomial.majorantRank)
          massLe
    _ =
      2 ^
        (polynomial.majorantMass +
          scale *
            polynomial.majorantRank) := by
          rw [
            ← Nat.pow_mul,
            ← Nat.pow_add
          ]

/--
The primitive budget family with linear candidates and logarithmic fuel is not
input-polynomially bounded.
-/
theorem jointHardPrimitive_not_inputPolynomiallyBounded :
    ¬
      InputPolynomiallyBounded
        jointHardInputBits
        (fun n =>
          closurePrimitiveQueryBudget
            (jointHardCandidateCount n)
            (jointHardFuel n)) := by
  intro bounded
  rcases bounded with
    ⟨envelope, budgetLe⟩
  let witnessIndex :=
    envelope.majorantMass +
      envelope.majorantRank
  let scale :=
    witnessIndex + 4
  let candidate :=
    2 ^ scale
  have indexExact :
      witnessIndex =
        envelope.majorantMass +
          envelope.majorantRank := by
    rfl
  have scaleExact :
      scale =
        envelope.majorantMass +
          envelope.majorantRank +
          4 := by
    simp only [scale, witnessIndex]
  have inputExact :
      jointHardInputBits witnessIndex =
        candidate := by
    unfold
      jointHardInputBits
      candidate
      scale
    rfl
  have candidateExact :
      jointHardCandidateCount witnessIndex =
        candidate := by
    rw [
      jointHardCandidateCount_eq_input,
      inputExact
    ]
  have fuelExact :
      jointHardFuel witnessIndex =
        witnessIndex + 4 := by
    rfl
  have candidatePositive :
      0 < candidate := by
    unfold candidate
    exact
      Nat.pow_pos
        Nat.zero_lt_two
  have lower :=
    closurePrimitiveQueryBudget_doublePower_lt
      candidate
      candidatePositive
      (witnessIndex + 2)
  have lowerRewritten :
      2 ^
            ((witnessIndex + 5) *
              (witnessIndex + 3)) <
        closurePrimitiveQueryBudget
          (jointHardCandidateCount witnessIndex)
          (jointHardFuel witnessIndex) := by
    rw [
      candidateExact
    ]
    rw [
      fuelExact
    ]
    change
      2 ^
            ((witnessIndex + 5) *
              (witnessIndex + 3)) <
        closurePrimitiveQueryBudget
          candidate
          (witnessIndex + 4)
    have baseExact :
        candidate + candidate =
          2 ^ (witnessIndex + 5) := by
      calc
        candidate + candidate
            =
          candidate * 2 :=
            (Nat.mul_two candidate).symm
        _ =
          2 ^ (witnessIndex + 5) := by
            unfold candidate scale
            simpa [Nat.add_assoc] using
              (Nat.pow_succ
                2
                (witnessIndex + 4)).symm
    have lowerPowerExact :
        (candidate + candidate) ^
              (witnessIndex + 3) =
          2 ^
            ((witnessIndex + 5) *
              (witnessIndex + 3)) := by
      rw [baseExact]
      exact
        (Nat.pow_mul
          2
          (witnessIndex + 5)
          (witnessIndex + 3)).symm
    calc
      2 ^
            ((witnessIndex + 5) *
              (witnessIndex + 3))
          =
        (candidate + candidate) ^
          (witnessIndex + 3) :=
            lowerPowerExact.symm
      _ <
        closurePrimitiveQueryBudget
          candidate
          (witnessIndex + 4) := by
            simpa [Nat.add_assoc] using lower
      _ =
        closurePrimitiveQueryBudget
          (jointHardCandidateCount witnessIndex)
          (jointHardFuel witnessIndex) := by
            rw [
              candidateExact,
              fuelExact
            ]
  have inputPositive :
      1 ≤
        jointHardInputBits witnessIndex :=
    (Nat.succ_le_iff).2
      (jointHardInputBits_positive
        witnessIndex)
  have evalLeMajorant :=
    envelope.eval_le_majorant
      (jointHardInputBits witnessIndex)
      inputPositive
  have majorantLePower :
      envelope.majorantMass *
            (jointHardInputBits witnessIndex) ^
              envelope.majorantRank ≤
        2 ^
          (envelope.majorantMass +
            scale *
              envelope.majorantRank) := by
    rw [inputExact]
    exact
      costPolynomialMajorant_le_twoPow
        envelope
        scale
  have exponentGap :
      envelope.majorantMass +
            scale *
              envelope.majorantRank <
        (witnessIndex + 5) *
          (witnessIndex + 3) := by
    rw [
      scaleExact,
      indexExact
    ]
    exact
      jointHard_exponent_gap
        envelope.majorantMass
        envelope.majorantRank
  have majorantLtLower :
      envelope.majorantMass *
            (jointHardInputBits witnessIndex) ^
              envelope.majorantRank <
        2 ^
          ((witnessIndex + 5) *
            (witnessIndex + 3)) :=
    Nat.lt_of_le_of_lt
      majorantLePower
      (Nat.pow_lt_pow_right
        Nat.one_lt_two
        exponentGap)
  have evalLtBudget :
      envelope.eval
            (jointHardInputBits witnessIndex) <
        closurePrimitiveQueryBudget
          (jointHardCandidateCount witnessIndex)
          (jointHardFuel witnessIndex) :=
    Nat.lt_of_le_of_lt
      evalLeMajorant
      (Nat.lt_trans
        majorantLtLower
        lowerRewritten)
  have impossible :
      closurePrimitiveQueryBudget
            (jointHardCandidateCount witnessIndex)
            (jointHardFuel witnessIndex) <
        closurePrimitiveQueryBudget
          (jointHardCandidateCount witnessIndex)
          (jointHardFuel witnessIndex) :=
    Nat.lt_of_le_of_lt
      (budgetLe witnessIndex)
      evalLtBudget
  exact
    (Nat.lt_irrefl _)
      impossible

/--
The composition-candidate budget is also non-polynomial on the same joint
family because it pointwise dominates the primitive-query budget.
-/
theorem jointHardComposition_not_inputPolynomiallyBounded :
    ¬
      InputPolynomiallyBounded
        jointHardInputBits
        (fun n =>
          closureCompositionCandidateBudget
            (jointHardCandidateCount n)
            (jointHardFuel n)) := by
  intro bounded
  rcases bounded with
    ⟨envelope, compositionLe⟩
  have primitiveBounded :
      InputPolynomiallyBounded
        jointHardInputBits
        (fun n =>
          closurePrimitiveQueryBudget
            (jointHardCandidateCount n)
            (jointHardFuel n)) := by
    refine
      ⟨envelope, ?_⟩
    intro n
    exact
      Nat.le_trans
        (closurePrimitiveQueryBudget_le_composition
          (jointHardCandidateCount n)
          (jointHardCandidateCount_positive n)
          (jointHardFuel n))
        (compositionLe n)
  exact
    jointHardPrimitive_not_inputPolynomiallyBounded
      primitiveBounded

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.closurePrimitiveQueryBudget_doublePower_lt
#print axioms ConstitutiveSearch.closurePrimitiveQueryBudget_le_composition
#print axioms ConstitutiveSearch.jointHardInputBits
#print axioms ConstitutiveSearch.jointHardCandidateCount
#print axioms ConstitutiveSearch.jointHardFuel
#print axioms ConstitutiveSearch.jointHardCandidateCount_eq_input
#print axioms ConstitutiveSearch.jointHardFuel_eq_log2Input
#print axioms ConstitutiveSearch.jointHardInputBits_positive
#print axioms ConstitutiveSearch.jointHardCandidateCount_positive
#print axioms ConstitutiveSearch.jointHardFuel_unbounded
#print axioms ConstitutiveSearch.jointHardCandidateCount_unbounded
#print axioms ConstitutiveSearch.jointHard_exponent_gap
#print axioms ConstitutiveSearch.costPolynomialMajorant_le_twoPow
#print axioms ConstitutiveSearch.jointHardPrimitive_not_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.jointHardComposition_not_inputPolynomiallyBounded
/- AXIOM_AUDIT_END -/
