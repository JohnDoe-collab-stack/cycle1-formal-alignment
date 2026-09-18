import Init.Omega
import ConstitutiveSearch.ClosureSearchScaledLogFuelPolynomial

/-!
# Bounded-candidate logarithmic closure regime

The one-candidate logarithmic results extend to any uniformly bounded candidate
list.

For candidate count m, both recursive source-level closure budgets admit the
common geometric envelope

  (2*m + 2)^fuel.

Consequently, if candidateCount <= M for one fixed cap M and

  fuel <= c * log2(inputBits),

then both budgets, and the actual executable closure counters they bound, admit
the explicit polynomial envelope

  inputBits ^ ((2*M + 2) * c).

This is a sufficient regime for the current ClosureSearch engine.  It does not
claim polynomiality when the candidate cap itself grows with input.
-/

namespace ConstitutiveSearch

/-- Common geometric base used to dominate both closure counters. -/
def closureGeometricBase
    (candidateCount : Nat) : Nat :=
  candidateCount +
    candidateCount +
    2

/-- Explicit polynomial degree induced by a candidate cap and logarithmic factor. -/
def closureBoundedCandidateLogDegree
    (candidateCap factor : Nat) : Nat :=
  closureGeometricBase candidateCap *
    factor

/--
Primitive-query budget plus one is bounded by the geometric envelope
(2*m+2)^fuel.
-/
theorem closurePrimitiveQueryBudget_add_one_le_geometric
    (candidateCount : Nat) :
    ∀ fuel : Nat,
      closurePrimitiveQueryBudget
            candidateCount
            fuel +
          1 ≤
        closureGeometricBase
            candidateCount ^
          fuel := by
  intro fuel
  induction fuel with
  | zero =>
      rfl
  | succ fuel inductionHypothesis =>
      let recursive :=
        closurePrimitiveQueryBudget
          candidateCount
          fuel
      let base :=
        closureGeometricBase
          candidateCount
      have coefficientLe :
          candidateCount +
              candidateCount ≤
            base := by
        unfold base closureGeometricBase
        omega
      have twoLeBase :
          2 ≤ base := by
        unfold base closureGeometricBase
        omega
      have recursivePartLe :
          candidateCount *
              (recursive + recursive) ≤
            base * recursive := by
        calc
          candidateCount *
                (recursive + recursive)
              =
            (candidateCount +
                candidateCount) *
              recursive := by
                rw [
                  Nat.mul_add,
                  Nat.add_mul
                ]
          _ ≤
            base * recursive :=
              Nat.mul_le_mul_right
                recursive
                coefficientLe
      have stepLe :
          candidateCount *
                (recursive + recursive) +
              2 ≤
            base *
              (recursive + 1) := by
        calc
          candidateCount *
                (recursive + recursive) +
              2
              ≤
            base * recursive +
              base :=
                Nat.add_le_add
                  recursivePartLe
                  twoLeBase
          _ =
            base *
              (recursive + 1) := by
                rw [
                  Nat.mul_add,
                  Nat.mul_one
                ]
      have liftedInduction :
          base *
              (recursive + 1) ≤
            base *
              (base ^ fuel) :=
        Nat.mul_le_mul_left
          base
          inductionHypothesis
      rw [show
        closurePrimitiveQueryBudget
            candidateCount
            (fuel + 1) =
          viaPrimitiveQueryBudget
              recursive
              candidateCount +
            1 from rfl]
      rw [
        viaPrimitiveQueryBudget_closed
      ]
      change
        candidateCount *
              (recursive + recursive) +
            1 +
            1 ≤
          base ^ (fuel + 1)
      calc
        candidateCount *
              (recursive + recursive) +
            1 +
            1
            =
          candidateCount *
                (recursive + recursive) +
              2 := by
                omega
        _ ≤
          base *
            (recursive + 1) :=
              stepLe
        _ ≤
          base *
            (base ^ fuel) :=
              liftedInduction
        _ =
          base ^ (fuel + 1) := by
            rw [
              Nat.pow_succ,
              Nat.mul_comm
            ]

/--
Composition-candidate budget plus one satisfies the same geometric envelope.
-/
theorem closureCompositionCandidateBudget_add_one_le_geometric
    (candidateCount : Nat) :
    ∀ fuel : Nat,
      closureCompositionCandidateBudget
            candidateCount
            fuel +
          1 ≤
        closureGeometricBase
            candidateCount ^
          fuel := by
  intro fuel
  induction fuel with
  | zero =>
      rfl
  | succ fuel inductionHypothesis =>
      let recursive :=
        closureCompositionCandidateBudget
          candidateCount
          fuel
      let base :=
        closureGeometricBase
          candidateCount
      have coefficientLe :
          candidateCount +
              candidateCount ≤
            base := by
        unfold base closureGeometricBase
        omega
      have tailLe :
          candidateCount + 1 ≤
            base := by
        unfold base closureGeometricBase
        omega
      have recursivePartLe :
          (candidateCount +
              candidateCount) *
              recursive ≤
            base * recursive :=
        Nat.mul_le_mul_right
          recursive
          coefficientLe
      have expanded :
          candidateCount *
                (recursive +
                  recursive +
                  1) =
            (candidateCount +
                candidateCount) *
                recursive +
              candidateCount := by
        rw [
          Nat.mul_add,
          Nat.mul_add,
          Nat.mul_one,
          Nat.add_mul
        ]
        omega
      have stepLe :
          candidateCount *
                (recursive +
                  recursive +
                  1) +
              1 ≤
            base *
              (recursive + 1) := by
        rw [expanded]
        calc
          (candidateCount +
                candidateCount) *
                recursive +
              candidateCount +
              1
              =
            (candidateCount +
                candidateCount) *
                recursive +
              (candidateCount + 1) := by
                omega
          _ ≤
            base * recursive +
              base :=
                Nat.add_le_add
                  recursivePartLe
                  tailLe
          _ =
            base *
              (recursive + 1) := by
                rw [
                  Nat.mul_add,
                  Nat.mul_one
                ]
      have liftedInduction :
          base *
              (recursive + 1) ≤
            base *
              (base ^ fuel) :=
        Nat.mul_le_mul_left
          base
          inductionHypothesis
      rw [show
        closureCompositionCandidateBudget
            candidateCount
            (fuel + 1) =
          viaCompositionCandidateBudget
            recursive
            candidateCount from rfl]
      rw [
        viaCompositionCandidateBudget_closed
      ]
      change
        candidateCount *
              (recursive +
                recursive +
                1) +
            1 ≤
          base ^ (fuel + 1)
      calc
        candidateCount *
              (recursive +
                recursive +
                1) +
            1
            ≤
          base *
            (recursive + 1) :=
              stepLe
        _ ≤
          base *
            (base ^ fuel) :=
              liftedInduction
        _ =
          base ^ (fuel + 1) := by
            rw [
              Nat.pow_succ,
              Nat.mul_comm
            ]

/-- Candidate-count monotonicity of the geometric base. -/
theorem closureGeometricBase_mono
    {small large : Nat}
    (smallLe :
      small ≤ large) :
    closureGeometricBase small ≤
      closureGeometricBase large := by
  unfold closureGeometricBase
  omega

/--
Under a fixed candidate cap, primitive budget plus one is bounded by the capped
geometric base raised to the actual fuel.
-/
theorem closurePrimitiveQueryBudget_add_one_le_cappedGeometric
    (candidateCount fuel candidateCap : Nat)
    (candidateLe :
      candidateCount ≤ candidateCap) :
    closurePrimitiveQueryBudget
          candidateCount
          fuel +
        1 ≤
      closureGeometricBase
          candidateCap ^
        fuel := by
  exact
    Nat.le_trans
      (closurePrimitiveQueryBudget_add_one_le_geometric
        candidateCount
        fuel)
      (Nat.pow_le_pow_left
        (closureGeometricBase_mono
          candidateLe)
        fuel)

/--
The composition budget satisfies the same capped geometric envelope.
-/
theorem closureCompositionCandidateBudget_add_one_le_cappedGeometric
    (candidateCount fuel candidateCap : Nat)
    (candidateLe :
      candidateCount ≤ candidateCap) :
    closureCompositionCandidateBudget
          candidateCount
          fuel +
        1 ≤
      closureGeometricBase
          candidateCap ^
        fuel := by
  exact
    Nat.le_trans
      (closureCompositionCandidateBudget_add_one_le_geometric
        candidateCount
        fuel)
      (Nat.pow_le_pow_left
        (closureGeometricBase_mono
          candidateLe)
        fuel)

/--
The capped geometric envelope is polynomial in inputBits whenever fuel is at
most factor*log2(inputBits).
-/
theorem closureCappedGeometric_scaledLog_le_inputPower
    (inputBits fuel : Nat → Nat)
    (candidateCap factor : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (fuelLeScaledLog :
      ∀ n : Nat,
        fuel n ≤
          factor *
            Nat.log2 (inputBits n)) :
    ∀ n : Nat,
      closureGeometricBase
            candidateCap ^
          fuel n ≤
        (inputBits n) ^
          closureBoundedCandidateLogDegree
            candidateCap
            factor := by
  intro n
  let base :=
    closureGeometricBase
      candidateCap
  let degree :=
    closureBoundedCandidateLogDegree
      candidateCap
      factor
  have baseLeTwoPower :
      base ≤
        2 ^ base :=
    Nat.le_of_lt
      Nat.lt_two_pow_self
  have basePowerLe :
      base ^ fuel n ≤
        (2 ^ base) ^ fuel n :=
    Nat.pow_le_pow_left
      baseLeTwoPower
      (fuel n)
  have exponentLe :
      base * fuel n ≤
        base *
          (factor *
            Nat.log2 (inputBits n)) :=
    Nat.mul_le_mul_left
      base
      (fuelLeScaledLog n)
  have twoPowerExponentLe :
      2 ^ (base * fuel n) ≤
        2 ^
          (base *
            (factor *
              Nat.log2 (inputBits n))) :=
    Nat.pow_le_pow_right
      Nat.zero_lt_two
      exponentLe
  have logPowerLe :
      2 ^ Nat.log2 (inputBits n) ≤
        inputBits n :=
    Nat.log2_self_le
      (Nat.ne_of_gt
        (inputPositive n))
  have finalPowerLe :
      (2 ^ Nat.log2 (inputBits n)) ^
            (base * factor) ≤
        (inputBits n) ^
            (base * factor) :=
    Nat.pow_le_pow_left
      logPowerLe
      (base * factor)
  calc
    closureGeometricBase
          candidateCap ^
        fuel n
        =
      base ^ fuel n := by
        rfl
    _ ≤
      (2 ^ base) ^ fuel n :=
        basePowerLe
    _ =
      2 ^ (base * fuel n) := by
        rw [
          Nat.pow_mul
        ]
    _ ≤
      2 ^
        (base *
          (factor *
            Nat.log2 (inputBits n))) :=
        twoPowerExponentLe
    _ =
      (2 ^ Nat.log2 (inputBits n)) ^
        (base * factor) := by
          have exponentExact :
              base *
                  (factor *
                    Nat.log2 (inputBits n)) =
                Nat.log2 (inputBits n) *
                  (base * factor) := by
            ac_rfl
          rw [
            exponentExact,
            Nat.pow_mul
          ]
    _ ≤
      (inputBits n) ^
        (base * factor) :=
          finalPowerLe
    _ =
      (inputBits n) ^ degree := by
        rfl

/--
Primitive budget is polynomial when candidate count is uniformly capped and
fuel is constant-factor logarithmic.
-/
theorem closurePrimitiveBoundedCandidates_scaledLogFuel_le_inputPower
    (inputBits candidateCount fuel : Nat → Nat)
    (candidateCap factor : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (candidateLe :
      ∀ n : Nat,
        candidateCount n ≤
          candidateCap)
    (fuelLeScaledLog :
      ∀ n : Nat,
        fuel n ≤
          factor *
            Nat.log2 (inputBits n)) :
    ∀ n : Nat,
      closurePrimitiveQueryBudget
          (candidateCount n)
          (fuel n) ≤
        (inputBits n) ^
          closureBoundedCandidateLogDegree
            candidateCap
            factor := by
  intro n
  have plusOneLe :
      closurePrimitiveQueryBudget
            (candidateCount n)
            (fuel n) +
          1 ≤
        closureGeometricBase
            candidateCap ^
          fuel n :=
    closurePrimitiveQueryBudget_add_one_le_cappedGeometric
      (candidateCount n)
      (fuel n)
      candidateCap
      (candidateLe n)
  have geometricLe :=
    closureCappedGeometric_scaledLog_le_inputPower
      inputBits
      fuel
      candidateCap
      factor
      inputPositive
      fuelLeScaledLog
      n
  exact
    Nat.le_trans
      (Nat.le_add_right
        (closurePrimitiveQueryBudget
          (candidateCount n)
          (fuel n))
        1)
      (Nat.le_trans
        plusOneLe
        geometricLe)

/--
Composition budget satisfies the same polynomial regime.
-/
theorem closureCompositionBoundedCandidates_scaledLogFuel_le_inputPower
    (inputBits candidateCount fuel : Nat → Nat)
    (candidateCap factor : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (candidateLe :
      ∀ n : Nat,
        candidateCount n ≤
          candidateCap)
    (fuelLeScaledLog :
      ∀ n : Nat,
        fuel n ≤
          factor *
            Nat.log2 (inputBits n)) :
    ∀ n : Nat,
      closureCompositionCandidateBudget
          (candidateCount n)
          (fuel n) ≤
        (inputBits n) ^
          closureBoundedCandidateLogDegree
            candidateCap
            factor := by
  intro n
  have plusOneLe :
      closureCompositionCandidateBudget
            (candidateCount n)
            (fuel n) +
          1 ≤
        closureGeometricBase
            candidateCap ^
          fuel n :=
    closureCompositionCandidateBudget_add_one_le_cappedGeometric
      (candidateCount n)
      (fuel n)
      candidateCap
      (candidateLe n)
  have geometricLe :=
    closureCappedGeometric_scaledLog_le_inputPower
      inputBits
      fuel
      candidateCap
      factor
      inputPositive
      fuelLeScaledLog
      n
  exact
    Nat.le_trans
      (Nat.le_add_right
        (closureCompositionCandidateBudget
          (candidateCount n)
          (fuel n))
        1)
      (Nat.le_trans
        plusOneLe
        geometricLe)

/-- Primitive budget packaged in the internal input-polynomial interface. -/
theorem closurePrimitiveBoundedCandidates_scaledLogFuel_inputPolynomiallyBounded
    (inputBits candidateCount fuel : Nat → Nat)
    (candidateCap factor : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (candidateLe :
      ∀ n : Nat,
        candidateCount n ≤
          candidateCap)
    (fuelLeScaledLog :
      ∀ n : Nat,
        fuel n ≤
          factor *
            Nat.log2 (inputBits n)) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        closurePrimitiveQueryBudget
          (candidateCount n)
          (fuel n)) :=
  ⟨CostPolynomial.inputPower
      (closureBoundedCandidateLogDegree
        candidateCap
        factor),
    fun n => by
      rw [
        CostPolynomial.eval_inputPower
      ]
      exact
        closurePrimitiveBoundedCandidates_scaledLogFuel_le_inputPower
          inputBits
          candidateCount
          fuel
          candidateCap
          factor
          inputPositive
          candidateLe
          fuelLeScaledLog
          n⟩

/-- Composition budget packaged in the same input-polynomial interface. -/
theorem closureCompositionBoundedCandidates_scaledLogFuel_inputPolynomiallyBounded
    (inputBits candidateCount fuel : Nat → Nat)
    (candidateCap factor : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (candidateLe :
      ∀ n : Nat,
        candidateCount n ≤
          candidateCap)
    (fuelLeScaledLog :
      ∀ n : Nat,
        fuel n ≤
          factor *
            Nat.log2 (inputBits n)) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        closureCompositionCandidateBudget
          (candidateCount n)
          (fuel n)) :=
  ⟨CostPolynomial.inputPower
      (closureBoundedCandidateLogDegree
        candidateCap
        factor),
    fun n => by
      rw [
        CostPolynomial.eval_inputPower
      ]
      exact
        closureCompositionBoundedCandidates_scaledLogFuel_le_inputPower
          inputBits
          candidateCount
          fuel
          candidateCap
          factor
          inputPositive
          candidateLe
          fuelLeScaledLog
          n⟩

/--
Actual executable primitive-query counts inherit the bounded-candidate,
scaled-logarithmic polynomial envelope.
-/
theorem searchTransportClosureBoundedCandidates_scaledLogFuel_primitiveQueries
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type}
    (primitive :
      (n : Nat) →
        RelationSearch (Generator n))
    (candidates :
      (n : Nat) →
        List (State n))
    (fuel inputBits : Nat → Nat)
    (candidateCap factor : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (candidateLe :
      ∀ n : Nat,
        (candidates n).length ≤
          candidateCap)
    (fuelLeScaledLog :
      ∀ n : Nat,
        fuel n ≤
          factor *
            Nat.log2 (inputBits n))
    (source target :
      (n : Nat) →
        State n) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (searchTransportClosureBounded
          (primitive n)
          (candidates n)
          (fuel n)
          (source n)
          (target n)).stats.primitiveQueries) := by
  rcases
      closurePrimitiveBoundedCandidates_scaledLogFuel_inputPolynomiallyBounded
        inputBits
        (fun n =>
          (candidates n).length)
        fuel
        candidateCap
        factor
        inputPositive
        candidateLe
        fuelLeScaledLog with
    ⟨envelope, budgetLe⟩
  refine
    ⟨envelope, ?_⟩
  intro n
  exact
    Nat.le_trans
      (searchTransportClosureBounded_primitiveQueries_le
        (primitive n)
        (candidates n)
        (fuel n)
        (source n)
        (target n))
      (budgetLe n)

/--
Actual executable composition-candidate counts inherit the same envelope.
-/
theorem searchTransportClosureBoundedCandidates_scaledLogFuel_compositionCandidates
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type}
    (primitive :
      (n : Nat) →
        RelationSearch (Generator n))
    (candidates :
      (n : Nat) →
        List (State n))
    (fuel inputBits : Nat → Nat)
    (candidateCap factor : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (candidateLe :
      ∀ n : Nat,
        (candidates n).length ≤
          candidateCap)
    (fuelLeScaledLog :
      ∀ n : Nat,
        fuel n ≤
          factor *
            Nat.log2 (inputBits n))
    (source target :
      (n : Nat) →
        State n) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (searchTransportClosureBounded
          (primitive n)
          (candidates n)
          (fuel n)
          (source n)
          (target n)).stats.compositionCandidates) := by
  rcases
      closureCompositionBoundedCandidates_scaledLogFuel_inputPolynomiallyBounded
        inputBits
        (fun n =>
          (candidates n).length)
        fuel
        candidateCap
        factor
        inputPositive
        candidateLe
        fuelLeScaledLog with
    ⟨envelope, budgetLe⟩
  refine
    ⟨envelope, ?_⟩
  intro n
  exact
    Nat.le_trans
      (searchTransportClosureBounded_compositionCandidates_le
        (primitive n)
        (candidates n)
        (fuel n)
        (source n)
        (target n))
      (budgetLe n)

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.closureGeometricBase
#print axioms ConstitutiveSearch.closureBoundedCandidateLogDegree
#print axioms ConstitutiveSearch.closurePrimitiveQueryBudget_add_one_le_geometric
#print axioms ConstitutiveSearch.closureCompositionCandidateBudget_add_one_le_geometric
#print axioms ConstitutiveSearch.closureGeometricBase_mono
#print axioms ConstitutiveSearch.closurePrimitiveQueryBudget_add_one_le_cappedGeometric
#print axioms ConstitutiveSearch.closureCompositionCandidateBudget_add_one_le_cappedGeometric
#print axioms ConstitutiveSearch.closureCappedGeometric_scaledLog_le_inputPower
#print axioms ConstitutiveSearch.closurePrimitiveBoundedCandidates_scaledLogFuel_le_inputPower
#print axioms ConstitutiveSearch.closureCompositionBoundedCandidates_scaledLogFuel_le_inputPower
#print axioms ConstitutiveSearch.closurePrimitiveBoundedCandidates_scaledLogFuel_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.closureCompositionBoundedCandidates_scaledLogFuel_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.searchTransportClosureBoundedCandidates_scaledLogFuel_primitiveQueries
#print axioms ConstitutiveSearch.searchTransportClosureBoundedCandidates_scaledLogFuel_compositionCandidates
/- AXIOM_AUDIT_END -/
