import Init.Omega
import ConstitutiveSearch.ClosureSearchBoundedCandidatesLogFuelPolynomial

/-!
# Joint candidate/fuel growth regime for closure search

The previous closure theorems isolate two polynomial regimes:
* polynomially many candidates with fixed fuel;
* uniformly bounded candidates with logarithmic fuel.

This module gives one joint sufficient condition in which both quantities may
vary with the concrete input size.

For candidate count m, the generic geometric envelope is

  closureGeometricBase m ^ fuel.

The base is bounded by one power of two using its binary width

  log2(closureGeometricBase m) + 1.

Hence, if for one fixed degree d,

  (log2(closureGeometricBase(candidateCount)) + 1) * fuel
    <= d * log2(inputBits),

then both closure budgets are bounded by inputBits^d.

A concrete witness family is also supplied where candidateCount and fuel are
both unbounded, yet the combined criterion holds with degree one.  Thus
"candidate count unbounded" plus "fuel unbounded" is not by itself a
non-polynomiality criterion; their joint growth relative to input size matters.
-/

namespace ConstitutiveSearch

/-- Binary width of the geometric base induced by one candidate count. -/
def closureCandidateBitWidth
    (candidateCount : Nat) : Nat :=
  Nat.log2
      (closureGeometricBase candidateCount) +
    1

/-- The geometric base fits below the power of two determined by its bit width. -/
theorem closureGeometricBase_le_twoPowCandidateBitWidth
    (candidateCount : Nat) :
    closureGeometricBase candidateCount ≤
      2 ^ closureCandidateBitWidth candidateCount := by
  unfold closureCandidateBitWidth
  exact
    Nat.le_of_lt
      (Nat.lt_log2_self
        (n := closureGeometricBase candidateCount))

/--
Joint logarithmic growth criterion for the geometric closure envelope.

The condition allows both candidate count and fuel to vary, provided their
combined binary growth remains within one fixed polynomial degree.
-/
theorem closureGeometric_jointGrowth_le_inputPower
    (inputBits candidateCount fuel : Nat → Nat)
    (degree : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (jointLe :
      ∀ n : Nat,
        closureCandidateBitWidth
              (candidateCount n) *
            fuel n ≤
          degree *
            Nat.log2 (inputBits n)) :
    ∀ n : Nat,
      closureGeometricBase
            (candidateCount n) ^
          fuel n ≤
        (inputBits n) ^ degree := by
  intro n
  let base :=
    closureGeometricBase
      (candidateCount n)
  let width :=
    closureCandidateBitWidth
      (candidateCount n)
  have baseLe :
      base ≤
        2 ^ width := by
    simpa only [base, width] using
      closureGeometricBase_le_twoPowCandidateBitWidth
        (candidateCount n)
  have basePowerLe :
      base ^ fuel n ≤
        (2 ^ width) ^ fuel n :=
    Nat.pow_le_pow_left
      baseLe
      (fuel n)
  have exponentLe :
      width * fuel n ≤
        degree *
          Nat.log2 (inputBits n) := by
    simpa only [width] using
      jointLe n
  have twoPowerLe :
      2 ^ (width * fuel n) ≤
        2 ^
          (degree *
            Nat.log2 (inputBits n)) :=
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
      (2 ^ Nat.log2 (inputBits n)) ^ degree ≤
        (inputBits n) ^ degree :=
    Nat.pow_le_pow_left
      logPowerLe
      degree
  calc
    closureGeometricBase
          (candidateCount n) ^
        fuel n
        =
      base ^ fuel n := by
        rfl
    _ ≤
      (2 ^ width) ^ fuel n :=
        basePowerLe
    _ =
      2 ^ (width * fuel n) := by
        rw [Nat.pow_mul]
    _ ≤
      2 ^
        (degree *
          Nat.log2 (inputBits n)) :=
        twoPowerLe
    _ =
      (2 ^ Nat.log2 (inputBits n)) ^ degree := by
        have exponentExact :
            degree *
                Nat.log2 (inputBits n) =
              Nat.log2 (inputBits n) *
                degree := by
          exact Nat.mul_comm _ _
        rw [
          exponentExact,
          Nat.pow_mul
        ]
    _ ≤
      (inputBits n) ^ degree :=
        finalPowerLe

/--
Primitive-query budget inherits the joint-growth polynomial envelope.
-/
theorem closurePrimitive_jointGrowth_le_inputPower
    (inputBits candidateCount fuel : Nat → Nat)
    (degree : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (jointLe :
      ∀ n : Nat,
        closureCandidateBitWidth
              (candidateCount n) *
            fuel n ≤
          degree *
            Nat.log2 (inputBits n)) :
    ∀ n : Nat,
      closurePrimitiveQueryBudget
          (candidateCount n)
          (fuel n) ≤
        (inputBits n) ^ degree := by
  intro n
  have plusOneLe :=
    closurePrimitiveQueryBudget_add_one_le_geometric
      (candidateCount n)
      (fuel n)
  have geometricLe :=
    closureGeometric_jointGrowth_le_inputPower
      inputBits
      candidateCount
      fuel
      degree
      inputPositive
      jointLe
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
Composition-candidate budget satisfies the same joint-growth envelope.
-/
theorem closureComposition_jointGrowth_le_inputPower
    (inputBits candidateCount fuel : Nat → Nat)
    (degree : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (jointLe :
      ∀ n : Nat,
        closureCandidateBitWidth
              (candidateCount n) *
            fuel n ≤
          degree *
            Nat.log2 (inputBits n)) :
    ∀ n : Nat,
      closureCompositionCandidateBudget
          (candidateCount n)
          (fuel n) ≤
        (inputBits n) ^ degree := by
  intro n
  have plusOneLe :=
    closureCompositionCandidateBudget_add_one_le_geometric
      (candidateCount n)
      (fuel n)
  have geometricLe :=
    closureGeometric_jointGrowth_le_inputPower
      inputBits
      candidateCount
      fuel
      degree
      inputPositive
      jointLe
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
theorem closurePrimitive_jointGrowth_inputPolynomiallyBounded
    (inputBits candidateCount fuel : Nat → Nat)
    (degree : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (jointLe :
      ∀ n : Nat,
        closureCandidateBitWidth
              (candidateCount n) *
            fuel n ≤
          degree *
            Nat.log2 (inputBits n)) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        closurePrimitiveQueryBudget
          (candidateCount n)
          (fuel n)) :=
  ⟨CostPolynomial.inputPower degree,
    fun n => by
      rw [CostPolynomial.eval_inputPower]
      exact
        closurePrimitive_jointGrowth_le_inputPower
          inputBits
          candidateCount
          fuel
          degree
          inputPositive
          jointLe
          n⟩

/-- Composition budget packaged in the same internal interface. -/
theorem closureComposition_jointGrowth_inputPolynomiallyBounded
    (inputBits candidateCount fuel : Nat → Nat)
    (degree : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (jointLe :
      ∀ n : Nat,
        closureCandidateBitWidth
              (candidateCount n) *
            fuel n ≤
          degree *
            Nat.log2 (inputBits n)) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        closureCompositionCandidateBudget
          (candidateCount n)
          (fuel n)) :=
  ⟨CostPolynomial.inputPower degree,
    fun n => by
      rw [CostPolynomial.eval_inputPower]
      exact
        closureComposition_jointGrowth_le_inputPower
          inputBits
          candidateCount
          fuel
          degree
          inputPositive
          jointLe
          n⟩

/--
Actual executable primitive-query counts inherit the same joint-growth
criterion.
-/
theorem searchTransportClosure_jointGrowth_primitiveQueries
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
    (degree : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (jointLe :
      ∀ n : Nat,
        closureCandidateBitWidth
              ((candidates n).length) *
            fuel n ≤
          degree *
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
      closurePrimitive_jointGrowth_inputPolynomiallyBounded
        inputBits
        (fun n =>
          (candidates n).length)
        fuel
        degree
        inputPositive
        jointLe with
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
Actual executable composition-candidate counts inherit the same criterion.
-/
theorem searchTransportClosure_jointGrowth_compositionCandidates
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
    (degree : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (jointLe :
      ∀ n : Nat,
        closureCandidateBitWidth
              ((candidates n).length) *
            fuel n ≤
          degree *
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
      closureComposition_jointGrowth_inputPolynomiallyBounded
        inputBits
        (fun n =>
          (candidates n).length)
        fuel
        degree
        inputPositive
        jointLe with
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

/-! ## Explicit jointly-unbounded witness -/

/--
Candidate count 2^n - 1.  This is unbounded while making the geometric base an
exact power of two.
-/
def jointGrowingCandidateCount
    (n : Nat) : Nat :=
  2 ^ n - 1

/-- Fuel grows linearly with the family index. -/
def jointGrowingFuel
    (n : Nat) : Nat :=
  n

/--
Concrete input size grows as 2^((n+2)^2), leaving exactly enough logarithmic
room for both candidate width and fuel to grow.
-/
def jointGrowingInputBits
    (n : Nat) : Nat :=
  2 ^ ((n + 2) * (n + 2))

/-- The witness geometric base is exactly 2^(n+1). -/
theorem jointGrowing_geometricBase
    (n : Nat) :
    closureGeometricBase
        (jointGrowingCandidateCount n) =
      2 ^ (n + 1) := by
  unfold
    jointGrowingCandidateCount
    closureGeometricBase
  have powerPositive :
      0 < 2 ^ n :=
    Nat.pow_pos
      Nat.zero_lt_two
  rw [Nat.pow_succ]
  omega

/-- Its candidate bit width is exactly n+2. -/
theorem jointGrowing_candidateBitWidth
    (n : Nat) :
    closureCandidateBitWidth
        (jointGrowingCandidateCount n) =
      n + 2 := by
  unfold closureCandidateBitWidth
  rw [
    jointGrowing_geometricBase,
    Nat.log2_two_pow
  ]

/-- The logarithm of the concrete input size is exactly (n+2)^2. -/
theorem jointGrowing_inputLog
    (n : Nat) :
    Nat.log2 (jointGrowingInputBits n) =
      (n + 2) * (n + 2) := by
  unfold jointGrowingInputBits
  rw [Nat.log2_two_pow]

/-- The witness input is always positive. -/
theorem jointGrowing_inputPositive
    (n : Nat) :
    0 < jointGrowingInputBits n := by
  unfold jointGrowingInputBits
  exact
    Nat.pow_pos
      Nat.zero_lt_two

/--
The combined candidate-width/fuel charge fits under one copy of log2(input).
-/
theorem jointGrowing_jointLe
    (n : Nat) :
    closureCandidateBitWidth
          (jointGrowingCandidateCount n) *
        jointGrowingFuel n ≤
      1 *
        Nat.log2 (jointGrowingInputBits n) := by
  rw [
    jointGrowing_candidateBitWidth,
    jointGrowing_inputLog
  ]
  unfold jointGrowingFuel
  rw [Nat.one_mul]
  exact
    Nat.mul_le_mul_left
      (n + 2)
      (Nat.le_add_right n 2)

/-- Candidate count itself is unbounded. -/
theorem jointGrowingCandidateCount_unbounded :
    ∀ cap : Nat,
      ∃ n : Nat,
        cap <
          jointGrowingCandidateCount n := by
  intro cap
  refine
    ⟨cap + 2, ?_⟩
  unfold jointGrowingCandidateCount
  have powerLt :
      cap + 2 <
        2 ^ (cap + 2) :=
    Nat.lt_two_pow_self
  omega

/-- Fuel is unbounded as well. -/
theorem jointGrowingFuel_unbounded :
    ∀ cap : Nat,
      ∃ n : Nat,
        cap <
          jointGrowingFuel n := by
  intro cap
  exact
    ⟨cap + 1,
      Nat.lt_succ_self cap⟩

/--
Despite both coordinates being unbounded, the primitive closure budget is
linear in the concrete input-size coordinate.
-/
theorem jointGrowingPrimitive_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      jointGrowingInputBits
      (fun n =>
        closurePrimitiveQueryBudget
          (jointGrowingCandidateCount n)
          (jointGrowingFuel n)) :=
  closurePrimitive_jointGrowth_inputPolynomiallyBounded
    jointGrowingInputBits
    jointGrowingCandidateCount
    jointGrowingFuel
    1
    jointGrowing_inputPositive
    jointGrowing_jointLe

/--
The composition-candidate budget is linear in the same concrete input size.
-/
theorem jointGrowingComposition_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      jointGrowingInputBits
      (fun n =>
        closureCompositionCandidateBudget
          (jointGrowingCandidateCount n)
          (jointGrowingFuel n)) :=
  closureComposition_jointGrowth_inputPolynomiallyBounded
    jointGrowingInputBits
    jointGrowingCandidateCount
    jointGrowingFuel
    1
    jointGrowing_inputPositive
    jointGrowing_jointLe

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.closureCandidateBitWidth
#print axioms ConstitutiveSearch.closureGeometricBase_le_twoPowCandidateBitWidth
#print axioms ConstitutiveSearch.closureGeometric_jointGrowth_le_inputPower
#print axioms ConstitutiveSearch.closurePrimitive_jointGrowth_le_inputPower
#print axioms ConstitutiveSearch.closureComposition_jointGrowth_le_inputPower
#print axioms ConstitutiveSearch.closurePrimitive_jointGrowth_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.closureComposition_jointGrowth_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.searchTransportClosure_jointGrowth_primitiveQueries
#print axioms ConstitutiveSearch.searchTransportClosure_jointGrowth_compositionCandidates
#print axioms ConstitutiveSearch.jointGrowingCandidateCount
#print axioms ConstitutiveSearch.jointGrowingFuel
#print axioms ConstitutiveSearch.jointGrowingInputBits
#print axioms ConstitutiveSearch.jointGrowing_geometricBase
#print axioms ConstitutiveSearch.jointGrowing_candidateBitWidth
#print axioms ConstitutiveSearch.jointGrowing_inputLog
#print axioms ConstitutiveSearch.jointGrowing_inputPositive
#print axioms ConstitutiveSearch.jointGrowing_jointLe
#print axioms ConstitutiveSearch.jointGrowingCandidateCount_unbounded
#print axioms ConstitutiveSearch.jointGrowingFuel_unbounded
#print axioms ConstitutiveSearch.jointGrowingPrimitive_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.jointGrowingComposition_inputPolynomiallyBounded
/- AXIOM_AUDIT_END -/
