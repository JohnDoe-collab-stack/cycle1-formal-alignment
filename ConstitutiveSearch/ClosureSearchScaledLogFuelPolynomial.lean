import Init.Data.Nat.Lemmas
import ConstitutiveSearch.ClosureSearchLogFuelPolynomial

/-!
# Constant-factor logarithmic growing-fuel regime

The one-candidate logarithmic regime extends to any fixed natural factor c.

If

  fuel(n) <= c * log2(inputBits(n)),

then the exact one-candidate closure recurrence is bounded by

  inputBits(n)^c.

The module reifies this bound as a CostPolynomial envelope of degree c and also
provides an exact witness family

  inputBits(n) = 2^n,
  fuel(n) = c*n,

for which budget(n) + 1 = inputBits(n)^c.

Thus an unbounded fuel can remain polynomial when its growth is logarithmic in
the concrete input size with one fixed multiplicative factor.
-/

namespace ConstitutiveSearch

namespace CostPolynomial

/-- Internal polynomial syntax for X^degree. -/
def inputPower : Nat → CostPolynomial
  | 0 =>
      .constant 1
  | degree + 1 =>
      .mul
        (inputPower degree)
        .input

/-- The internal input-power syntax evaluates exactly to an ordinary Nat power. -/
theorem eval_inputPower :
    ∀ (degree inputBits : Nat),
      (inputPower degree).eval inputBits =
        inputBits ^ degree
  | 0, _ =>
      rfl
  | degree + 1, inputBits => by
      change
        (inputPower degree).eval inputBits *
            inputBits =
          inputBits ^ (degree + 1)
      rw [
        eval_inputPower
          degree
          inputBits,
        Nat.pow_succ
      ]

/-- Structural degree of the internal X^degree syntax is exactly degree. -/
theorem inputPower_degree :
    ∀ degree : Nat,
      (inputPower degree).degree =
        degree
  | 0 =>
      rfl
  | degree + 1 => by
      change
        (inputPower degree).degree + 1 =
          degree + 1
      rw [
        inputPower_degree degree
      ]

end CostPolynomial

/--
A one-candidate primitive-query budget with fuel <= factor*log2(inputBits) is
pointwise bounded by inputBits^factor.
-/
theorem closurePrimitiveOneCandidate_scaledLogFuel_le_inputPower
    (inputBits fuel : Nat → Nat)
    (factor : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (fuelLeScaledLog :
      ∀ n : Nat,
        fuel n ≤
          factor *
            Constructive.natLog2 (inputBits n)) :
    ∀ n : Nat,
      closurePrimitiveQueryBudget
          1
          (fuel n) ≤
        (inputBits n) ^ factor := by
  intro n
  have fuelPowerLe :
      2 ^ fuel n ≤
        2 ^
          (factor *
            Constructive.natLog2 (inputBits n)) :=
    Nat.pow_le_pow_right
      Nat.zero_lt_two
      (fuelLeScaledLog n)
  have logPowerLe :
      2 ^ Constructive.natLog2 (inputBits n) ≤
        inputBits n :=
    Constructive.two_pow_natLog2_le
      (Nat.ne_of_gt
        (inputPositive n))
  have scaledPowerLe :
      2 ^
          (factor *
            Constructive.natLog2 (inputBits n)) ≤
        (inputBits n) ^ factor := by
    rw [
      Nat.mul_comm
        factor
        (Constructive.natLog2 (inputBits n)),
      Constructive.nat_pow_mul
    ]
    exact
      Nat.pow_le_pow_left
        logPowerLe
        factor
  have budgetPlusOneLe :
      closurePrimitiveQueryBudget
            1
            (fuel n) +
          1 ≤
        (inputBits n) ^ factor := by
    rw [
      closurePrimitiveOneCandidateGrowingFuel_eq_two_pow
        (fuel n)
    ]
    exact
      Nat.le_trans
        fuelPowerLe
        scaledPowerLe
  exact
    Nat.le_trans
      (Nat.le_add_right
        (closurePrimitiveQueryBudget
          1
          (fuel n))
        1)
      budgetPlusOneLe

/--
The primitive-query family therefore has the explicit internal envelope X^factor.
-/
theorem closurePrimitiveOneCandidate_scaledLogFuel_inputPolynomiallyBounded
    (inputBits fuel : Nat → Nat)
    (factor : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (fuelLeScaledLog :
      ∀ n : Nat,
        fuel n ≤
          factor *
            Constructive.natLog2 (inputBits n)) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        closurePrimitiveQueryBudget
          1
          (fuel n)) :=
  ⟨CostPolynomial.inputPower factor,
    fun n => by
      rw [
        CostPolynomial.eval_inputPower
      ]
      exact
        closurePrimitiveOneCandidate_scaledLogFuel_le_inputPower
          inputBits
          fuel
          factor
          inputPositive
          fuelLeScaledLog
          n⟩

/--
The composition-candidate counter satisfies the same scaled-logarithmic bound.
-/
theorem closureCompositionOneCandidate_scaledLogFuel_le_inputPower
    (inputBits fuel : Nat → Nat)
    (factor : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (fuelLeScaledLog :
      ∀ n : Nat,
        fuel n ≤
          factor *
            Constructive.natLog2 (inputBits n)) :
    ∀ n : Nat,
      closureCompositionCandidateBudget
          1
          (fuel n) ≤
        (inputBits n) ^ factor := by
  intro n
  have fuelPowerLe :
      2 ^ fuel n ≤
        2 ^
          (factor *
            Constructive.natLog2 (inputBits n)) :=
    Nat.pow_le_pow_right
      Nat.zero_lt_two
      (fuelLeScaledLog n)
  have logPowerLe :
      2 ^ Constructive.natLog2 (inputBits n) ≤
        inputBits n :=
    Constructive.two_pow_natLog2_le
      (Nat.ne_of_gt
        (inputPositive n))
  have scaledPowerLe :
      2 ^
          (factor *
            Constructive.natLog2 (inputBits n)) ≤
        (inputBits n) ^ factor := by
    rw [
      Nat.mul_comm
        factor
        (Constructive.natLog2 (inputBits n)),
      Constructive.nat_pow_mul
    ]
    exact
      Nat.pow_le_pow_left
        logPowerLe
        factor
  have budgetPlusOneLe :
      closureCompositionCandidateBudget
            1
            (fuel n) +
          1 ≤
        (inputBits n) ^ factor := by
    rw [
      closureCompositionOneCandidateGrowingFuel_eq_two_pow
        (fuel n)
    ]
    exact
      Nat.le_trans
        fuelPowerLe
        scaledPowerLe
  exact
    Nat.le_trans
      (Nat.le_add_right
        (closureCompositionCandidateBudget
          1
          (fuel n))
        1)
      budgetPlusOneLe

/--
The composition-candidate family has the same explicit X^factor envelope.
-/
theorem closureCompositionOneCandidate_scaledLogFuel_inputPolynomiallyBounded
    (inputBits fuel : Nat → Nat)
    (factor : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (fuelLeScaledLog :
      ∀ n : Nat,
        fuel n ≤
          factor *
            Constructive.natLog2 (inputBits n)) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        closureCompositionCandidateBudget
          1
          (fuel n)) :=
  ⟨CostPolynomial.inputPower factor,
    fun n => by
      rw [
        CostPolynomial.eval_inputPower
      ]
      exact
        closureCompositionOneCandidate_scaledLogFuel_le_inputPower
          inputBits
          fuel
          factor
          inputPositive
          fuelLeScaledLog
          n⟩

/-- Concrete fuel family c*n over the existing input family 2^n. -/
def scaledLogarithmicWitnessFuel
    (factor n : Nat) : Nat :=
  factor * n

theorem scaledLogarithmicWitnessFuel_le_scaledLog
    (factor : Nat) :
    ∀ n : Nat,
      scaledLogarithmicWitnessFuel
          factor
          n ≤
        factor *
          Constructive.natLog2
            (logarithmicWitnessInputBits n) := by
  intro n
  unfold
    scaledLogarithmicWitnessFuel
    logarithmicWitnessInputBits
  rw [
    Constructive.natLog2_two_pow
  ]
  exact
    Nat.le_refl
      (factor * n)

/--
For positive factor, the scaled logarithmic witness fuel is genuinely unbounded.
-/
theorem scaledLogarithmicWitnessFuel_unbounded
    (factor : Nat)
    (factorPositive :
      0 < factor) :
    ∀ cap : Nat,
      ∃ n : Nat,
        cap <
          scaledLogarithmicWitnessFuel
            factor
            n := by
  intro cap
  refine
    ⟨cap + 1, ?_⟩
  have oneLeFactor :
      1 ≤ factor :=
    factorPositive
  have lower :
      cap + 1 ≤
        factor * (cap + 1) := by
    calc
      cap + 1
          =
        1 * (cap + 1) := by
          rw [Nat.one_mul]
      _ ≤
        factor * (cap + 1) :=
          Nat.mul_le_mul_right
            (cap + 1)
            oneLeFactor
  exact
    Nat.lt_of_lt_of_le
      (Nat.lt_succ_self cap)
      lower

/--
On the concrete witness family, primitive-query budget plus one is exactly the
factor-th power of the concrete input size.
-/
theorem scaledLogarithmicWitnessPrimitive_exact
    (factor n : Nat) :
    closurePrimitiveQueryBudget
          1
          (scaledLogarithmicWitnessFuel
            factor
            n) +
        1 =
      (logarithmicWitnessInputBits n) ^ factor := by
  rw [
    closurePrimitiveOneCandidateGrowingFuel_eq_two_pow
      (scaledLogarithmicWitnessFuel
        factor
        n)
  ]
  unfold
    scaledLogarithmicWitnessFuel
    logarithmicWitnessInputBits
  rw [
    Nat.mul_comm
      factor
      n,
    Constructive.nat_pow_mul
  ]

/--
The composition-candidate witness has the same exact factor-th power form.
-/
theorem scaledLogarithmicWitnessComposition_exact
    (factor n : Nat) :
    closureCompositionCandidateBudget
          1
          (scaledLogarithmicWitnessFuel
            factor
            n) +
        1 =
      (logarithmicWitnessInputBits n) ^ factor := by
  rw [
    closureCompositionOneCandidateGrowingFuel_eq_two_pow
      (scaledLogarithmicWitnessFuel
        factor
        n)
  ]
  unfold
    scaledLogarithmicWitnessFuel
    logarithmicWitnessInputBits
  rw [
    Nat.mul_comm
      factor
      n,
    Constructive.nat_pow_mul
  ]

theorem scaledLogarithmicWitnessPrimitive_inputPolynomiallyBounded
    (factor : Nat) :
    InputPolynomiallyBounded
      logarithmicWitnessInputBits
      (fun n =>
        closurePrimitiveQueryBudget
          1
          (scaledLogarithmicWitnessFuel
            factor
            n)) :=
  closurePrimitiveOneCandidate_scaledLogFuel_inputPolynomiallyBounded
    logarithmicWitnessInputBits
    (scaledLogarithmicWitnessFuel factor)
    factor
    logarithmicWitnessInputPositive
    (scaledLogarithmicWitnessFuel_le_scaledLog
      factor)

theorem scaledLogarithmicWitnessComposition_inputPolynomiallyBounded
    (factor : Nat) :
    InputPolynomiallyBounded
      logarithmicWitnessInputBits
      (fun n =>
        closureCompositionCandidateBudget
          1
          (scaledLogarithmicWitnessFuel
            factor
            n)) :=
  closureCompositionOneCandidate_scaledLogFuel_inputPolynomiallyBounded
    logarithmicWitnessInputBits
    (scaledLogarithmicWitnessFuel factor)
    factor
    logarithmicWitnessInputPositive
    (scaledLogarithmicWitnessFuel_le_scaledLog
      factor)

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.CostPolynomial.inputPower
#print axioms ConstitutiveSearch.CostPolynomial.eval_inputPower
#print axioms ConstitutiveSearch.CostPolynomial.inputPower_degree
#print axioms ConstitutiveSearch.closurePrimitiveOneCandidate_scaledLogFuel_le_inputPower
#print axioms ConstitutiveSearch.closurePrimitiveOneCandidate_scaledLogFuel_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.closureCompositionOneCandidate_scaledLogFuel_le_inputPower
#print axioms ConstitutiveSearch.closureCompositionOneCandidate_scaledLogFuel_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.scaledLogarithmicWitnessFuel
#print axioms ConstitutiveSearch.scaledLogarithmicWitnessFuel_le_scaledLog
#print axioms ConstitutiveSearch.scaledLogarithmicWitnessFuel_unbounded
#print axioms ConstitutiveSearch.scaledLogarithmicWitnessPrimitive_exact
#print axioms ConstitutiveSearch.scaledLogarithmicWitnessComposition_exact
#print axioms ConstitutiveSearch.scaledLogarithmicWitnessPrimitive_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.scaledLogarithmicWitnessComposition_inputPolynomiallyBounded
/- AXIOM_AUDIT_END -/
