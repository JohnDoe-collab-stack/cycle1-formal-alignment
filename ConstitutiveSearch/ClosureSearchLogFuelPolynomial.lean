import Init.Data.Nat.Lemmas
import ConstitutiveSearch.PolynomialExponentialSeparator

/-!
# Logarithmic growing-fuel polynomial regime

The exponential separator shows that one-candidate closure with
fuel(input)=input is not PolynomiallyBounded.

This module isolates a complementary positive regime.  When there is one
candidate and the fuel is bounded by log2 of the concrete input size, the exact
binary closure recurrence stays linearly bounded by inputBits.

Thus unbounded fuel is not, by itself, the obstruction.  What matters is its
growth relative to the concrete input-size coordinate.
-/

namespace ConstitutiveSearch

/--
For positive concrete input size, a one-candidate primitive-query closure budget
whose fuel stays below log2(inputBits) is pointwise bounded by inputBits.
-/
theorem closurePrimitiveOneCandidate_logFuel_le_input
    (inputBits fuel : Nat → Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (fuelLeLog :
      ∀ n : Nat,
        fuel n ≤
          Constructive.natLog2 (inputBits n)) :
    ∀ n : Nat,
      closurePrimitiveQueryBudget
          1
          (fuel n) ≤
        inputBits n := by
  intro n
  have fuelPowerLe :
      2 ^ fuel n ≤
        2 ^ Constructive.natLog2 (inputBits n) :=
    Nat.pow_le_pow_right
      Nat.zero_lt_two
      (fuelLeLog n)
  have logPowerLe :
      2 ^ Constructive.natLog2 (inputBits n) ≤
        inputBits n :=
    Constructive.two_pow_natLog2_le
      (Nat.ne_of_gt
        (inputPositive n))
  have budgetPlusOneLe :
      closurePrimitiveQueryBudget
            1
            (fuel n) +
          1 ≤
        inputBits n := by
    rw [
      closurePrimitiveOneCandidateGrowingFuel_eq_two_pow
        (fuel n)
    ]
    exact
      Nat.le_trans
        fuelPowerLe
        logPowerLe
  exact
    Nat.le_trans
      (Nat.le_add_right
        (closurePrimitiveQueryBudget 1 (fuel n))
        1)
      budgetPlusOneLe

/--
The primitive-query cost family is therefore input-polynomial, with the
identity polynomial X as an explicit envelope.
-/
theorem closurePrimitiveOneCandidate_logFuel_inputPolynomiallyBounded
    (inputBits fuel : Nat → Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (fuelLeLog :
      ∀ n : Nat,
        fuel n ≤
          Constructive.natLog2 (inputBits n)) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        closurePrimitiveQueryBudget
          1
          (fuel n)) :=
  ⟨CostPolynomial.input,
    closurePrimitiveOneCandidate_logFuel_le_input
      inputBits
      fuel
      inputPositive
      fuelLeLog⟩

/--
The same logarithmic-fuel bound holds for the one-candidate composition counter.
-/
theorem closureCompositionOneCandidate_logFuel_le_input
    (inputBits fuel : Nat → Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (fuelLeLog :
      ∀ n : Nat,
        fuel n ≤
          Constructive.natLog2 (inputBits n)) :
    ∀ n : Nat,
      closureCompositionCandidateBudget
          1
          (fuel n) ≤
        inputBits n := by
  intro n
  have fuelPowerLe :
      2 ^ fuel n ≤
        2 ^ Constructive.natLog2 (inputBits n) :=
    Nat.pow_le_pow_right
      Nat.zero_lt_two
      (fuelLeLog n)
  have logPowerLe :
      2 ^ Constructive.natLog2 (inputBits n) ≤
        inputBits n :=
    Constructive.two_pow_natLog2_le
      (Nat.ne_of_gt
        (inputPositive n))
  have budgetPlusOneLe :
      closureCompositionCandidateBudget
            1
            (fuel n) +
          1 ≤
        inputBits n := by
    rw [
      closureCompositionOneCandidateGrowingFuel_eq_two_pow
        (fuel n)
    ]
    exact
      Nat.le_trans
        fuelPowerLe
        logPowerLe
  exact
    Nat.le_trans
      (Nat.le_add_right
        (closureCompositionCandidateBudget 1 (fuel n))
        1)
      budgetPlusOneLe

/--
The one-candidate composition counter is likewise input-polynomial under
logarithmic fuel.
-/
theorem closureCompositionOneCandidate_logFuel_inputPolynomiallyBounded
    (inputBits fuel : Nat → Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < inputBits n)
    (fuelLeLog :
      ∀ n : Nat,
        fuel n ≤
          Constructive.natLog2 (inputBits n)) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        closureCompositionCandidateBudget
          1
          (fuel n)) :=
  ⟨CostPolynomial.input,
    closureCompositionOneCandidate_logFuel_le_input
      inputBits
      fuel
      inputPositive
      fuelLeLog⟩

/--
Concrete unbounded-fuel witness family:
inputBits(n)=2^n and fuel(n)=n.

Fuel grows without bound, but it is exactly log2(inputBits), so both one-candidate
closure counters remain linear in concrete input size.
-/
def logarithmicWitnessInputBits
    (n : Nat) : Nat :=
  2 ^ n

def logarithmicWitnessFuel
    (n : Nat) : Nat :=
  n

theorem logarithmicWitnessInputPositive :
    ∀ n : Nat,
      0 < logarithmicWitnessInputBits n := by
  intro n
  unfold logarithmicWitnessInputBits
  exact
    Nat.pow_pos
      Nat.zero_lt_two

theorem logarithmicWitnessFuel_eq_log :
    ∀ n : Nat,
      logarithmicWitnessFuel n =
        Constructive.natLog2
          (logarithmicWitnessInputBits n) := by
  intro n
  unfold
    logarithmicWitnessFuel
    logarithmicWitnessInputBits
  exact
    (Constructive.natLog2_two_pow).symm

theorem logarithmicWitnessFuel_unbounded :
    ∀ cap : Nat,
      ∃ n : Nat,
        cap <
          logarithmicWitnessFuel n := by
  intro cap
  exact
    ⟨cap + 1,
      by
        unfold logarithmicWitnessFuel
        exact Nat.lt_succ_self cap⟩

theorem logarithmicWitnessPrimitive_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      logarithmicWitnessInputBits
      (fun n =>
        closurePrimitiveQueryBudget
          1
          (logarithmicWitnessFuel n)) :=
  closurePrimitiveOneCandidate_logFuel_inputPolynomiallyBounded
    logarithmicWitnessInputBits
    logarithmicWitnessFuel
    logarithmicWitnessInputPositive
    (fun n => by
      rw [
        logarithmicWitnessFuel_eq_log
          n
      ]
      exact
        Nat.le_refl
          (Constructive.natLog2
            (logarithmicWitnessInputBits n)))

theorem logarithmicWitnessComposition_inputPolynomiallyBounded :
    InputPolynomiallyBounded
      logarithmicWitnessInputBits
      (fun n =>
        closureCompositionCandidateBudget
          1
          (logarithmicWitnessFuel n)) :=
  closureCompositionOneCandidate_logFuel_inputPolynomiallyBounded
    logarithmicWitnessInputBits
    logarithmicWitnessFuel
    logarithmicWitnessInputPositive
    (fun n => by
      rw [
        logarithmicWitnessFuel_eq_log
          n
      ]
      exact
        Nat.le_refl
          (Constructive.natLog2
            (logarithmicWitnessInputBits n)))

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.closurePrimitiveOneCandidate_logFuel_le_input
#print axioms ConstitutiveSearch.closurePrimitiveOneCandidate_logFuel_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.closureCompositionOneCandidate_logFuel_le_input
#print axioms ConstitutiveSearch.closureCompositionOneCandidate_logFuel_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.logarithmicWitnessInputBits
#print axioms ConstitutiveSearch.logarithmicWitnessFuel
#print axioms ConstitutiveSearch.logarithmicWitnessInputPositive
#print axioms ConstitutiveSearch.logarithmicWitnessFuel_eq_log
#print axioms ConstitutiveSearch.logarithmicWitnessFuel_unbounded
#print axioms ConstitutiveSearch.logarithmicWitnessPrimitive_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.logarithmicWitnessComposition_inputPolynomiallyBounded
/- AXIOM_AUDIT_END -/
