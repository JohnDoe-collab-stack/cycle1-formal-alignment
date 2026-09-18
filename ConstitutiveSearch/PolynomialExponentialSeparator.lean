import Init.Omega
import ConstitutiveSearch.PolynomialCostEnvelope
import ConstitutiveSearch.ClosureSearchGrowingFuelSeparator

/-!
# Exponential separator for internal cost polynomials

This module proves, entirely inside the project's CostPolynomial language, that
the function n ↦ 2^n is not PolynomiallyBounded.

The proof has two layers.

First, every CostPolynomial is assigned:
* a nonnegative coefficient mass;
* a structural rank.

For every input n >= 1, evaluation is bounded by

  eval p n <= mass(p) * n^rank(p).

Second, from those two finite parameters we construct an explicit input at
which 2^n strictly exceeds that majorant.

The result is then applied to the one-candidate growing-fuel closure separator:
when fuel(input) = input, neither canonical closure counter is
PolynomiallyBounded.

These are statements about the source-level event budgets of the announced
ClosureSearch engine, not wall-clock machine-time lower bounds.
-/

namespace ConstitutiveSearch

namespace CostPolynomial

/-- Sum/product coefficient mass used by the structural majorant. -/
def majorantMass : CostPolynomial → Nat
  | .constant value =>
      value
  | .input =>
      1
  | .add left right =>
      left.majorantMass +
        right.majorantMass
  | .mul left right =>
      left.majorantMass *
        right.majorantMass

/--
A convenient structural rank for the majorant.

Addition deliberately receives enough rank to dominate both children without
needing subtraction or a max-normalization proof.
-/
def majorantRank : CostPolynomial → Nat
  | .constant _ =>
      0
  | .input =>
      1
  | .add left right =>
      left.majorantRank +
        right.majorantRank +
        1
  | .mul left right =>
      left.majorantRank +
        right.majorantRank

/--
Every internal cost polynomial is bounded by one monomial built from its own
finite syntax.
-/
theorem eval_le_majorant :
    ∀ (polynomial : CostPolynomial)
      (inputBits : Nat),
      1 ≤ inputBits →
        polynomial.eval inputBits ≤
          polynomial.majorantMass *
            inputBits ^ polynomial.majorantRank
  | .constant value, inputBits, _ => by
      simp only [
        eval,
        majorantMass,
        majorantRank,
        Nat.pow_zero,
        Nat.mul_one
      ]
      exact Nat.le_refl value
  | .input, inputBits, _ => by
      simp only [
        eval,
        majorantMass,
        majorantRank,
        Nat.pow_one,
        Nat.one_mul
      ]
      exact Nat.le_refl inputBits
  | .add left right, inputBits, inputPositive => by
      have inputNonzero :
          0 < inputBits :=
        Nat.lt_of_lt_of_le
          Nat.zero_lt_one
          inputPositive
      have leftLe :=
        eval_le_majorant
          left
          inputBits
          inputPositive
      have rightLe :=
        eval_le_majorant
          right
          inputBits
          inputPositive
      have leftRankLe :
          left.majorantRank ≤
            left.majorantRank +
              right.majorantRank +
              1 := by
        omega
      have rightRankLe :
          right.majorantRank ≤
            left.majorantRank +
              right.majorantRank +
              1 := by
        omega
      have leftPowLe :
          inputBits ^ left.majorantRank ≤
            inputBits ^
              (left.majorantRank +
                right.majorantRank +
                1) :=
        Nat.pow_le_pow_right
          inputNonzero
          leftRankLe
      have rightPowLe :
          inputBits ^ right.majorantRank ≤
            inputBits ^
              (left.majorantRank +
                right.majorantRank +
                1) :=
        Nat.pow_le_pow_right
          inputNonzero
          rightRankLe
      have leftLifted :
          left.eval inputBits ≤
            left.majorantMass *
              inputBits ^
                (left.majorantRank +
                  right.majorantRank +
                  1) :=
        Nat.le_trans
          leftLe
          (Nat.mul_le_mul_left
            left.majorantMass
            leftPowLe)
      have rightLifted :
          right.eval inputBits ≤
            right.majorantMass *
              inputBits ^
                (left.majorantRank +
                  right.majorantRank +
                  1) :=
        Nat.le_trans
          rightLe
          (Nat.mul_le_mul_left
            right.majorantMass
            rightPowLe)
      change
        left.eval inputBits +
            right.eval inputBits ≤
          (left.majorantMass +
              right.majorantMass) *
            inputBits ^
              (left.majorantRank +
                right.majorantRank +
                1)
      calc
        left.eval inputBits +
              right.eval inputBits
            ≤
          left.majorantMass *
                inputBits ^
                  (left.majorantRank +
                    right.majorantRank +
                    1) +
              right.majorantMass *
                inputBits ^
                  (left.majorantRank +
                    right.majorantRank +
                    1) :=
          Nat.add_le_add
            leftLifted
            rightLifted
        _ =
          (left.majorantMass +
              right.majorantMass) *
            inputBits ^
              (left.majorantRank +
                right.majorantRank +
                1) := by
          rw [Nat.add_mul]
  | .mul left right, inputBits, inputPositive => by
      have leftLe :=
        eval_le_majorant
          left
          inputBits
          inputPositive
      have rightLe :=
        eval_le_majorant
          right
          inputBits
          inputPositive
      change
        left.eval inputBits *
            right.eval inputBits ≤
          (left.majorantMass *
              right.majorantMass) *
            inputBits ^
              (left.majorantRank +
                right.majorantRank)
      calc
        left.eval inputBits *
              right.eval inputBits
            ≤
          (left.majorantMass *
              inputBits ^ left.majorantRank) *
            (right.majorantMass *
              inputBits ^ right.majorantRank) :=
          Nat.mul_le_mul
            leftLe
            rightLe
        _ =
          (left.majorantMass *
              right.majorantMass) *
            inputBits ^
              (left.majorantRank +
                right.majorantRank) := by
          rw [Nat.pow_add]
          ac_rfl

/--
For n >= 3, doubling n still remains strictly below 2^n.

This small lemma is the only asymptotic arithmetic ingredient needed by the
explicit escape construction.
-/
theorem two_mul_lt_two_pow_of_three_le
    (n : Nat)
    (threeLe : 3 ≤ n) :
    n + n < 2 ^ n := by
  obtain ⟨offset, rfl⟩ :=
    Nat.exists_eq_add_of_le
      threeLe
  induction offset with
  | zero =>
      decide
  | succ offset inductionHypothesis =>
      have oneLe :
          1 ≤ 3 + offset := by
        omega
      have twoLePow :
          2 ≤ 2 ^ (3 + offset) := by
        have powerMonotone :=
          Nat.pow_le_pow_right
            Nat.zero_lt_two
            oneLe
        simpa only [
          Nat.pow_one
        ] using powerMonotone
      rw [
        show
          3 + (offset + 1) =
            (3 + offset) + 1 by
              omega,
        Nat.pow_succ
      ]
      omega

/-- First finite parameter used by the explicit escape point. -/
def escapeCore
    (polynomial : CostPolynomial) : Nat :=
  polynomial.majorantMass +
    polynomial.majorantRank +
    4

/-- First power-of-two expansion of the structural parameters. -/
def escapeExponent
    (polynomial : CostPolynomial) : Nat :=
  2 ^ polynomial.escapeCore

/-- Concrete input at which the exponential escapes the polynomial majorant. -/
def exponentialEscapeInput
    (polynomial : CostPolynomial) : Nat :=
  2 ^ polynomial.escapeExponent

/-- The escape core is safely inside the doubling-growth regime. -/
theorem escapeCore_three_le
    (polynomial : CostPolynomial) :
    3 ≤ polynomial.escapeCore := by
  unfold escapeCore
  omega

/-- The structural mass lies strictly below the first power-of-two expansion. -/
theorem majorantMass_lt_escapeExponent
    (polynomial : CostPolynomial) :
    polynomial.majorantMass <
      polynomial.escapeExponent := by
  unfold escapeExponent
  have massLtCore :
      polynomial.majorantMass <
        polynomial.escapeCore := by
    unfold escapeCore
    omega
  exact
    Nat.lt_trans
      massLtCore
      (show
        polynomial.escapeCore <
          2 ^ polynomial.escapeCore from
        Nat.lt_two_pow_self)

/-- Rank plus one is bounded by the finite escape core. -/
theorem majorantRank_succ_le_escapeCore
    (polynomial : CostPolynomial) :
    polynomial.majorantRank + 1 ≤
      polynomial.escapeCore := by
  unfold escapeCore
  omega

/--
The linear exponent induced by the monomial majorant lies below the concrete
escape input.
-/
theorem majorantExponent_lt_escapeInput
    (polynomial : CostPolynomial) :
    polynomial.majorantMass +
          polynomial.escapeExponent *
            polynomial.majorantRank <
      polynomial.exponentialEscapeInput := by
  let core :=
    polynomial.escapeCore
  let exponent :=
    polynomial.escapeExponent
  have coreThree :
      3 ≤ core := by
    simpa only [core] using
      polynomial.escapeCore_three_le
  have coreDoubleLt :
      core + core <
        2 ^ core :=
    two_mul_lt_two_pow_of_three_le
      core
      coreThree
  have exponentEq :
      exponent = 2 ^ core := by
    rfl
  have massLtExponent :
      polynomial.majorantMass <
        exponent := by
    simpa only [exponent] using
      polynomial.majorantMass_lt_escapeExponent
  have rankSuccLeCore :
      polynomial.majorantRank + 1 ≤
        core := by
    simpa only [core] using
      polynomial.majorantRank_succ_le_escapeCore
  have first :
      polynomial.majorantMass +
            exponent *
              polynomial.majorantRank <
        exponent *
          (polynomial.majorantRank + 1) := by
    calc
      polynomial.majorantMass +
            exponent *
              polynomial.majorantRank
          <
        exponent +
            exponent *
              polynomial.majorantRank :=
        Nat.add_lt_add_right
          massLtExponent
          (exponent *
            polynomial.majorantRank)
      _ =
        exponent *
          (polynomial.majorantRank + 1) := by
        rw [
          Nat.mul_add,
          Nat.mul_one,
          Nat.add_comm
        ]
  have second :
      exponent *
          (polynomial.majorantRank + 1) ≤
        exponent * core :=
    Nat.mul_le_mul_left
      exponent
      rankSuccLeCore
  have coreLeExponent :
      core ≤ exponent := by
    have coreLt :
        core < exponent := by
      rw [exponentEq]
      exact Nat.lt_two_pow_self
    exact Nat.le_of_lt coreLt
  have third :
      exponent * core ≤
        exponent * exponent :=
    Nat.mul_le_mul_left
      exponent
      coreLeExponent
  have exponentSquareEq :
      exponent * exponent =
        2 ^ (core + core) := by
    rw [
      exponentEq,
      Nat.pow_add
    ]
  have fourth :
      exponent * exponent <
        2 ^ exponent := by
    rw [exponentSquareEq]
    exact
      Nat.pow_lt_pow_right
        Nat.one_lt_two
        (by
          rw [exponentEq]
          exact coreDoubleLt)
  have combined :
      polynomial.majorantMass +
            exponent *
              polynomial.majorantRank <
        2 ^ exponent :=
    Nat.lt_of_lt_of_le
      first
      (Nat.le_trans
        second
        (Nat.le_of_lt
          (Nat.lt_of_le_of_lt
            third
            fourth)))
  simpa only [
    exponentialEscapeInput,
    exponent
  ] using combined

/--
At the explicit escape input, the polynomial's structural majorant is strictly
below 2^input.
-/
theorem majorant_lt_two_pow_at_escape
    (polynomial : CostPolynomial) :
    polynomial.majorantMass *
          polynomial.exponentialEscapeInput ^
            polynomial.majorantRank <
      2 ^ polynomial.exponentialEscapeInput := by
  let exponent :=
    polynomial.escapeExponent
  let input :=
    polynomial.exponentialEscapeInput
  have massLePow :
      polynomial.majorantMass ≤
        2 ^ polynomial.majorantMass :=
    Nat.le_of_lt
      Nat.lt_two_pow_self
  have coefficientLift :
      polynomial.majorantMass *
            input ^ polynomial.majorantRank ≤
        2 ^ polynomial.majorantMass *
          input ^ polynomial.majorantRank :=
    Nat.mul_le_mul_right
      (input ^ polynomial.majorantRank)
      massLePow
  have inputEq :
      input = 2 ^ exponent := by
    rfl
  have monomialEq :
      2 ^ polynomial.majorantMass *
            input ^ polynomial.majorantRank =
        2 ^
          (polynomial.majorantMass +
            exponent *
              polynomial.majorantRank) := by
    rw [
      inputEq,
      ← Nat.pow_mul,
      ← Nat.pow_add
    ]
  have exponentLt :
      polynomial.majorantMass +
            exponent *
              polynomial.majorantRank <
        input := by
    simpa only [
      exponent,
      input
    ] using
      polynomial.majorantExponent_lt_escapeInput
  have powerLt :
      2 ^
          (polynomial.majorantMass +
            exponent *
              polynomial.majorantRank) <
        2 ^ input :=
    Nat.pow_lt_pow_right
      Nat.one_lt_two
      exponentLt
  exact
    Nat.lt_of_le_of_lt
      coefficientLift
      (by
        rw [monomialEq]
        exact powerLt)

/--
Every CostPolynomial is strictly beaten by 2^n at one explicit natural input.
-/
theorem exists_eval_lt_two_pow
    (polynomial : CostPolynomial) :
    ∃ inputBits : Nat,
      polynomial.eval inputBits <
        2 ^ inputBits := by
  refine
    ⟨polynomial.exponentialEscapeInput, ?_⟩
  have inputPositive :
      1 ≤
        polynomial.exponentialEscapeInput := by
    unfold exponentialEscapeInput
    exact
      Nat.one_le_pow
        polynomial.escapeExponent
        2
        Nat.zero_lt_two
  exact
    Nat.lt_of_le_of_lt
      (polynomial.eval_le_majorant
        polynomial.exponentialEscapeInput
        inputPositive)
      polynomial.majorant_lt_two_pow_at_escape

end CostPolynomial

/--
The exponential function 2^n does not admit any finite internal CostPolynomial
envelope.
-/
theorem twoPow_not_polynomiallyBounded :
    ¬
      PolynomiallyBounded
        (fun inputBits =>
          2 ^ inputBits) := by
  intro bounded
  rcases bounded with
    ⟨envelope, exponentialLe⟩
  rcases
      envelope.exists_eval_lt_two_pow with
    ⟨inputBits, envelopeLt⟩
  have impossible :
      2 ^ inputBits <
        2 ^ inputBits :=
    Nat.lt_of_le_of_lt
      (exponentialLe inputBits)
      envelopeLt
  exact
    (Nat.lt_irrefl
      (2 ^ inputBits))
      impossible

/--
The one-candidate primitive-query closure budget with fuel(input)=input is not
PolynomiallyBounded in the project's internal sense.
-/
theorem closurePrimitiveOneCandidateIdentityFuel_not_polynomiallyBounded :
    ¬
      PolynomiallyBounded
        (fun inputBits =>
          closurePrimitiveQueryBudget
            1
            inputBits) := by
  intro bounded
  have plusOneBounded :
      PolynomiallyBounded
        (fun inputBits =>
          closurePrimitiveQueryBudget
              1
              inputBits +
            1) :=
    PolynomiallyBounded.add
      bounded
      (PolynomiallyBounded.constant 1)
  have exponentialBounded :
      PolynomiallyBounded
        (fun inputBits =>
          2 ^ inputBits) := by
    simpa only [
      closurePrimitiveOneCandidateGrowingFuel_eq_two_pow
    ] using plusOneBounded
  exact
    twoPow_not_polynomiallyBounded
      exponentialBounded

/--
The analogous one-candidate composition-candidate closure budget is also not
PolynomiallyBounded when fuel(input)=input.
-/
theorem closureCompositionOneCandidateIdentityFuel_not_polynomiallyBounded :
    ¬
      PolynomiallyBounded
        (fun inputBits =>
          closureCompositionCandidateBudget
            1
            inputBits) := by
  intro bounded
  have plusOneBounded :
      PolynomiallyBounded
        (fun inputBits =>
          closureCompositionCandidateBudget
              1
              inputBits +
            1) :=
    PolynomiallyBounded.add
      bounded
      (PolynomiallyBounded.constant 1)
  have exponentialBounded :
      PolynomiallyBounded
        (fun inputBits =>
          2 ^ inputBits) := by
    simpa only [
      closureCompositionOneCandidateGrowingFuel_eq_two_pow
    ] using plusOneBounded
  exact
    twoPow_not_polynomiallyBounded
      exponentialBounded

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.CostPolynomial.majorantMass
#print axioms ConstitutiveSearch.CostPolynomial.majorantRank
#print axioms ConstitutiveSearch.CostPolynomial.eval_le_majorant
#print axioms ConstitutiveSearch.CostPolynomial.two_mul_lt_two_pow_of_three_le
#print axioms ConstitutiveSearch.CostPolynomial.escapeCore
#print axioms ConstitutiveSearch.CostPolynomial.escapeExponent
#print axioms ConstitutiveSearch.CostPolynomial.exponentialEscapeInput
#print axioms ConstitutiveSearch.CostPolynomial.escapeCore_three_le
#print axioms ConstitutiveSearch.CostPolynomial.majorantMass_lt_escapeExponent
#print axioms ConstitutiveSearch.CostPolynomial.majorantRank_succ_le_escapeCore
#print axioms ConstitutiveSearch.CostPolynomial.majorantExponent_lt_escapeInput
#print axioms ConstitutiveSearch.CostPolynomial.majorant_lt_two_pow_at_escape
#print axioms ConstitutiveSearch.CostPolynomial.exists_eval_lt_two_pow
#print axioms ConstitutiveSearch.twoPow_not_polynomiallyBounded
#print axioms ConstitutiveSearch.closurePrimitiveOneCandidateIdentityFuel_not_polynomiallyBounded
#print axioms ConstitutiveSearch.closureCompositionOneCandidateIdentityFuel_not_polynomiallyBounded
/- AXIOM_AUDIT_END -/
