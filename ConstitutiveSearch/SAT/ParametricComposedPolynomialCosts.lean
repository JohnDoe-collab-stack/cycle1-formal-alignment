import ConstitutiveSearch.SAT.ParametricComposedBitComplexity

/-!
# Polynomial representation bound for the SAT composition phase

This module closes the recursive representation budgets used by the parametric
composition benchmark into explicit polynomial expressions in n, and then
re-indexes the resulting phase bound by the concrete binary size of F(n).

The theorem remains about the declared binary representation-charge model.  It
does not identify that charge with wall-clock execution time.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Closed polynomial history envelope for the n+2 decision square states. -/
def composedHistoryPolynomialBudget
    (count : Nat) : Nat :=
  (count + 2) * ((count + 2) + 3) + 1

/-- Closed polynomial encoded-state envelope. -/
def composedStatePolynomialBudget
    (count : Nat) : Nat :=
  explicitFamilyFormulaPolynomialBudget count +
    composedHistoryPolynomialBudget count

/-- Closed polynomial envelope for one structural flip equality surface. -/
def composedSingleFlipEqualityPolynomialBudget
    (count : Nat) : Nat :=
  explicitFamilyFormulaPolynomialBudget count +
    explicitFamilyFormulaPolynomialBudget count +
      (composedHistoryPolynomialBudget count +
        composedHistoryPolynomialBudget count)

/-- Closed polynomial envelope for one two-generator primitive query. -/
def composedPrimitiveQueryPolynomialBudget
    (count : Nat) : Nat :=
  composedSingleFlipEqualityPolynomialBudget count +
    composedSingleFlipEqualityPolynomialBudget count

/-- Polynomial certificate envelope for a witness variable at most n+2. -/
def composedCertificateAtomPolynomialBudget
    (count : Nat) : Nat :=
  (count + 2) + 2

/-- Closed polynomial representation budget for the complete added phase. -/
def composedClosurePhaseRepresentationPolynomialBudget
    (count : Nat) : Nat :=
  2 * composedStatePolynomialBudget count +
    (2 * composedCertificateAtomPolynomialBudget count +
      (3 * composedPrimitiveQueryPolynomialBudget count +
        composedStatePolynomialBudget count))

/-- The recursive history budget is exactly the closed polynomial expression. -/
theorem composedHistoryBinaryBudget_eq_polynomial
    (count : Nat) :
    composedHistoryBinaryBudget count =
      composedHistoryPolynomialBudget count := by
  unfold composedHistoryBinaryBudget
  unfold composedHistoryPolynomialBudget
  exact
    StructuralDecisionHistory.binaryBudget_closed
      (count + 2)
      (count + 2)

/-- The encoded square-state envelope is exactly polynomial. -/
theorem composedStateBinaryBudget_eq_polynomial
    (count : Nat) :
    composedStateBinaryBudget count =
      composedStatePolynomialBudget count := by
  unfold composedStateBinaryBudget
  unfold composedStatePolynomialBudget
  rw [
    explicitFamilyBinaryBudget_eq_polynomial,
    composedHistoryBinaryBudget_eq_polynomial
  ]

/-- The uniform single-flip equality budget is exactly polynomial. -/
theorem composedSingleFlipEqualityBinaryBudget_eq_polynomial
    (count : Nat) :
    composedSingleFlipEqualityBinaryBudget count =
      composedSingleFlipEqualityPolynomialBudget count := by
  unfold composedSingleFlipEqualityBinaryBudget
  unfold uniformGeneratedFlipEqualityCharge
  unfold composedSingleFlipEqualityPolynomialBudget
  rw [
    explicitFamilyBinaryBudget_eq_polynomial,
    composedHistoryBinaryBudget_eq_polynomial
  ]

/-- The two-generator primitive-query envelope is exactly polynomial. -/
theorem composedPrimitiveQueryBinaryBudget_eq_polynomial
    (count : Nat) :
    composedPrimitiveQueryBinaryBudget count =
      composedPrimitiveQueryPolynomialBudget count := by
  unfold composedPrimitiveQueryBinaryBudget
  unfold composedPrimitiveQueryPolynomialBudget
  rw [
    composedSingleFlipEqualityBinaryBudget_eq_polynomial
  ]

/-- The declared certificate envelope already is polynomial. -/
theorem composedCertificateAtomBinaryBudget_eq_polynomial
    (count : Nat) :
    composedCertificateAtomBinaryBudget count =
      composedCertificateAtomPolynomialBudget count := by
  rfl

/-- The full composition-phase representation budget is exactly polynomial. -/
theorem composedClosurePhaseRepresentationBudget_eq_polynomial
    (count : Nat) :
    composedClosurePhaseRepresentationBudget count =
      composedClosurePhaseRepresentationPolynomialBudget count := by
  unfold composedClosurePhaseRepresentationBudget
  unfold composedClosurePhaseRepresentationPolynomialBudget
  rw [
    composedStateBinaryBudget_eq_polynomial,
    composedCertificateAtomBinaryBudget_eq_polynomial,
    composedPrimitiveQueryBinaryBudget_eq_polynomial
  ]

/-- Unconditional polynomial representation bound for the composition phase. -/
theorem composedClosurePhaseRepresentationChargedCost_eq_polynomial
    (count : Nat) :
    composedClosurePhaseRepresentationChargedCost count =
      composedClosurePhaseRepresentationPolynomialBudget count := by
  exact
    Eq.trans
      (composedClosurePhaseRepresentationChargedCost_eq_budget
        count)
      (composedClosurePhaseRepresentationBudget_eq_polynomial
        count)

/-- The square-state history polynomial is monotone. -/
theorem composedHistoryPolynomialBudget_mono
    {small large : Nat}
    (smallLeLarge : small ≤ large) :
    composedHistoryPolynomialBudget small ≤
      composedHistoryPolynomialBudget large := by
  have plusTwoLe :
      small + 2 ≤ large + 2 :=
    Nat.add_le_add_right
      smallLeLarge
      2
  have plusFiveLe :
      (small + 2) + 3 ≤
        (large + 2) + 3 :=
    Nat.add_le_add_right
      plusTwoLe
      3
  unfold composedHistoryPolynomialBudget
  exact
    Nat.add_le_add_right
      (natMulLeMul
        plusTwoLe
        plusFiveLe)
      1

/-- The encoded square-state polynomial is monotone. -/
theorem composedStatePolynomialBudget_mono
    {small large : Nat}
    (smallLeLarge : small ≤ large) :
    composedStatePolynomialBudget small ≤
      composedStatePolynomialBudget large := by
  unfold composedStatePolynomialBudget
  exact
    Nat.add_le_add
      (explicitFamilyFormulaPolynomialBudget_mono
        smallLeLarge)
      (composedHistoryPolynomialBudget_mono
        smallLeLarge)

/-- The single-flip equality polynomial is monotone. -/
theorem composedSingleFlipEqualityPolynomialBudget_mono
    {small large : Nat}
    (smallLeLarge : small ≤ large) :
    composedSingleFlipEqualityPolynomialBudget small ≤
      composedSingleFlipEqualityPolynomialBudget large := by
  unfold composedSingleFlipEqualityPolynomialBudget
  have formulaLe :=
    explicitFamilyFormulaPolynomialBudget_mono
      smallLeLarge
  have historyLe :=
    composedHistoryPolynomialBudget_mono
      smallLeLarge
  exact
    Nat.add_le_add
      (Nat.add_le_add
        formulaLe
        formulaLe)
      (Nat.add_le_add
        historyLe
        historyLe)

/-- The two-generator primitive-query polynomial is monotone. -/
theorem composedPrimitiveQueryPolynomialBudget_mono
    {small large : Nat}
    (smallLeLarge : small ≤ large) :
    composedPrimitiveQueryPolynomialBudget small ≤
      composedPrimitiveQueryPolynomialBudget large := by
  unfold composedPrimitiveQueryPolynomialBudget
  have singleLe :=
    composedSingleFlipEqualityPolynomialBudget_mono
      smallLeLarge
  exact
    Nat.add_le_add
      singleLe
      singleLe

/-- The certificate polynomial is monotone. -/
theorem composedCertificateAtomPolynomialBudget_mono
    {small large : Nat}
    (smallLeLarge : small ≤ large) :
    composedCertificateAtomPolynomialBudget small ≤
      composedCertificateAtomPolynomialBudget large := by
  unfold composedCertificateAtomPolynomialBudget
  exact
    Nat.add_le_add_right
      (Nat.add_le_add_right
        smallLeLarge
        2)
      2

/-- The complete composition-phase polynomial is monotone. -/
theorem composedClosurePhaseRepresentationPolynomialBudget_mono
    {small large : Nat}
    (smallLeLarge : small ≤ large) :
    composedClosurePhaseRepresentationPolynomialBudget small ≤
      composedClosurePhaseRepresentationPolynomialBudget large := by
  have stateLe :=
    composedStatePolynomialBudget_mono
      smallLeLarge
  have certificateLe :=
    composedCertificateAtomPolynomialBudget_mono
      smallLeLarge
  have queryLe :=
    composedPrimitiveQueryPolynomialBudget_mono
      smallLeLarge
  unfold composedClosurePhaseRepresentationPolynomialBudget
  exact
    Nat.add_le_add
      (Nat.mul_le_mul_left
        2
        stateLe)
      (Nat.add_le_add
        (Nat.mul_le_mul_left
          2
          certificateLe)
        (Nat.add_le_add
          (Nat.mul_le_mul_left
            3
            queryLe)
          stateLe))

/-- Input-indexed polynomial envelope for the added composition phase. -/
def composedClosurePhaseInputIndexedPolynomialBudget
    (count : Nat) : Nat :=
  composedClosurePhaseRepresentationPolynomialBudget
    (explicitFamilyInputBitSize count)

/--
The added composition-phase representation charge is polynomially bounded by
the concrete binary size of the underlying input F(n).
-/
theorem composedClosurePhaseRepresentationChargedCost_le_inputIndexedPolynomial
    (count : Nat) :
    composedClosurePhaseRepresentationChargedCost count ≤
      composedClosurePhaseInputIndexedPolynomialBudget count := by
  rw [
    composedClosurePhaseRepresentationChargedCost_eq_polynomial
  ]
  exact
    composedClosurePhaseRepresentationPolynomialBudget_mono
      (explicitFamilyIndex_le_inputBitSize count)

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.composedHistoryPolynomialBudget
#print axioms ConstitutiveSearch.SAT.composedStatePolynomialBudget
#print axioms ConstitutiveSearch.SAT.composedSingleFlipEqualityPolynomialBudget
#print axioms ConstitutiveSearch.SAT.composedPrimitiveQueryPolynomialBudget
#print axioms ConstitutiveSearch.SAT.composedCertificateAtomPolynomialBudget
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseRepresentationPolynomialBudget
#print axioms ConstitutiveSearch.SAT.composedHistoryBinaryBudget_eq_polynomial
#print axioms ConstitutiveSearch.SAT.composedStateBinaryBudget_eq_polynomial
#print axioms ConstitutiveSearch.SAT.composedSingleFlipEqualityBinaryBudget_eq_polynomial
#print axioms ConstitutiveSearch.SAT.composedPrimitiveQueryBinaryBudget_eq_polynomial
#print axioms ConstitutiveSearch.SAT.composedCertificateAtomBinaryBudget_eq_polynomial
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseRepresentationBudget_eq_polynomial
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseRepresentationChargedCost_eq_polynomial
#print axioms ConstitutiveSearch.SAT.composedHistoryPolynomialBudget_mono
#print axioms ConstitutiveSearch.SAT.composedStatePolynomialBudget_mono
#print axioms ConstitutiveSearch.SAT.composedSingleFlipEqualityPolynomialBudget_mono
#print axioms ConstitutiveSearch.SAT.composedPrimitiveQueryPolynomialBudget_mono
#print axioms ConstitutiveSearch.SAT.composedCertificateAtomPolynomialBudget_mono
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseRepresentationPolynomialBudget_mono
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseInputIndexedPolynomialBudget
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseRepresentationChargedCost_le_inputIndexedPolynomial
/- AXIOM_AUDIT_END -/
