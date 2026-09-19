import Init.Omega
import ConstitutiveSearch.PolynomialExponentialSeparator
import ConstitutiveSearch.SAT.ExplicitFamilyCostPolynomials
import ConstitutiveSearch.SAT.TrajectoryDerivedClosure

/-!
# Complexity boundary of trajectory-derived closure on F(n)

TrajectoryDerivedClosure removes the external choice of primitive variables,
candidate states and fuel for the explicit SAT family F(n).  The certified
trajectory itself reconstructs:

* exactly n primitive variables;
* exactly 2n split-state candidates;
* closure fuel exactly n.

This module classifies the canonical recursive ClosureSearch budgets associated
with that fully endogenous schedule.

The concrete binary input size of F(n) is first shown polynomially bounded in
the family index n.  Candidate-count monotonicity then transfers the already
proved one-candidate exponential separator to the 2n-candidate trajectory
schedule.

Consequently, the recursive primitive-query and composition-candidate budget
functions induced by the trajectory are not InputPolynomiallyBounded in the
actual encoded input size of F(n).

Important qualification: ClosureSearchCosts provides upper envelopes for
executable counters.  Non-polynomiality of these canonical recursive envelopes
does not by itself prove a lower bound on the counters of any particular run.
It identifies a quantitative limitation of the current generic closure-search
accounting/search regime.
-/

namespace ConstitutiveSearch

/-- Polynomial boundedness is downward closed under pointwise domination. -/
theorem polynomiallyBounded_of_le
    {lower upper : Nat → Nat}
    (upperBounded :
      PolynomiallyBounded upper)
    (lowerLe :
      ∀ n : Nat,
        lower n ≤ upper n) :
    PolynomiallyBounded lower := by
  rcases upperBounded with
    ⟨envelope, upperLe⟩
  exact
    ⟨envelope,
      fun n =>
        Nat.le_trans
          (lowerLe n)
          (upperLe n)⟩

/--
If the concrete input-size function is itself bounded by one CostPolynomial in
the family index, then an input-indexed polynomial cost is polynomial in that
family index as well.
-/
theorem inputPolynomiallyBounded_to_polynomiallyBounded
    {inputBits cost : Nat → Nat}
    (inputEnvelope : CostPolynomial)
    (inputLe :
      ∀ n : Nat,
        inputBits n ≤
          inputEnvelope.eval n)
    (bounded :
      InputPolynomiallyBounded
        inputBits
        cost) :
    PolynomiallyBounded cost := by
  rcases bounded with
    ⟨costEnvelope, costLe⟩
  refine
    ⟨CostPolynomial.substitute
        costEnvelope
        inputEnvelope,
      ?_⟩
  intro n
  rw [CostPolynomial.eval_substitute]
  exact
    Nat.le_trans
      (costLe n)
      (costEnvelope.eval_mono
        (inputLe n))

/-- Primitive recursive closure budget is monotone in candidate count. -/
theorem closurePrimitiveQueryBudget_mono_candidateCount
    {small large : Nat}
    (candidateLe :
      small ≤ large) :
    ∀ fuel : Nat,
      closurePrimitiveQueryBudget small fuel ≤
        closurePrimitiveQueryBudget large fuel := by
  intro fuel
  induction fuel with
  | zero =>
      exact Nat.le_refl 0
  | succ fuel inductionHypothesis =>
      change
        viaPrimitiveQueryBudget
              (closurePrimitiveQueryBudget small fuel)
              small +
            1 ≤
          viaPrimitiveQueryBudget
              (closurePrimitiveQueryBudget large fuel)
              large +
            1
      rw [
        viaPrimitiveQueryBudget_closed,
        viaPrimitiveQueryBudget_closed
      ]
      exact
        Nat.add_le_add_right
          (PolynomiallyBounded.natMulLeMul
            candidateLe
            (Nat.add_le_add
              inductionHypothesis
              inductionHypothesis))
          1

/-- Composition-candidate recursive closure budget is monotone in candidate count. -/
theorem closureCompositionCandidateBudget_mono_candidateCount
    {small large : Nat}
    (candidateLe :
      small ≤ large) :
    ∀ fuel : Nat,
      closureCompositionCandidateBudget small fuel ≤
        closureCompositionCandidateBudget large fuel := by
  intro fuel
  induction fuel with
  | zero =>
      exact Nat.le_refl 0
  | succ fuel inductionHypothesis =>
      change
        viaCompositionCandidateBudget
            (closureCompositionCandidateBudget small fuel)
            small ≤
          viaCompositionCandidateBudget
            (closureCompositionCandidateBudget large fuel)
            large
      rw [
        viaCompositionCandidateBudget_closed,
        viaCompositionCandidateBudget_closed
      ]
      exact
        PolynomiallyBounded.natMulLeMul
          candidateLe
          (Nat.add_le_add_right
            (Nat.add_le_add
              inductionHypothesis
              inductionHypothesis)
            1)

namespace SAT

/--
The actual binary input size of F(n) is bounded by the already reified formula
cost polynomial evaluated at n.
-/
theorem explicitFamilyInputBitSize_le_indexPolynomial
    (count : Nat) :
    explicitFamilyInputBitSize count ≤
      explicitFamilyFormulaCostPolynomial.eval count := by
  unfold explicitFamilyInputBitSize
  calc
    Cnf.binarySize
          (explicitStackedSymmetricFamily count)
        ≤
      explicitFamilyBinaryBudget count :=
        explicitFamily_binarySize_le_budget
          count
    _ =
      explicitFamilyFormulaPolynomialBudget count :=
        explicitFamilyBinaryBudget_eq_polynomial
          count
    _ =
      explicitFamilyFormulaCostPolynomial.eval count :=
        (explicitFamilyFormulaCostPolynomial_eval
          count).symm

/--
Canonical primitive-query recursive budget of the trajectory-derived closure
schedule.
-/
def explicitFamilyTrajectoryPrimitiveClosureBudget
    (count : Nat) : Nat :=
  closurePrimitiveQueryBudget
    (explicitFamilyTrajectoryClosureCandidates count).length
    (explicitFamilyTrajectoryClosureFuel count)

/--
Canonical composition-candidate recursive budget of the same endogenous
schedule.
-/
def explicitFamilyTrajectoryCompositionClosureBudget
    (count : Nat) : Nat :=
  closureCompositionCandidateBudget
    (explicitFamilyTrajectoryClosureCandidates count).length
    (explicitFamilyTrajectoryClosureFuel count)

/-- The derived primitive budget uses exactly 2n candidates and fuel n. -/
theorem explicitFamilyTrajectoryPrimitiveClosureBudget_eq
    (count : Nat) :
    explicitFamilyTrajectoryPrimitiveClosureBudget count =
      closurePrimitiveQueryBudget
        (2 * count)
        count := by
  unfold explicitFamilyTrajectoryPrimitiveClosureBudget
  rw [
    explicitFamilyTrajectoryClosureCandidates_length,
    explicitFamilyTrajectoryClosureFuel_eq
  ]

/-- The derived composition budget uses exactly the same 2n/n schedule. -/
theorem explicitFamilyTrajectoryCompositionClosureBudget_eq
    (count : Nat) :
    explicitFamilyTrajectoryCompositionClosureBudget count =
      closureCompositionCandidateBudget
        (2 * count)
        count := by
  unfold explicitFamilyTrajectoryCompositionClosureBudget
  rw [
    explicitFamilyTrajectoryClosureCandidates_length,
    explicitFamilyTrajectoryClosureFuel_eq
  ]

/--
The one-candidate identity-fuel primitive budget is pointwise below the
trajectory-derived 2n-candidate budget.
-/
theorem oneCandidatePrimitive_le_explicitFamilyTrajectoryBudget
    (count : Nat) :
    closurePrimitiveQueryBudget 1 count ≤
      explicitFamilyTrajectoryPrimitiveClosureBudget count := by
  rw [
    explicitFamilyTrajectoryPrimitiveClosureBudget_eq
  ]
  cases count with
  | zero =>
      rfl
  | succ count =>
      exact
        closurePrimitiveQueryBudget_mono_candidateCount
          (small := 1)
          (large := 2 * (count + 1))
          (by omega)
          (count + 1)

/--
The analogous one-candidate composition budget lies below the trajectory
schedule's composition envelope.
-/
theorem oneCandidateComposition_le_explicitFamilyTrajectoryBudget
    (count : Nat) :
    closureCompositionCandidateBudget 1 count ≤
      explicitFamilyTrajectoryCompositionClosureBudget count := by
  rw [
    explicitFamilyTrajectoryCompositionClosureBudget_eq
  ]
  cases count with
  | zero =>
      rfl
  | succ count =>
      exact
        closureCompositionCandidateBudget_mono_candidateCount
          (small := 1)
          (large := 2 * (count + 1))
          (by omega)
          (count + 1)

/--
As a function of the family index n, the endogenous primitive recursive budget
is not polynomially bounded.
-/
theorem explicitFamilyTrajectoryPrimitiveClosureBudget_not_polynomiallyBounded :
    ¬
      PolynomiallyBounded
        explicitFamilyTrajectoryPrimitiveClosureBudget := by
  intro bounded
  have oneCandidateBounded :
      PolynomiallyBounded
        (fun count =>
          closurePrimitiveQueryBudget
            1
            count) :=
    polynomiallyBounded_of_le
      bounded
      oneCandidatePrimitive_le_explicitFamilyTrajectoryBudget
  exact
    closurePrimitiveOneCandidateIdentityFuel_not_polynomiallyBounded
      oneCandidateBounded

/--
The endogenous composition-candidate recursive budget is likewise not
polynomially bounded in n.
-/
theorem explicitFamilyTrajectoryCompositionClosureBudget_not_polynomiallyBounded :
    ¬
      PolynomiallyBounded
        explicitFamilyTrajectoryCompositionClosureBudget := by
  intro bounded
  have oneCandidateBounded :
      PolynomiallyBounded
        (fun count =>
          closureCompositionCandidateBudget
            1
            count) :=
    polynomiallyBounded_of_le
      bounded
      oneCandidateComposition_le_explicitFamilyTrajectoryBudget
  exact
    closureCompositionOneCandidateIdentityFuel_not_polynomiallyBounded
      oneCandidateBounded

/--
Because the actual encoded input size of F(n) is polynomially bounded in n,
the trajectory-derived primitive recursive budget cannot become polynomial by
reindexing it with explicitFamilyInputBitSize.
-/
theorem explicitFamilyTrajectoryPrimitiveClosureBudget_not_inputPolynomiallyBounded :
    ¬
      InputPolynomiallyBounded
        explicitFamilyInputBitSize
        explicitFamilyTrajectoryPrimitiveClosureBudget := by
  intro bounded
  have indexBounded :
      PolynomiallyBounded
        explicitFamilyTrajectoryPrimitiveClosureBudget :=
    inputPolynomiallyBounded_to_polynomiallyBounded
      explicitFamilyFormulaCostPolynomial
      explicitFamilyInputBitSize_le_indexPolynomial
      bounded
  exact
    explicitFamilyTrajectoryPrimitiveClosureBudget_not_polynomiallyBounded
      indexBounded

/--
The same reindexing argument excludes an input-polynomial envelope for the
trajectory-derived composition-candidate recursive budget.
-/
theorem explicitFamilyTrajectoryCompositionClosureBudget_not_inputPolynomiallyBounded :
    ¬
      InputPolynomiallyBounded
        explicitFamilyInputBitSize
        explicitFamilyTrajectoryCompositionClosureBudget := by
  intro bounded
  have indexBounded :
      PolynomiallyBounded
        explicitFamilyTrajectoryCompositionClosureBudget :=
    inputPolynomiallyBounded_to_polynomiallyBounded
      explicitFamilyFormulaCostPolynomial
      explicitFamilyInputBitSize_le_indexPolynomial
      bounded
  exact
    explicitFamilyTrajectoryCompositionClosureBudget_not_polynomiallyBounded
      indexBounded

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.polynomiallyBounded_of_le
#print axioms ConstitutiveSearch.inputPolynomiallyBounded_to_polynomiallyBounded
#print axioms ConstitutiveSearch.closurePrimitiveQueryBudget_mono_candidateCount
#print axioms ConstitutiveSearch.closureCompositionCandidateBudget_mono_candidateCount
#print axioms ConstitutiveSearch.SAT.explicitFamilyInputBitSize_le_indexPolynomial
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryPrimitiveClosureBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryCompositionClosureBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryPrimitiveClosureBudget_eq
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryCompositionClosureBudget_eq
#print axioms ConstitutiveSearch.SAT.oneCandidatePrimitive_le_explicitFamilyTrajectoryBudget
#print axioms ConstitutiveSearch.SAT.oneCandidateComposition_le_explicitFamilyTrajectoryBudget
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryPrimitiveClosureBudget_not_polynomiallyBounded
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryCompositionClosureBudget_not_polynomiallyBounded
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryPrimitiveClosureBudget_not_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.explicitFamilyTrajectoryCompositionClosureBudget_not_inputPolynomiallyBounded
/- AXIOM_AUDIT_END -/
