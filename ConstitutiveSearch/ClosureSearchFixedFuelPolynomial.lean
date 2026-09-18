import ConstitutiveSearch.ClosureSearchPolynomialComplexity
import ConstitutiveSearch.ConstitutiveComplexityInputPolynomial

/-!
# Polynomial closure-search budgets for every fixed fuel

ClosureSearchGrowth gives exact recursive control-flow budgets.  Fuel two was
already isolated explicitly.  Here the same construction is generalized to
every fixed fuel value.

For each natural fuel f, this module builds two finite CostPolynomial terms in
the candidate-count variable:
* one exactly evaluating to closurePrimitiveQueryBudget m f;
* one exactly evaluating to closureCompositionCandidateBudget m f.

Consequently, when candidateCount <= inputBits and fuel is fixed independently
of the input, both executable search counters admit polynomial envelopes in
inputBits.

This does not claim polynomiality when fuel itself grows with the input.
-/

namespace ConstitutiveSearch

/-- Exact candidate-count polynomial for primitive-query budget at fixed fuel. -/
def closurePrimitiveFixedFuelPolynomial : Nat → CostPolynomial
  | 0 =>
      .constant 0
  | fuel + 1 =>
      .add
        (.mul
          .input
          (.add
            (closurePrimitiveFixedFuelPolynomial fuel)
            (closurePrimitiveFixedFuelPolynomial fuel)))
        (.constant 1)

/-- Exact candidate-count polynomial for composition-candidate budget at fixed fuel. -/
def closureCompositionFixedFuelPolynomial : Nat → CostPolynomial
  | 0 =>
      .constant 0
  | fuel + 1 =>
      .mul
        .input
        (.add
          (.add
            (closureCompositionFixedFuelPolynomial fuel)
            (closureCompositionFixedFuelPolynomial fuel))
          (.constant 1))

/-- Primitive-query polynomial evaluates exactly to the recursive closure budget. -/
theorem closurePrimitiveFixedFuelPolynomial_eval :
    ∀ (fuel candidateCount : Nat),
      (closurePrimitiveFixedFuelPolynomial fuel).eval candidateCount =
        closurePrimitiveQueryBudget candidateCount fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro candidateCount
      rfl
  | succ fuel inductionHypothesis =>
      intro candidateCount
      change
        candidateCount *
              ((closurePrimitiveFixedFuelPolynomial fuel).eval candidateCount +
                (closurePrimitiveFixedFuelPolynomial fuel).eval candidateCount) +
            1 =
          closurePrimitiveQueryBudget
            candidateCount
            (fuel + 1)
      rw [
        inductionHypothesis candidateCount
      ]
      rw [show
        closurePrimitiveQueryBudget
            candidateCount
            (fuel + 1) =
          viaPrimitiveQueryBudget
              (closurePrimitiveQueryBudget candidateCount fuel)
              candidateCount +
            1 from rfl]
      rw [
        viaPrimitiveQueryBudget_closed
      ]

/-- Composition-candidate polynomial evaluates exactly to its recursive budget. -/
theorem closureCompositionFixedFuelPolynomial_eval :
    ∀ (fuel candidateCount : Nat),
      (closureCompositionFixedFuelPolynomial fuel).eval candidateCount =
        closureCompositionCandidateBudget candidateCount fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro candidateCount
      rfl
  | succ fuel inductionHypothesis =>
      intro candidateCount
      change
        candidateCount *
            ((closureCompositionFixedFuelPolynomial fuel).eval candidateCount +
                (closureCompositionFixedFuelPolynomial fuel).eval candidateCount +
              1) =
          closureCompositionCandidateBudget
            candidateCount
            (fuel + 1)
      rw [
        inductionHypothesis candidateCount
      ]
      rw [show
        closureCompositionCandidateBudget
            candidateCount
            (fuel + 1) =
          viaCompositionCandidateBudget
            (closureCompositionCandidateBudget candidateCount fuel)
            candidateCount from rfl]
      exact
        (viaCompositionCandidateBudget_closed
          (closureCompositionCandidateBudget
            candidateCount
            fuel)
          candidateCount).symm

/-- For every fixed fuel, primitive-query budget as a function of candidates is polynomial. -/
theorem closurePrimitiveFixedFuel_polynomiallyBounded
    (fuel : Nat) :
    PolynomiallyBounded
      (fun candidateCount =>
        closurePrimitiveQueryBudget
          candidateCount
          fuel) :=
  ⟨closurePrimitiveFixedFuelPolynomial fuel,
    fun candidateCount =>
      Nat.le_of_eq
        (closurePrimitiveFixedFuelPolynomial_eval
          fuel
          candidateCount).symm⟩

/-- For every fixed fuel, composition-candidate budget is polynomial in candidates. -/
theorem closureCompositionFixedFuel_polynomiallyBounded
    (fuel : Nat) :
    PolynomiallyBounded
      (fun candidateCount =>
        closureCompositionCandidateBudget
          candidateCount
          fuel) :=
  ⟨closureCompositionFixedFuelPolynomial fuel,
    fun candidateCount =>
      Nat.le_of_eq
        (closureCompositionFixedFuelPolynomial_eval
          fuel
          candidateCount).symm⟩

/--
If the candidate list is bounded by inputBits, any fixed-fuel primitive-query
budget is bounded by the same fixed-fuel polynomial evaluated at inputBits.
-/
theorem closurePrimitiveFixedFuel_le_inputPolynomial
    (fuel candidateCount inputBits : Nat)
    (candidateLe :
      candidateCount ≤ inputBits) :
    closurePrimitiveQueryBudget candidateCount fuel ≤
      (closurePrimitiveFixedFuelPolynomial fuel).eval inputBits := by
  calc
    closurePrimitiveQueryBudget candidateCount fuel
        =
      (closurePrimitiveFixedFuelPolynomial fuel).eval candidateCount :=
        (closurePrimitiveFixedFuelPolynomial_eval
          fuel
          candidateCount).symm
    _ ≤
      (closurePrimitiveFixedFuelPolynomial fuel).eval inputBits :=
        CostPolynomial.eval_mono
          (closurePrimitiveFixedFuelPolynomial fuel)
          candidateLe

/--
The analogous fixed-fuel composition-candidate budget is polynomially bounded
by inputBits.
-/
theorem closureCompositionFixedFuel_le_inputPolynomial
    (fuel candidateCount inputBits : Nat)
    (candidateLe :
      candidateCount ≤ inputBits) :
    closureCompositionCandidateBudget candidateCount fuel ≤
      (closureCompositionFixedFuelPolynomial fuel).eval inputBits := by
  calc
    closureCompositionCandidateBudget candidateCount fuel
        =
      (closureCompositionFixedFuelPolynomial fuel).eval candidateCount :=
        (closureCompositionFixedFuelPolynomial_eval
          fuel
          candidateCount).symm
    _ ≤
      (closureCompositionFixedFuelPolynomial fuel).eval inputBits :=
        CostPolynomial.eval_mono
          (closureCompositionFixedFuelPolynomial fuel)
          candidateLe

/-- Actual executable primitive-query count inherits the fixed-fuel polynomial envelope. -/
theorem searchTransportClosureFixedFuel_primitiveQueries_le_inputPolynomial
    {State : Type}
    {Generator : State → State → Type}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (fuel inputBits : Nat)
    (candidateLe :
      candidates.length ≤ inputBits)
    (source target : State) :
    (searchTransportClosureBounded
      primitive
      candidates
      fuel
      source
      target).stats.primitiveQueries ≤
      (closurePrimitiveFixedFuelPolynomial fuel).eval inputBits := by
  exact
    Nat.le_trans
      (searchTransportClosureBounded_primitiveQueries_le
        primitive
        candidates
        fuel
        source
        target)
      (closurePrimitiveFixedFuel_le_inputPolynomial
        fuel
        candidates.length
        inputBits
        candidateLe)

/-- Actual executable composition-candidate count inherits the polynomial envelope. -/
theorem searchTransportClosureFixedFuel_compositionCandidates_le_inputPolynomial
    {State : Type}
    {Generator : State → State → Type}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (fuel inputBits : Nat)
    (candidateLe :
      candidates.length ≤ inputBits)
    (source target : State) :
    (searchTransportClosureBounded
      primitive
      candidates
      fuel
      source
      target).stats.compositionCandidates ≤
      (closureCompositionFixedFuelPolynomial fuel).eval inputBits := by
  exact
    Nat.le_trans
      (searchTransportClosureBounded_compositionCandidates_le
        primitive
        candidates
        fuel
        source
        target)
      (closureCompositionFixedFuel_le_inputPolynomial
        fuel
        candidates.length
        inputBits
        candidateLe)

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.closurePrimitiveFixedFuelPolynomial
#print axioms ConstitutiveSearch.closureCompositionFixedFuelPolynomial
#print axioms ConstitutiveSearch.closurePrimitiveFixedFuelPolynomial_eval
#print axioms ConstitutiveSearch.closureCompositionFixedFuelPolynomial_eval
#print axioms ConstitutiveSearch.closurePrimitiveFixedFuel_polynomiallyBounded
#print axioms ConstitutiveSearch.closureCompositionFixedFuel_polynomiallyBounded
#print axioms ConstitutiveSearch.closurePrimitiveFixedFuel_le_inputPolynomial
#print axioms ConstitutiveSearch.closureCompositionFixedFuel_le_inputPolynomial
#print axioms ConstitutiveSearch.searchTransportClosureFixedFuel_primitiveQueries_le_inputPolynomial
#print axioms ConstitutiveSearch.searchTransportClosureFixedFuel_compositionCandidates_le_inputPolynomial
/- AXIOM_AUDIT_END -/
