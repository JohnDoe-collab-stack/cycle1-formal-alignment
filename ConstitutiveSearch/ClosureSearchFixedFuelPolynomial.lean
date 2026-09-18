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

/-- Structural degree of the exact primitive-query polynomial is the fuel. -/
theorem closurePrimitiveFixedFuelPolynomial_degree :
    ∀ fuel : Nat,
      (closurePrimitiveFixedFuelPolynomial fuel).degree =
        fuel
  | 0 =>
      rfl
  | fuel + 1 => by
      change
        Nat.max
            (1 +
              Nat.max
                (closurePrimitiveFixedFuelPolynomial fuel).degree
                (closurePrimitiveFixedFuelPolynomial fuel).degree)
            0 =
          fuel + 1
      rw [
        closurePrimitiveFixedFuelPolynomial_degree fuel
      ]
      have selfMax :
          Nat.max fuel fuel = fuel :=
        Nat.max_eq_left
          (Nat.le_refl fuel)
      rw [selfMax]
      have outerMax :
          Nat.max (1 + fuel) 0 =
            1 + fuel :=
        Nat.max_eq_left
          (Nat.zero_le _)
      rw [outerMax]
      exact Nat.add_comm 1 fuel

/-- Structural degree of the exact composition-candidate polynomial is the fuel. -/
theorem closureCompositionFixedFuelPolynomial_degree :
    ∀ fuel : Nat,
      (closureCompositionFixedFuelPolynomial fuel).degree =
        fuel
  | 0 =>
      rfl
  | fuel + 1 => by
      change
        1 +
            Nat.max
              (Nat.max
                (closureCompositionFixedFuelPolynomial fuel).degree
                (closureCompositionFixedFuelPolynomial fuel).degree)
              0 =
          fuel + 1
      rw [
        closureCompositionFixedFuelPolynomial_degree fuel
      ]
      have selfMax :
          Nat.max fuel fuel = fuel :=
        Nat.max_eq_left
          (Nat.le_refl fuel)
      rw [selfMax]
      have outerMax :
          Nat.max fuel 0 = fuel :=
        Nat.max_eq_left
          (Nat.zero_le _)
      rw [outerMax]
      exact Nat.add_comm 1 fuel

/--
An unbounded fuel family therefore produces canonical exact closure polynomials
of unbounded structural degree.
-/
theorem closurePrimitiveFixedFuelPolynomial_degree_unbounded
    (fuel : Nat → Nat)
    (fuelUnbounded :
      ∀ cap : Nat,
        ∃ n : Nat,
          cap < fuel n) :
    ∀ cap : Nat,
      ∃ n : Nat,
        cap <
          (closurePrimitiveFixedFuelPolynomial
            (fuel n)).degree := by
  intro cap
  rcases fuelUnbounded cap with
    ⟨n, capLt⟩
  exact
    ⟨n, by
      rw [closurePrimitiveFixedFuelPolynomial_degree]
      exact capLt⟩

/--
The same unbounded-degree boundary holds for the exact composition-candidate
polynomials.
-/
theorem closureCompositionFixedFuelPolynomial_degree_unbounded
    (fuel : Nat → Nat)
    (fuelUnbounded :
      ∀ cap : Nat,
        ∃ n : Nat,
          cap < fuel n) :
    ∀ cap : Nat,
      ∃ n : Nat,
        cap <
          (closureCompositionFixedFuelPolynomial
            (fuel n)).degree := by
  intro cap
  rcases fuelUnbounded cap with
    ⟨n, capLt⟩
  exact
    ⟨n, by
      rw [closureCompositionFixedFuelPolynomial_degree]
      exact capLt⟩

/--
Uniformly bounded fuel is equivalent to a uniform structural-degree bound on
the exact primitive-query polynomial family.
-/
theorem closurePrimitiveFixedFuelPolynomial_degree_bounded_iff
    (fuel : Nat → Nat) :
    (∃ fuelCap : Nat,
      ∀ n : Nat,
        fuel n ≤ fuelCap) ↔
    (∃ degreeCap : Nat,
      ∀ n : Nat,
        (closurePrimitiveFixedFuelPolynomial
          (fuel n)).degree ≤ degreeCap) := by
  constructor
  · intro bounded
    rcases bounded with
      ⟨fuelCap, fuelLe⟩
    exact
      ⟨fuelCap,
        fun n => by
          rw [closurePrimitiveFixedFuelPolynomial_degree]
          exact fuelLe n⟩
  · intro bounded
    rcases bounded with
      ⟨degreeCap, degreeLe⟩
    exact
      ⟨degreeCap,
        fun n => by
          rw [← closurePrimitiveFixedFuelPolynomial_degree
            (fuel n)]
          exact degreeLe n⟩

/--
The analogous uniform-degree characterization holds for the exact
composition-candidate polynomial family.
-/
theorem closureCompositionFixedFuelPolynomial_degree_bounded_iff
    (fuel : Nat → Nat) :
    (∃ fuelCap : Nat,
      ∀ n : Nat,
        fuel n ≤ fuelCap) ↔
    (∃ degreeCap : Nat,
      ∀ n : Nat,
        (closureCompositionFixedFuelPolynomial
          (fuel n)).degree ≤ degreeCap) := by
  constructor
  · intro bounded
    rcases bounded with
      ⟨fuelCap, fuelLe⟩
    exact
      ⟨fuelCap,
        fun n => by
          rw [closureCompositionFixedFuelPolynomial_degree]
          exact fuelLe n⟩
  · intro bounded
    rcases bounded with
      ⟨degreeCap, degreeLe⟩
    exact
      ⟨degreeCap,
        fun n => by
          rw [← closureCompositionFixedFuelPolynomial_degree
            (fuel n)]
          exact degreeLe n⟩

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

/--
If candidateCount itself is polynomially bounded in the concrete input size,
then every fixed-fuel primitive-query budget is input-polynomially bounded.
-/
theorem closurePrimitiveFixedFuel_of_candidateInputPolynomial
    (fuel : Nat)
    {inputBits candidateCount : Nat → Nat}
    (candidateBounded :
      InputPolynomiallyBounded
        inputBits
        candidateCount) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        closurePrimitiveQueryBudget
          (candidateCount n)
          fuel) := by
  have evaluated :
      InputPolynomiallyBounded
        inputBits
        (fun n =>
          (closurePrimitiveFixedFuelPolynomial fuel).eval
            (candidateCount n)) :=
    InputPolynomiallyBounded.apply_polynomial
      candidateBounded
      (closurePrimitiveFixedFuelPolynomial fuel)
  simpa only [
    closurePrimitiveFixedFuelPolynomial_eval
  ] using evaluated

/--
The same closure property holds for fixed-fuel composition-candidate budgets.
-/
theorem closureCompositionFixedFuel_of_candidateInputPolynomial
    (fuel : Nat)
    {inputBits candidateCount : Nat → Nat}
    (candidateBounded :
      InputPolynomiallyBounded
        inputBits
        candidateCount) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        closureCompositionCandidateBudget
          (candidateCount n)
          fuel) := by
  have evaluated :
      InputPolynomiallyBounded
        inputBits
        (fun n =>
          (closureCompositionFixedFuelPolynomial fuel).eval
            (candidateCount n)) :=
    InputPolynomiallyBounded.apply_polynomial
      candidateBounded
      (closureCompositionFixedFuelPolynomial fuel)
  simpa only [
    closureCompositionFixedFuelPolynomial_eval
  ] using evaluated

/--
For a family of candidate lists whose lengths are input-polynomially bounded,
the actual executable primitive-query count is input-polynomially bounded at
every fixed fuel.
-/
theorem searchTransportClosureFixedFuel_primitiveQueries_of_candidateInputPolynomial
    {State : Type}
    {Generator : State → State → Type}
    (primitive : RelationSearch Generator)
    (candidates : Nat → List State)
    (fuel : Nat)
    {inputBits : Nat → Nat}
    (candidateBounded :
      InputPolynomiallyBounded
        inputBits
        (fun n =>
          (candidates n).length))
    (source target : Nat → State) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (searchTransportClosureBounded
          primitive
          (candidates n)
          fuel
          (source n)
          (target n)).stats.primitiveQueries) := by
  rcases
      closurePrimitiveFixedFuel_of_candidateInputPolynomial
        fuel
        candidateBounded with
    ⟨envelope, budgetLe⟩
  refine
    ⟨envelope, ?_⟩
  intro n
  exact
    Nat.le_trans
      (searchTransportClosureBounded_primitiveQueries_le
        primitive
        (candidates n)
        fuel
        (source n)
        (target n))
      (budgetLe n)

/--
For the same candidate-list family, the actual executable composition-candidate
count is input-polynomially bounded at every fixed fuel.
-/
theorem searchTransportClosureFixedFuel_compositionCandidates_of_candidateInputPolynomial
    {State : Type}
    {Generator : State → State → Type}
    (primitive : RelationSearch Generator)
    (candidates : Nat → List State)
    (fuel : Nat)
    {inputBits : Nat → Nat}
    (candidateBounded :
      InputPolynomiallyBounded
        inputBits
        (fun n =>
          (candidates n).length))
    (source target : Nat → State) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (searchTransportClosureBounded
          primitive
          (candidates n)
          fuel
          (source n)
          (target n)).stats.compositionCandidates) := by
  rcases
      closureCompositionFixedFuel_of_candidateInputPolynomial
        fuel
        candidateBounded with
    ⟨envelope, budgetLe⟩
  refine
    ⟨envelope, ?_⟩
  intro n
  exact
    Nat.le_trans
      (searchTransportClosureBounded_compositionCandidates_le
        primitive
        (candidates n)
        fuel
        (source n)
        (target n))
      (budgetLe n)

/-- Candidate scanning is monotone in the recursive primitive-query budget. -/
theorem viaPrimitiveQueryBudget_mono_recursive
    {small large : Nat}
    (recursiveLe : small ≤ large)
    (candidateCount : Nat) :
    viaPrimitiveQueryBudget small candidateCount ≤
      viaPrimitiveQueryBudget large candidateCount := by
  rw [
    viaPrimitiveQueryBudget_closed,
    viaPrimitiveQueryBudget_closed
  ]
  exact
    Nat.mul_le_mul_left
      candidateCount
      (Nat.add_le_add
        recursiveLe
        recursiveLe)

/-- Candidate scanning is monotone in the recursive composition budget. -/
theorem viaCompositionCandidateBudget_mono_recursive
    {small large : Nat}
    (recursiveLe : small ≤ large)
    (candidateCount : Nat) :
    viaCompositionCandidateBudget small candidateCount ≤
      viaCompositionCandidateBudget large candidateCount := by
  rw [
    viaCompositionCandidateBudget_closed,
    viaCompositionCandidateBudget_closed
  ]
  exact
    Nat.mul_le_mul_left
      candidateCount
      (Nat.add_le_add_right
        (Nat.add_le_add
          recursiveLe
          recursiveLe)
        1)

/-- Primitive-query closure budget is monotone in fuel. -/
theorem closurePrimitiveQueryBudget_mono_fuel
    (candidateCount : Nat) :
    ∀ {smallFuel largeFuel : Nat},
      smallFuel ≤ largeFuel →
        closurePrimitiveQueryBudget candidateCount smallFuel ≤
          closurePrimitiveQueryBudget candidateCount largeFuel := by
  intro smallFuel largeFuel fuelLe
  induction largeFuel generalizing smallFuel with
  | zero =>
      cases smallFuel with
      | zero =>
          exact Nat.le_refl 0
      | succ smallFuel =>
          cases fuelLe
  | succ largeFuel inductionHypothesis =>
      cases smallFuel with
      | zero =>
          exact Nat.zero_le _
      | succ smallFuel =>
          have smallerFuelLe :
              smallFuel ≤ largeFuel :=
            Nat.le_of_succ_le_succ fuelLe
          have recursiveLe :
              closurePrimitiveQueryBudget candidateCount smallFuel ≤
                closurePrimitiveQueryBudget candidateCount largeFuel :=
            inductionHypothesis smallerFuelLe
          change
            viaPrimitiveQueryBudget
                  (closurePrimitiveQueryBudget
                    candidateCount
                    smallFuel)
                  candidateCount +
                1 ≤
              viaPrimitiveQueryBudget
                  (closurePrimitiveQueryBudget
                    candidateCount
                    largeFuel)
                  candidateCount +
                1
          exact
            Nat.add_le_add_right
              (viaPrimitiveQueryBudget_mono_recursive
                recursiveLe
                candidateCount)
              1

/-- Composition-candidate closure budget is monotone in fuel. -/
theorem closureCompositionCandidateBudget_mono_fuel
    (candidateCount : Nat) :
    ∀ {smallFuel largeFuel : Nat},
      smallFuel ≤ largeFuel →
        closureCompositionCandidateBudget candidateCount smallFuel ≤
          closureCompositionCandidateBudget candidateCount largeFuel := by
  intro smallFuel largeFuel fuelLe
  induction largeFuel generalizing smallFuel with
  | zero =>
      cases smallFuel with
      | zero =>
          exact Nat.le_refl 0
      | succ smallFuel =>
          cases fuelLe
  | succ largeFuel inductionHypothesis =>
      cases smallFuel with
      | zero =>
          exact Nat.zero_le _
      | succ smallFuel =>
          have smallerFuelLe :
              smallFuel ≤ largeFuel :=
            Nat.le_of_succ_le_succ fuelLe
          have recursiveLe :
              closureCompositionCandidateBudget candidateCount smallFuel ≤
                closureCompositionCandidateBudget candidateCount largeFuel :=
            inductionHypothesis smallerFuelLe
          change
            viaCompositionCandidateBudget
                (closureCompositionCandidateBudget
                  candidateCount
                  smallFuel)
                candidateCount ≤
              viaCompositionCandidateBudget
                (closureCompositionCandidateBudget
                  candidateCount
                  largeFuel)
                candidateCount
          exact
            viaCompositionCandidateBudget_mono_recursive
              recursiveLe
              candidateCount

/--
A variable fuel uniformly bounded by one fixed cap preserves primitive-query
input-polynomiality whenever candidate growth is input-polynomial.
-/
theorem closurePrimitiveBoundedFuel_of_candidateInputPolynomial
    (fuelCap : Nat)
    {inputBits candidateCount fuel : Nat → Nat}
    (candidateBounded :
      InputPolynomiallyBounded
        inputBits
        candidateCount)
    (fuelBounded :
      ∀ n : Nat,
        fuel n ≤ fuelCap) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        closurePrimitiveQueryBudget
          (candidateCount n)
          (fuel n)) := by
  rcases
      closurePrimitiveFixedFuel_of_candidateInputPolynomial
        fuelCap
        candidateBounded with
    ⟨envelope, capLe⟩
  refine
    ⟨envelope, ?_⟩
  intro n
  exact
    Nat.le_trans
      (closurePrimitiveQueryBudget_mono_fuel
        (candidateCount n)
        (fuelBounded n))
      (capLe n)

/--
The analogous uniformly bounded variable-fuel regime preserves polynomiality of
composition-candidate budgets.
-/
theorem closureCompositionBoundedFuel_of_candidateInputPolynomial
    (fuelCap : Nat)
    {inputBits candidateCount fuel : Nat → Nat}
    (candidateBounded :
      InputPolynomiallyBounded
        inputBits
        candidateCount)
    (fuelBounded :
      ∀ n : Nat,
        fuel n ≤ fuelCap) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        closureCompositionCandidateBudget
          (candidateCount n)
          (fuel n)) := by
  rcases
      closureCompositionFixedFuel_of_candidateInputPolynomial
        fuelCap
        candidateBounded with
    ⟨envelope, capLe⟩
  refine
    ⟨envelope, ?_⟩
  intro n
  exact
    Nat.le_trans
      (closureCompositionCandidateBudget_mono_fuel
        (candidateCount n)
        (fuelBounded n))
      (capLe n)

/--
Actual executable primitive-query counts remain input-polynomial when the
candidate-list lengths are input-polynomial and the varying fuel is uniformly
bounded by one fixed cap.
-/
theorem searchTransportClosureBoundedFuel_primitiveQueries_of_candidateInputPolynomial
    {State : Type}
    {Generator : State → State → Type}
    (primitive : RelationSearch Generator)
    (candidates : Nat → List State)
    (fuel : Nat → Nat)
    (fuelCap : Nat)
    {inputBits : Nat → Nat}
    (candidateBounded :
      InputPolynomiallyBounded
        inputBits
        (fun n =>
          (candidates n).length))
    (fuelBounded :
      ∀ n : Nat,
        fuel n ≤ fuelCap)
    (source target : Nat → State) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (searchTransportClosureBounded
          primitive
          (candidates n)
          (fuel n)
          (source n)
          (target n)).stats.primitiveQueries) := by
  rcases
      closurePrimitiveBoundedFuel_of_candidateInputPolynomial
        fuelCap
        candidateBounded
        fuelBounded with
    ⟨envelope, budgetLe⟩
  refine
    ⟨envelope, ?_⟩
  intro n
  exact
    Nat.le_trans
      (searchTransportClosureBounded_primitiveQueries_le
        primitive
        (candidates n)
        (fuel n)
        (source n)
        (target n))
      (budgetLe n)

/--
Actual executable composition-candidate counts satisfy the same bounded-fuel
input-polynomial regime.
-/
theorem searchTransportClosureBoundedFuel_compositionCandidates_of_candidateInputPolynomial
    {State : Type}
    {Generator : State → State → Type}
    (primitive : RelationSearch Generator)
    (candidates : Nat → List State)
    (fuel : Nat → Nat)
    (fuelCap : Nat)
    {inputBits : Nat → Nat}
    (candidateBounded :
      InputPolynomiallyBounded
        inputBits
        (fun n =>
          (candidates n).length))
    (fuelBounded :
      ∀ n : Nat,
        fuel n ≤ fuelCap)
    (source target : Nat → State) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (searchTransportClosureBounded
          primitive
          (candidates n)
          (fuel n)
          (source n)
          (target n)).stats.compositionCandidates) := by
  rcases
      closureCompositionBoundedFuel_of_candidateInputPolynomial
        fuelCap
        candidateBounded
        fuelBounded with
    ⟨envelope, budgetLe⟩
  refine
    ⟨envelope, ?_⟩
  intro n
  exact
    Nat.le_trans
      (searchTransportClosureBounded_compositionCandidates_le
        primitive
        (candidates n)
        (fuel n)
        (source n)
        (target n))
      (budgetLe n)

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
#print axioms ConstitutiveSearch.closurePrimitiveFixedFuelPolynomial_degree
#print axioms ConstitutiveSearch.closureCompositionFixedFuelPolynomial_degree
#print axioms ConstitutiveSearch.closurePrimitiveFixedFuelPolynomial_degree_unbounded
#print axioms ConstitutiveSearch.closureCompositionFixedFuelPolynomial_degree_unbounded
#print axioms ConstitutiveSearch.closurePrimitiveFixedFuelPolynomial_degree_bounded_iff
#print axioms ConstitutiveSearch.closureCompositionFixedFuelPolynomial_degree_bounded_iff
#print axioms ConstitutiveSearch.closurePrimitiveFixedFuelPolynomial_eval
#print axioms ConstitutiveSearch.closureCompositionFixedFuelPolynomial_eval
#print axioms ConstitutiveSearch.closurePrimitiveFixedFuel_polynomiallyBounded
#print axioms ConstitutiveSearch.closureCompositionFixedFuel_polynomiallyBounded
#print axioms ConstitutiveSearch.closurePrimitiveFixedFuel_le_inputPolynomial
#print axioms ConstitutiveSearch.closureCompositionFixedFuel_le_inputPolynomial
#print axioms ConstitutiveSearch.closurePrimitiveFixedFuel_of_candidateInputPolynomial
#print axioms ConstitutiveSearch.closureCompositionFixedFuel_of_candidateInputPolynomial
#print axioms ConstitutiveSearch.searchTransportClosureFixedFuel_primitiveQueries_of_candidateInputPolynomial
#print axioms ConstitutiveSearch.searchTransportClosureFixedFuel_compositionCandidates_of_candidateInputPolynomial
#print axioms ConstitutiveSearch.viaPrimitiveQueryBudget_mono_recursive
#print axioms ConstitutiveSearch.viaCompositionCandidateBudget_mono_recursive
#print axioms ConstitutiveSearch.closurePrimitiveQueryBudget_mono_fuel
#print axioms ConstitutiveSearch.closureCompositionCandidateBudget_mono_fuel
#print axioms ConstitutiveSearch.closurePrimitiveBoundedFuel_of_candidateInputPolynomial
#print axioms ConstitutiveSearch.closureCompositionBoundedFuel_of_candidateInputPolynomial
#print axioms ConstitutiveSearch.searchTransportClosureBoundedFuel_primitiveQueries_of_candidateInputPolynomial
#print axioms ConstitutiveSearch.searchTransportClosureBoundedFuel_compositionCandidates_of_candidateInputPolynomial
#print axioms ConstitutiveSearch.searchTransportClosureFixedFuel_primitiveQueries_le_inputPolynomial
#print axioms ConstitutiveSearch.searchTransportClosureFixedFuel_compositionCandidates_le_inputPolynomial
/- AXIOM_AUDIT_END -/
