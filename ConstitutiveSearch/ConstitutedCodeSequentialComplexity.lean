import ConstitutiveSearch.SearchableTransportCode
import ConstitutiveSearch.ConstitutiveComplexityInputPolynomial

/-!
# Input-polynomial sequential execution of constituted code families

SearchableTransportCode removes the need to rediscover one already constituted
TransportCode through global ClosureSearch.

This module lifts that local result to input-indexed families.

If:
* each family member carries an already constituted TransportCode;
* every atom of that code is searchable by the announced primitive search;
* the code size is InputPolynomiallyBounded in the concrete input size; and
* the sequential fuel is positive;

then every family member has a sequential primitive-hit execution with:
* exactly code.size primitive queries;
* zero composition-candidate inspections;
* primitive-query count bounded by the same input-polynomial envelope as the
  code size.

No global closure run or global candidate exploration is used to obtain the
sequential execution.
-/

namespace ConstitutiveSearch

universe uGenerator

/--
A family of searchable constituted codes with input-polynomial code size admits
uniformly input-polynomial sequential execution.
-/
theorem searchableCodeFamily_inputPolynomialSequentialExecution
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    (primitive :
      (n : Nat) →
        RelationSearch (Generator n))
    (candidates :
      (n : Nat) →
        List (State n))
    (fuel : Nat → Nat)
    (fuelPositive :
      ∀ n : Nat,
        0 < fuel n)
    (source target :
      (n : Nat) →
        State n)
    (code :
      (n : Nat) →
        TransportClosure
          (Generator n)
          (source n)
          (target n))
    (searchable :
      ∀ n : Nat,
        (code n).SearchableBy
          (primitive n))
    {inputBits : Nat → Nat}
    (codeSizeBounded :
      InputPolynomiallyBounded
        inputBits
        (fun n =>
          (code n).size)) :
    ∃ envelope : CostPolynomial,
      ∀ n : Nat,
        ∃ path :
            PrimitiveHitPath
              (primitive n)
              (source n)
              (target n),
          path.length =
              (code n).size ∧
            (path.sequentialStats
                (candidates n)
                (fuel n)).primitiveQueries =
              (code n).size ∧
            (path.sequentialStats
                (candidates n)
                (fuel n)).primitiveQueries ≤
              envelope.eval
                (inputBits n) ∧
            (path.sequentialStats
                (candidates n)
                (fuel n)).compositionCandidates =
              0 := by
  rcases codeSizeBounded with
    ⟨envelope, codeSizeLe⟩
  refine
    ⟨envelope, ?_⟩
  intro n
  rcases
      (code n).hasSequentialExecution_of_searchable
        (primitive n)
        (candidates n)
        (fuel n)
        (fuelPositive n)
        (searchable n) with
    ⟨path,
      pathLength,
      primitiveExact,
      compositionZero⟩
  refine
    ⟨path,
      pathLength,
      primitiveExact,
      ?_,
      compositionZero⟩
  rw [primitiveExact]
  exact
    codeSizeLe n

/--
The preceding theorem can be packaged directly when the code-size envelope is
given explicitly rather than through InputPolynomiallyBounded.
-/
theorem searchableCodeFamily_of_explicitSizeEnvelope
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    (primitive :
      (n : Nat) →
        RelationSearch (Generator n))
    (candidates :
      (n : Nat) →
        List (State n))
    (fuel : Nat → Nat)
    (fuelPositive :
      ∀ n : Nat,
        0 < fuel n)
    (source target :
      (n : Nat) →
        State n)
    (code :
      (n : Nat) →
        TransportClosure
          (Generator n)
          (source n)
          (target n))
    (searchable :
      ∀ n : Nat,
        (code n).SearchableBy
          (primitive n))
    (inputBits : Nat → Nat)
    (envelope : CostPolynomial)
    (codeSizeLe :
      ∀ n : Nat,
        (code n).size ≤
          envelope.eval
            (inputBits n)) :
    ∀ n : Nat,
      ∃ path :
          PrimitiveHitPath
            (primitive n)
            (source n)
            (target n),
        path.length =
            (code n).size ∧
          (path.sequentialStats
              (candidates n)
              (fuel n)).primitiveQueries =
            (code n).size ∧
          (path.sequentialStats
              (candidates n)
              (fuel n)).primitiveQueries ≤
            envelope.eval
              (inputBits n) ∧
          (path.sequentialStats
              (candidates n)
              (fuel n)).compositionCandidates =
            0 := by
  rcases
      searchableCodeFamily_inputPolynomialSequentialExecution
        primitive
        candidates
        fuel
        fuelPositive
        source
        target
        code
        searchable
        (inputBits := inputBits)
        ⟨envelope, codeSizeLe⟩ with
    ⟨returnedEnvelope, executions⟩
  intro n
  rcases executions n with
    ⟨path,
      pathLength,
      primitiveExact,
      _returnedBound,
      compositionZero⟩
  refine
    ⟨path,
      pathLength,
      primitiveExact,
      ?_,
      compositionZero⟩
  rw [primitiveExact]
  exact
    codeSizeLe n

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.searchableCodeFamily_inputPolynomialSequentialExecution
#print axioms ConstitutiveSearch.searchableCodeFamily_of_explicitSizeEnvelope
/- AXIOM_AUDIT_END -/
