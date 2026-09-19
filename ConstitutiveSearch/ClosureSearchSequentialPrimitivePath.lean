import ConstitutiveSearch.ClosureSearchPrimitiveHit

/-!
# Sequential execution along primitive-hit paths

The primitive-hit short-circuit theorem is not SAT-specific.  This module
packages the underlying execution pattern directly at the ClosureSearch level.

A PrimitiveHitPath is a finite constituted chain whose every adjacent edge is
already found by one announced primitive RelationSearch.

If each edge is queried sequentially through searchTransportClosureBounded with
any common candidate list and any positive fuel, then:
* exactly one primitive query is charged per edge;
* no composition candidate is inspected.

Therefore a primitive-hit path of length k executes with exactly k primitive
queries and zero composition candidates, independently of the size of the
global candidate list and independently of the positive fuel value.

This theorem concerns actual ClosureSearch counters, not recursive upper
budgets.
-/

namespace ConstitutiveSearch

universe uGenerator

/-- Finite path whose every adjacent edge is an executable primitive hit. -/
inductive PrimitiveHitPath
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator) :
    State → State → Nat → Type where
  | done
      (state : State) :
      PrimitiveHitPath primitive state state 0
  | step
      {target : State}
      {length : Nat}
      (source middle : State)
      (hit :
        primitive.find source middle ≠ none)
      (tail :
        PrimitiveHitPath
          primitive
          middle
          target
          length) :
      PrimitiveHitPath
        primitive
        source
        target
        (length + 1)

namespace PrimitiveHitPath

/--
Aggregate actual ClosureSearch stats obtained by querying every primitive edge
sequentially with one common control domain.
-/
def sequentialStats
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    {source target : State}
    {length : Nat}
    (path :
      PrimitiveHitPath
        primitive
        source
        target
        length)
    (candidates : List State)
    (fuel : Nat) :
    ClosureSearchStats :=
  match path with
  | .done _ =>
      ClosureSearchStats.zero
  | .step edgeSource edgeTarget _hit tail =>
      ClosureSearchStats.combine
        (searchTransportClosureBounded
          primitive
          candidates
          fuel
          edgeSource
          edgeTarget).stats
        (tail.sequentialStats
          candidates
          fuel)

/-- Exactly one primitive query is executed for each edge of the path. -/
theorem sequentialStats_primitiveQueries
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    {source target : State}
    {length : Nat}
    (path :
      PrimitiveHitPath
        primitive
        source
        target
        length)
    (candidates : List State)
    (fuel : Nat)
    (fuelPositive :
      0 < fuel) :
    (path.sequentialStats
      candidates
      fuel).primitiveQueries =
      length := by
  induction path with
  | done state =>
      rfl
  | step edgeSource edgeTarget hit tail inductionHypothesis =>
      have edgeStats :=
        searchTransportClosureBounded_primitiveHit_stats
          primitive
          candidates
          fuel
          edgeSource
          edgeTarget
          fuelPositive
          hit
      change
        (searchTransportClosureBounded
            primitive
            candidates
            fuel
            edgeSource
            edgeTarget).stats.primitiveQueries +
            (tail.sequentialStats
              candidates
              fuel).primitiveQueries =
          _ + 1
      rw [
        edgeStats.1,
        inductionHypothesis
      ]
      exact Nat.add_comm 1 _

/-- No composition candidate is inspected along a sequential primitive-hit path. -/
theorem sequentialStats_compositionCandidates
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    {source target : State}
    {length : Nat}
    (path :
      PrimitiveHitPath
        primitive
        source
        target
        length)
    (candidates : List State)
    (fuel : Nat)
    (fuelPositive :
      0 < fuel) :
    (path.sequentialStats
      candidates
      fuel).compositionCandidates =
      0 := by
  induction path with
  | done state =>
      rfl
  | step edgeSource edgeTarget hit tail inductionHypothesis =>
      have edgeStats :=
        searchTransportClosureBounded_primitiveHit_stats
          primitive
          candidates
          fuel
          edgeSource
          edgeTarget
          fuelPositive
          hit
      change
        (searchTransportClosureBounded
            primitive
            candidates
            fuel
            edgeSource
            edgeTarget).stats.compositionCandidates +
            (tail.sequentialStats
              candidates
              fuel).compositionCandidates =
          0
      rw [
        edgeStats.2,
        inductionHypothesis
      ]

end PrimitiveHitPath

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.PrimitiveHitPath
#print axioms ConstitutiveSearch.PrimitiveHitPath.sequentialStats
#print axioms ConstitutiveSearch.PrimitiveHitPath.sequentialStats_primitiveQueries
#print axioms ConstitutiveSearch.PrimitiveHitPath.sequentialStats_compositionCandidates
/- AXIOM_AUDIT_END -/
