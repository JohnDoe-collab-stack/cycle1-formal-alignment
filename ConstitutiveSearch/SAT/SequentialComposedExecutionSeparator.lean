import ConstitutiveSearch.SAT.SequentialGlobalClosureSeparator
import ConstitutiveSearch.SAT.ParametricComposedClosure

/-!
# Sequential versus global execution on the composed SAT benchmark

ParametricComposedClosure already gives a concrete query that genuinely
requires composition:

  source -> target

is not a primitive relation, while

  source -> middle
  middle -> target

are primitive hits.

The single global closure query with candidate [middle] and fuel 2 executes:
* 3 primitive queries;
* 1 composition candidate.

This module executes the same two certified edges sequentially through the same
ClosureSearch engine, with the same candidate list and fuel.  Because each edge
is a primitive hit, the two runs together execute:
* 2 primitive queries;
* 0 composition candidates.

Thus the extra control-flow work is formally attributable to requesting the
composed relation globally rather than following the two constituted primitive
steps sequentially.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Closure run for the first primitive edge of the composed benchmark. -/
def composedSequentialSourceMiddleRun
    (count : Nat) :=
  searchTransportClosureBounded
    (composedPrimitiveSearch count)
    [composedMiddle count]
    2
    (composedSource count)
    (composedMiddle count)

/-- Closure run for the second primitive edge. -/
def composedSequentialMiddleTargetRun
    (count : Nat) :=
  searchTransportClosureBounded
    (composedPrimitiveSearch count)
    [composedMiddle count]
    2
    (composedMiddle count)
    (composedTarget count)

/-- Aggregate stats of executing the two primitive edges sequentially. -/
def composedSequentialClosureStats
    (count : Nat) :
    ClosureSearchStats :=
  ClosureSearchStats.combine
    (composedSequentialSourceMiddleRun count).stats
    (composedSequentialMiddleTargetRun count).stats

/-- The source-to-middle run short-circuits at the primitive layer. -/
theorem composedSequentialSourceMiddle_stats
    (count : Nat) :
    (composedSequentialSourceMiddleRun count).stats.primitiveQueries = 1 ∧
      (composedSequentialSourceMiddleRun count).stats.compositionCandidates = 0 := by
  rcases
      composedPrimitiveSearch_source_middle_some count with
    ⟨witness, exactFind⟩
  apply
    searchTransportClosureBounded_primitiveHit_stats
      (composedPrimitiveSearch count)
      [composedMiddle count]
      2
      (composedSource count)
      (composedMiddle count)
      (by decide)
  rw [exactFind]
  intro impossible
  cases impossible

/-- The middle-to-target run also short-circuits at the primitive layer. -/
theorem composedSequentialMiddleTarget_stats
    (count : Nat) :
    (composedSequentialMiddleTargetRun count).stats.primitiveQueries = 1 ∧
      (composedSequentialMiddleTargetRun count).stats.compositionCandidates = 0 := by
  rcases
      composedPrimitiveSearch_middle_target_some count with
    ⟨witness, exactFind⟩
  apply
    searchTransportClosureBounded_primitiveHit_stats
      (composedPrimitiveSearch count)
      [composedMiddle count]
      2
      (composedMiddle count)
      (composedTarget count)
      (by decide)
  rw [exactFind]
  intro impossible
  cases impossible

/-- Sequential execution uses exactly two primitive queries. -/
theorem composedSequentialClosureStats_primitiveQueries
    (count : Nat) :
    (composedSequentialClosureStats count).primitiveQueries =
      2 := by
  have first :=
    composedSequentialSourceMiddle_stats count
  have second :=
    composedSequentialMiddleTarget_stats count
  unfold composedSequentialClosureStats
  change
    (composedSequentialSourceMiddleRun count).stats.primitiveQueries +
        (composedSequentialMiddleTargetRun count).stats.primitiveQueries =
      2
  rw [
    first.1,
    second.1
  ]

/-- Sequential execution inspects no composition candidate. -/
theorem composedSequentialClosureStats_compositionCandidates
    (count : Nat) :
    (composedSequentialClosureStats count).compositionCandidates =
      0 := by
  have first :=
    composedSequentialSourceMiddle_stats count
  have second :=
    composedSequentialMiddleTarget_stats count
  unfold composedSequentialClosureStats
  change
    (composedSequentialSourceMiddleRun count).stats.compositionCandidates +
        (composedSequentialMiddleTargetRun count).stats.compositionCandidates =
      0
  rw [
    first.2,
    second.2
  ]

/-- The global composed query executes one more primitive query than the sequence. -/
theorem composedSequential_primitiveQueries_lt_global
    (count : Nat) :
    (composedSequentialClosureStats count).primitiveQueries <
      (composedClosureFuelTwo count).stats.primitiveQueries := by
  rw [
    composedSequentialClosureStats_primitiveQueries,
    composedClosureFuelTwo_primitiveQueries
  ]
  decide

/-- The global composed query inspects a composition candidate; the sequence does not. -/
theorem composedSequential_compositionCandidates_lt_global
    (count : Nat) :
    (composedSequentialClosureStats count).compositionCandidates <
      (composedClosureFuelTwo count).stats.compositionCandidates := by
  rw [
    composedSequentialClosureStats_compositionCandidates,
    composedClosureFuelTwo_compositionCandidates
  ]
  decide

/--
Exact executable-counter separator between following the two constituted
primitive steps and asking one globally composed query.
-/
structure SequentialComposedExecutionSeparator
    (count : Nat) : Prop where
  sequentialPrimitive :
    (composedSequentialClosureStats count).primitiveQueries = 2
  sequentialComposition :
    (composedSequentialClosureStats count).compositionCandidates = 0
  globalPrimitive :
    (composedClosureFuelTwo count).stats.primitiveQueries = 3
  globalComposition :
    (composedClosureFuelTwo count).stats.compositionCandidates = 1
  primitiveStrict :
    (composedSequentialClosureStats count).primitiveQueries <
      (composedClosureFuelTwo count).stats.primitiveQueries
  compositionStrict :
    (composedSequentialClosureStats count).compositionCandidates <
      (composedClosureFuelTwo count).stats.compositionCandidates

theorem composedSequentialGlobalExecutionSeparator
    (count : Nat) :
    SequentialComposedExecutionSeparator count :=
  { sequentialPrimitive :=
      composedSequentialClosureStats_primitiveQueries count
    sequentialComposition :=
      composedSequentialClosureStats_compositionCandidates count
    globalPrimitive :=
      composedClosureFuelTwo_primitiveQueries count
    globalComposition :=
      composedClosureFuelTwo_compositionCandidates count
    primitiveStrict :=
      composedSequential_primitiveQueries_lt_global count
    compositionStrict :=
      composedSequential_compositionCandidates_lt_global count }

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.composedSequentialSourceMiddleRun
#print axioms ConstitutiveSearch.SAT.composedSequentialMiddleTargetRun
#print axioms ConstitutiveSearch.SAT.composedSequentialClosureStats
#print axioms ConstitutiveSearch.SAT.composedSequentialSourceMiddle_stats
#print axioms ConstitutiveSearch.SAT.composedSequentialMiddleTarget_stats
#print axioms ConstitutiveSearch.SAT.composedSequentialClosureStats_primitiveQueries
#print axioms ConstitutiveSearch.SAT.composedSequentialClosureStats_compositionCandidates
#print axioms ConstitutiveSearch.SAT.composedSequential_primitiveQueries_lt_global
#print axioms ConstitutiveSearch.SAT.composedSequential_compositionCandidates_lt_global
#print axioms ConstitutiveSearch.SAT.SequentialComposedExecutionSeparator
#print axioms ConstitutiveSearch.SAT.composedSequentialGlobalExecutionSeparator
/- AXIOM_AUDIT_END -/
