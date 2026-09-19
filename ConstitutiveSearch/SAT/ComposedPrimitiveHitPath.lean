import ConstitutiveSearch.SequentialPrimitiveExecution
import ConstitutiveSearch.SAT.SequentialComposedExecutionSeparator

/-!
# Primitive-hit path behind the composed SAT separator

The composed SAT benchmark has no direct primitive source-to-target relation,
but it has the certified primitive path

  source -> middle -> target.

This module instantiates the generic PrimitiveHitPath interface and shows that
the benchmark is a GlobalCompositionRequired query in the precise sense:
* direct primitive search misses;
* a primitive-hit path of length exactly two connects the endpoints.

The same path executes sequentially with exactly two primitive queries and zero
composition candidates, while the flattened global query executes three
primitive queries and one composition candidate.
-/

namespace ConstitutiveSearch
namespace SAT

/--
The composed SAT source-to-target request is globally composition-required.
-/
theorem composedGlobalCompositionRequired
    (count : Nat) :
    PrimitiveHitPath.GlobalCompositionRequired
      (composedPrimitiveSearch count)
      (composedSource count)
      (composedTarget count) := by
  constructor
  · exact
      composedPrimitiveSearch_source_target_none
        count
  · rcases
        composedPrimitiveSearch_source_middle_some
          count with
      ⟨firstWitness, firstExact⟩
    rcases
        composedPrimitiveSearch_middle_target_some
          count with
      ⟨secondWitness, secondExact⟩
    let path :
        PrimitiveHitPath
          (composedPrimitiveSearch count)
          (composedSource count)
          (composedTarget count) :=
      .step
        firstExact
        (.step
          secondExact
          (.identity
            (composedTarget count)))
    exact
      ⟨path, by
        change 2 ≤ 2
        exact Nat.le_refl 2⟩

/-- The witnessing primitive-hit path can be chosen with exact length two. -/
theorem composedPrimitiveHitPath_length_two
    (count : Nat) :
    ∃ path :
        PrimitiveHitPath
          (composedPrimitiveSearch count)
          (composedSource count)
          (composedTarget count),
      path.length = 2 := by
  rcases
      composedPrimitiveSearch_source_middle_some
        count with
    ⟨firstWitness, firstExact⟩
  rcases
      composedPrimitiveSearch_middle_target_some
        count with
    ⟨secondWitness, secondExact⟩
  let path :
      PrimitiveHitPath
        (composedPrimitiveSearch count)
        (composedSource count)
        (composedTarget count) :=
    .step
      firstExact
      (.step
        secondExact
        (.identity
          (composedTarget count)))
  exact
    ⟨path, rfl⟩

/--
Sequentially executing the constituted two-edge path uses exactly the two
primitive hits and no composition-candidate search.
-/
theorem composedPrimitiveHitPath_sequentialStats
    (count : Nat) :
    ∃ path :
        PrimitiveHitPath
          (composedPrimitiveSearch count)
          (composedSource count)
          (composedTarget count),
      path.length = 2 ∧
        (path.sequentialStats
            [composedMiddle count]
            2).primitiveQueries = 2 ∧
        (path.sequentialStats
            [composedMiddle count]
            2).compositionCandidates = 0 := by
  rcases
      composedPrimitiveSearch_source_middle_some
        count with
    ⟨firstWitness, firstExact⟩
  rcases
      composedPrimitiveSearch_middle_target_some
        count with
    ⟨secondWitness, secondExact⟩
  let path :
      PrimitiveHitPath
        (composedPrimitiveSearch count)
        (composedSource count)
        (composedTarget count) :=
    .step
      firstExact
      (.step
        secondExact
        (.identity
          (composedTarget count)))
  have primitiveExact :=
    path.sequentialStats_primitiveQueries
      [composedMiddle count]
      2
      (by decide)
  have compositionExact :=
    path.sequentialStats_compositionCandidates
      [composedMiddle count]
      2
      (by decide)
  refine
    ⟨path, rfl, ?_, compositionExact⟩
  simpa only [show path.length = 2 by rfl] using
    primitiveExact

/--
The same endpoint relation therefore exhibits a strict execution gap between
global closure and sequential path execution.
-/
theorem composedGlobalCompositionRequired_executionGap
    (count : Nat) :
    ∃ path :
        PrimitiveHitPath
          (composedPrimitiveSearch count)
          (composedSource count)
          (composedTarget count),
      path.length = 2 ∧
        (path.sequentialStats
            [composedMiddle count]
            2).primitiveQueries <
          (composedClosureFuelTwo count).stats.primitiveQueries ∧
        (path.sequentialStats
            [composedMiddle count]
            2).compositionCandidates <
          (composedClosureFuelTwo count).stats.compositionCandidates := by
  rcases
      composedPrimitiveHitPath_sequentialStats
        count with
    ⟨path, lengthExact, primitiveExact, compositionExact⟩
  refine
    ⟨path, lengthExact, ?_, ?_⟩
  · rw [
      primitiveExact,
      composedClosureFuelTwo_primitiveQueries
    ]
    decide
  · rw [
      compositionExact,
      composedClosureFuelTwo_compositionCandidates
    ]
    decide

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.composedGlobalCompositionRequired
#print axioms ConstitutiveSearch.SAT.composedPrimitiveHitPath_length_two
#print axioms ConstitutiveSearch.SAT.composedPrimitiveHitPath_sequentialStats
#print axioms ConstitutiveSearch.SAT.composedGlobalCompositionRequired_executionGap
/- AXIOM_AUDIT_END -/
