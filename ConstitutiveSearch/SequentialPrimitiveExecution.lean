import Init.Omega
import ConstitutiveSearch.ClosureSearch

/-!
# Sequential execution of certified primitive-hit paths

Global closure can ask for a relation between distant endpoints even when the
constitutive path between them is already known edge by edge.

This module factors the generic object behind the SAT separators:
a finite path whose every edge is an executable primitive-search hit.

Such a path has three distinct readings:
* proof-relevant sequential structure;
* a finite TransportCode obtained by composing its primitive witnesses;
* an actual sequential ClosureSearch execution.

The sequential execution theorem is exact.  For every positive fuel and every
candidate list, a path of length k executes as:
* exactly k primitive queries;
* zero composition candidates.

Thus a direct primitive miss between the endpoints can coexist with a fully
primitive sequential realization.  In that situation composition is required
only by the global endpoint query, not by execution of the constituted path.
-/

namespace ConstitutiveSearch

universe uGenerator

/--
A finite path of primitive-search hits.

Each edge stores the exact witness returned by the announced RelationSearch.
-/
inductive PrimitiveHitPath
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator) :
    State → State → Type uGenerator where
  | identity
      (state : State) :
      PrimitiveHitPath primitive state state
  | step
      {source middle target : State}
      {witness : Generator source middle}
      (hit :
        primitive.find source middle =
          some witness)
      (tail :
        PrimitiveHitPath
          primitive
          middle
          target) :
      PrimitiveHitPath
        primitive
        source
        target

namespace PrimitiveHitPath

/-- Number of primitive edges in the path. -/
def length
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    {source target : State} :
    PrimitiveHitPath primitive source target → Nat
  | .identity _ =>
      0
  | .step _ tail =>
      tail.length + 1

/-- Compile a primitive-hit path into the free transport closure. -/
def toTransportCode
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    {source target : State} :
    PrimitiveHitPath primitive source target →
      TransportClosure Generator source target
  | .identity state =>
      .identity state
  | .step (witness := witness) _ tail =>
      .compose
        (.atom witness)
        tail.toTransportCode

/-- Compilation preserves exactly the number of primitive generator atoms. -/
theorem toTransportCode_size
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    {source target : State}
    (path :
      PrimitiveHitPath
        primitive
        source
        target) :
    path.toTransportCode.size =
      path.length := by
  induction path with
  | identity state =>
      rfl
  | step hit tail inductionHypothesis =>
      simp only [
        toTransportCode,
        TransportCode.size,
        length
      ]
      rw [inductionHypothesis]
      omega

/--
Aggregate actual ClosureSearch statistics obtained by following path edges
sequentially.

The same candidate list and fuel are supplied to every edge run; primitive hits
make those global parameters irrelevant to the successful edge itself.
-/
def sequentialStats
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    (candidates : List State)
    (fuel : Nat) :
    {source target : State} →
      PrimitiveHitPath
        primitive
        source
        target →
      ClosureSearchStats
  | _, _, .identity _ =>
      ClosureSearchStats.zero
  | source, _, .step (middle := middle) _ tail =>
      ClosureSearchStats.combine
        (searchTransportClosureBounded
          primitive
          candidates
          fuel
          source
          middle).stats
        (sequentialStats
          candidates
          fuel
          tail)

/--
A positive-fuel ClosureSearch query that is already a primitive hit performs
exactly one primitive query and no composition-candidate inspection.
-/
theorem primitiveHit_run_stats
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (fuel : Nat)
    (source target : State)
    (fuelPositive : 0 < fuel)
    (primitiveHit :
      primitive.find source target ≠ none) :
    let run :=
      searchTransportClosureBounded
        primitive
        candidates
        fuel
        source
        target
    run.stats.primitiveQueries = 1 ∧
      run.stats.compositionCandidates = 0 := by
  cases fuel with
  | zero =>
      omega
  | succ fuel =>
      cases found :
          primitive.find source target with
      | none =>
          exact False.elim (primitiveHit found)
      | some witness =>
          simp only [
            searchTransportClosureBounded,
            found,
            ClosureSearchStats.withPrimitiveQuery,
            ClosureSearchStats.zero
          ]
          exact ⟨True.intro, True.intro⟩

/-- Every stored edge is a non-none primitive hit. -/
theorem step_hit_ne_none
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    {source middle target : State}
    {witness : Generator source middle}
    (hit :
      primitive.find source middle =
        some witness)
    (tail :
      PrimitiveHitPath
        primitive
        middle
        target) :
    primitive.find source middle ≠ none := by
  rw [hit]
  intro impossible
  cases impossible

/--
Sequential execution performs exactly one primitive query per certified edge.
-/
theorem sequentialStats_primitiveQueries
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    (candidates : List State)
    (fuel : Nat)
    (fuelPositive : 0 < fuel)
    {source target : State}
    (path :
      PrimitiveHitPath
        primitive
        source
        target) :
    (path.sequentialStats
      candidates
      fuel).primitiveQueries =
        path.length := by
  induction path with
  | identity state =>
      rfl
  | @step source middle target witness hit tail inductionHypothesis =>
      have edgeStats :=
        primitiveHit_run_stats
          primitive
          candidates
          fuel
          source
          middle
          fuelPositive
          (step_hit_ne_none
            hit
            tail)
      simp only [
        sequentialStats,
        ClosureSearchStats.combine,
        length
      ]
      rw [
        edgeStats.1,
        inductionHypothesis
      ]
      omega

/--
Sequential execution never inspects a composition candidate: every edge
short-circuits at the primitive layer.
-/
theorem sequentialStats_compositionCandidates
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    (candidates : List State)
    (fuel : Nat)
    (fuelPositive : 0 < fuel)
    {source target : State}
    (path :
      PrimitiveHitPath
        primitive
        source
        target) :
    (path.sequentialStats
      candidates
      fuel).compositionCandidates =
        0 := by
  induction path with
  | identity state =>
      rfl
  | @step source middle target witness hit tail inductionHypothesis =>
      have edgeStats :=
        primitiveHit_run_stats
          primitive
          candidates
          fuel
          source
          middle
          fuelPositive
          (step_hit_ne_none
            hit
            tail)
      simp only [
        sequentialStats,
        ClosureSearchStats.combine
      ]
      rw [
        edgeStats.2,
        inductionHypothesis
      ]

/--
A global endpoint query is composition-required relative to a primitive search
when the direct primitive query misses while a certified primitive-hit path of
length at least two connects the same endpoints.
-/
def GlobalCompositionRequired
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (source target : State) : Prop :=
  primitive.find source target = none ∧
    ∃ path :
        PrimitiveHitPath
          primitive
          source
          target,
      2 ≤ path.length

/--
A global composition requirement carries an explicit closure code with at least
two primitive atoms.
-/
theorem globalCompositionRequired_hasCode
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    {source target : State}
    (required :
      GlobalCompositionRequired
        primitive
        source
        target) :
    ∃ code :
        TransportClosure
          Generator
          source
          target,
      2 ≤ code.size := by
  rcases required with
    ⟨_directMiss, path, pathLength⟩
  exact
    ⟨path.toTransportCode,
      by
        rw [path.toTransportCode_size]
        exact pathLength⟩

/--
A global composition requirement can still be executed sequentially without any
composition-candidate search once its constituted primitive path is retained.
-/
theorem globalCompositionRequired_hasSequentialExecution
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    (candidates : List State)
    (fuel : Nat)
    (fuelPositive : 0 < fuel)
    {source target : State}
    (required :
      GlobalCompositionRequired
        primitive
        source
        target) :
    ∃ path :
        PrimitiveHitPath
          primitive
          source
          target,
      2 ≤ path.length ∧
        (path.sequentialStats
            candidates
            fuel).primitiveQueries =
          path.length ∧
        (path.sequentialStats
            candidates
            fuel).compositionCandidates =
          0 := by
  rcases required with
    ⟨_directMiss, path, pathLength⟩
  exact
    ⟨path,
      pathLength,
      path.sequentialStats_primitiveQueries
        candidates
        fuel
        fuelPositive,
      path.sequentialStats_compositionCandidates
        candidates
        fuel
        fuelPositive⟩

end PrimitiveHitPath

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.PrimitiveHitPath
#print axioms ConstitutiveSearch.PrimitiveHitPath.length
#print axioms ConstitutiveSearch.PrimitiveHitPath.toTransportCode
#print axioms ConstitutiveSearch.PrimitiveHitPath.toTransportCode_size
#print axioms ConstitutiveSearch.PrimitiveHitPath.sequentialStats
#print axioms ConstitutiveSearch.PrimitiveHitPath.primitiveHit_run_stats
#print axioms ConstitutiveSearch.PrimitiveHitPath.step_hit_ne_none
#print axioms ConstitutiveSearch.PrimitiveHitPath.sequentialStats_primitiveQueries
#print axioms ConstitutiveSearch.PrimitiveHitPath.sequentialStats_compositionCandidates
#print axioms ConstitutiveSearch.PrimitiveHitPath.GlobalCompositionRequired
#print axioms ConstitutiveSearch.PrimitiveHitPath.globalCompositionRequired_hasCode
#print axioms ConstitutiveSearch.PrimitiveHitPath.globalCompositionRequired_hasSequentialExecution
/- AXIOM_AUDIT_END -/
