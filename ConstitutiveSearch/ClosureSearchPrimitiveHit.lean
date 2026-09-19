import Init.Omega
import ConstitutiveSearch.ClosureSearch

/-!
# Primitive-hit short circuit for bounded closure search

This generic layer isolates one executable fact about ClosureSearch.

If a positive-fuel query is already solved by the announced primitive relation
search, the bounded closure engine returns immediately.  The actual control-flow
counters are therefore exactly:
* one primitive query;
* zero composition candidates.

The result is independent of the candidate-list size and of the positive fuel
magnitude.  It is an actual counter theorem, not a recursive budget statement.
-/

namespace ConstitutiveSearch

universe uGenerator

/--
A positive-fuel primitive hit short-circuits bounded closure search with exact
stats 1/0.
-/
theorem searchTransportClosureBounded_primitiveHit_stats
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
      cases h :
          primitive.find source target with
      | none =>
          exact False.elim (primitiveHit h)
      | some witness =>
          simp only [
            searchTransportClosureBounded,
            h,
            ClosureSearchStats.withPrimitiveQuery,
            ClosureSearchStats.zero
          ]
          exact ⟨True.intro, True.intro⟩

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.searchTransportClosureBounded_primitiveHit_stats
/- AXIOM_AUDIT_END -/
