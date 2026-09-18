import ConstitutiveSearch.ClosureSearch
import Std.Tactic.Omega

/-!
# Bounds for bounded transport-closure search

This module proves an explicit recursive upper budget for the executable bounded
closure search.

The budget depends only on:
* the finite intermediate-candidate list;
* the fuel.

It bounds the source-level control-flow work recorded by the search. It does
not claim completeness beyond those announced bounds and it is not a wall-clock
runtime theorem.
-/

namespace ConstitutiveSearch

universe uGenerator

namespace ClosureSearchStats

/-- Combined source-level work events recorded by one bounded-closure run. -/
def workUnits
    (stats : ClosureSearchStats) : Nat :=
  stats.primitiveQueries +
    stats.compositionCandidates

theorem workUnits_zero :
    zero.workUnits = 0 := by
  rfl

theorem workUnits_combine
    (left right : ClosureSearchStats) :
    (combine left right).workUnits =
      left.workUnits + right.workUnits := by
  unfold workUnits combine
  omega

theorem workUnits_withPrimitiveQuery
    (stats : ClosureSearchStats) :
    (withPrimitiveQuery stats).workUnits =
      stats.workUnits + 1 := by
  unfold workUnits withPrimitiveQuery
  omega

theorem workUnits_withCompositionCandidate
    (stats : ClosureSearchStats) :
    (withCompositionCandidate stats).workUnits =
      stats.workUnits + 1 := by
  unfold workUnits withCompositionCandidate
  omega

theorem primitiveQueries_le_workUnits
    (stats : ClosureSearchStats) :
    stats.primitiveQueries ≤ stats.workUnits := by
  unfold workUnits
  exact
    Nat.le_add_right
      stats.primitiveQueries
      stats.compositionCandidates

theorem compositionCandidates_le_workUnits
    (stats : ClosureSearchStats) :
    stats.compositionCandidates ≤ stats.workUnits := by
  unfold workUnits
  exact
    Nat.le_add_left
      stats.compositionCandidates
      stats.primitiveQueries

end ClosureSearchStats

/--
Worst-case work contributed by traversing an explicit candidate list, assuming
every recursive subquery costs at most recursiveBound.

For each candidate we reserve:
* up to two recursive subqueries;
* one composition-candidate event.
-/
def closureCandidateWorkBound
    {State : Type}
    (candidates : List State)
    (recursiveBound : Nat) : Nat :=
  match candidates with
  | [] =>
      0
  | _ :: rest =>
      recursiveBound +
        recursiveBound +
        1 +
        closureCandidateWorkBound
          rest
          recursiveBound

/--
Recursive worst-case work budget for bounded closure search.
-/
def closureSearchWorkBound
    {State : Type}
    (candidates : List State) :
    Nat → Nat
  | 0 =>
      0
  | fuel + 1 =>
      1 +
        closureCandidateWorkBound
          candidates
          (closureSearchWorkBound
            candidates
            fuel)

/--
Candidate traversal is bounded solely by the candidate list and a uniform bound
on recursive subqueries.
-/
theorem searchClosureViaCandidates_workUnits_le
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (recurse :
      (source target : State) →
        ClosureSearchRun Generator source target)
    (recursiveBound : Nat)
    (recurseBound :
      ∀ source target : State,
        (recurse source target).stats.workUnits ≤
          recursiveBound) :
    ∀ (candidates : List State)
      (source target : State),
      (searchClosureViaCandidates
        recurse
        candidates
        source
        target).stats.workUnits ≤
          closureCandidateWorkBound
            candidates
            recursiveBound := by
  intro candidates
  induction candidates with
  | nil =>
      intro source target
      exact Nat.le_refl 0
  | cons middle rest inductionHypothesis =>
      intro source target
      have firstBound :
          (recurse source middle).stats.workUnits ≤
            recursiveBound :=
        recurseBound source middle
      cases firstCode :
          (recurse source middle).code? with
      | none =>
          have laterBound :
              (searchClosureViaCandidates
                recurse
                rest
                source
                target).stats.workUnits ≤
                  closureCandidateWorkBound
                    rest
                    recursiveBound :=
            inductionHypothesis source target
          simp only [
            searchClosureViaCandidates,
            firstCode,
            ClosureSearchStats.workUnits_withCompositionCandidate,
            ClosureSearchStats.workUnits_combine,
            closureCandidateWorkBound
          ]
          omega
      | some firstCodeValue =>
          have secondBound :
              (recurse middle target).stats.workUnits ≤
                recursiveBound :=
            recurseBound middle target
          cases secondCode :
              (recurse middle target).code? with
          | some secondCodeValue =>
              simp only [
                searchClosureViaCandidates,
                firstCode,
                secondCode,
                ClosureSearchStats.workUnits_withCompositionCandidate,
                ClosureSearchStats.workUnits_combine,
                closureCandidateWorkBound
              ]
              have nonnegative :
                  0 ≤
                    closureCandidateWorkBound
                      rest
                      recursiveBound :=
                Nat.zero_le _
              omega
          | none =>
              have laterBound :
                  (searchClosureViaCandidates
                    recurse
                    rest
                    source
                    target).stats.workUnits ≤
                      closureCandidateWorkBound
                        rest
                        recursiveBound :=
                inductionHypothesis source target
              simp only [
                searchClosureViaCandidates,
                firstCode,
                secondCode,
                ClosureSearchStats.workUnits_withCompositionCandidate,
                ClosureSearchStats.workUnits_combine,
                closureCandidateWorkBound
              ]
              omega

/--
The complete bounded closure search stays within the recursive work budget.
-/
theorem searchTransportClosureBounded_workUnits_le
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State) :
    ∀ (fuel : Nat)
      (source target : State),
      (searchTransportClosureBounded
        primitive
        candidates
        fuel
        source
        target).stats.workUnits ≤
          closureSearchWorkBound
            candidates
            fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro source target
      exact Nat.le_refl 0
  | succ fuel inductionHypothesis =>
      intro source target
      cases primitiveResult :
          primitive.find source target with
      | some witness =>
          simp only [
            searchTransportClosureBounded,
            primitiveResult,
            ClosureSearchStats.workUnits_withPrimitiveQuery,
            ClosureSearchStats.workUnits_zero,
            closureSearchWorkBound
          ]
          have nonnegative :
              0 ≤
                closureCandidateWorkBound
                  candidates
                  (closureSearchWorkBound
                    candidates
                    fuel) :=
            Nat.zero_le _
          omega
      | none =>
          have recurseBound :
              ∀ left right : State,
                (searchTransportClosureBounded
                  primitive
                  candidates
                  fuel
                  left
                  right).stats.workUnits ≤
                    closureSearchWorkBound
                      candidates
                      fuel :=
            inductionHypothesis
          have viaBound :
              (searchClosureViaCandidates
                (fun left right =>
                  searchTransportClosureBounded
                    primitive
                    candidates
                    fuel
                    left
                    right)
                candidates
                source
                target).stats.workUnits ≤
                  closureCandidateWorkBound
                    candidates
                    (closureSearchWorkBound
                      candidates
                      fuel) :=
            searchClosureViaCandidates_workUnits_le
              (fun left right =>
                searchTransportClosureBounded
                  primitive
                  candidates
                  fuel
                  left
                  right)
              (closureSearchWorkBound
                candidates
                fuel)
              recurseBound
              candidates
              source
              target
          simp only [
            searchTransportClosureBounded,
            primitiveResult,
            ClosureSearchStats.workUnits_withPrimitiveQuery,
            closureSearchWorkBound
          ]
          omega

/-- Primitive relation queries are individually bounded by the total work budget. -/
theorem searchTransportClosureBounded_primitiveQueries_le
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (fuel : Nat)
    (source target : State) :
    (searchTransportClosureBounded
      primitive
      candidates
      fuel
      source
      target).stats.primitiveQueries ≤
        closureSearchWorkBound
          candidates
          fuel := by
  exact
    Nat.le_trans
      (ClosureSearchStats.primitiveQueries_le_workUnits
        (searchTransportClosureBounded
          primitive
          candidates
          fuel
          source
          target).stats)
      (searchTransportClosureBounded_workUnits_le
        primitive
        candidates
        fuel
        source
        target)

/-- Composition-candidate events are individually bounded by the same budget. -/
theorem searchTransportClosureBounded_compositionCandidates_le
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State)
    (fuel : Nat)
    (source target : State) :
    (searchTransportClosureBounded
      primitive
      candidates
      fuel
      source
      target).stats.compositionCandidates ≤
        closureSearchWorkBound
          candidates
          fuel := by
  exact
    Nat.le_trans
      (ClosureSearchStats.compositionCandidates_le_workUnits
        (searchTransportClosureBounded
          primitive
          candidates
          fuel
          source
          target).stats)
      (searchTransportClosureBounded_workUnits_le
        primitive
        candidates
        fuel
        source
        target)

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ClosureSearchStats.workUnits
#print axioms ConstitutiveSearch.ClosureSearchStats.workUnits_combine
#print axioms ConstitutiveSearch.ClosureSearchStats.workUnits_withPrimitiveQuery
#print axioms ConstitutiveSearch.ClosureSearchStats.workUnits_withCompositionCandidate
#print axioms ConstitutiveSearch.closureCandidateWorkBound
#print axioms ConstitutiveSearch.closureSearchWorkBound
#print axioms ConstitutiveSearch.searchClosureViaCandidates_workUnits_le
#print axioms ConstitutiveSearch.searchTransportClosureBounded_workUnits_le
#print axioms ConstitutiveSearch.searchTransportClosureBounded_primitiveQueries_le
#print axioms ConstitutiveSearch.searchTransportClosureBounded_compositionCandidates_le
/- AXIOM_AUDIT_END -/
