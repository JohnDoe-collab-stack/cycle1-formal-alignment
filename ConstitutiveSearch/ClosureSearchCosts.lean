import ConstitutiveSearch.ClosureSearch

/-!
# Structural cost bounds for bounded transport-closure search

The bounded closure search is executable but may branch through every explicit
intermediate candidate at every fuel level.  This module gives recursive upper
bounds for the two counters collected by the search itself.

The bounds deliberately mirror the search tree instead of prematurely claiming
a polynomial closed form.  They therefore expose possible combinatorial growth
in closure search.

These are source-level event-count bounds, not wall-clock runtime theorems.
-/

namespace ConstitutiveSearch

universe uGenerator

/--
Worst-case primitive-query contribution of scanning a finite intermediate list,
assuming every recursive sub-search uses at most recursiveBudget primitive
queries.
-/
def viaPrimitiveQueryBudget
    (recursiveBudget : Nat) : Nat → Nat
  | 0 =>
      0
  | candidateCount + 1 =>
      recursiveBudget +
        (recursiveBudget +
          viaPrimitiveQueryBudget
            recursiveBudget
            candidateCount)

/--
Worst-case composition-candidate contribution of scanning a finite intermediate
list, assuming every recursive sub-search uses at most recursiveBudget
composition candidates.
-/
def viaCompositionCandidateBudget
    (recursiveBudget : Nat) : Nat → Nat
  | 0 =>
      0
  | candidateCount + 1 =>
      recursiveBudget +
        (recursiveBudget +
          viaCompositionCandidateBudget
            recursiveBudget
            candidateCount) +
        1

/-- Recursive primitive-query budget of the bounded closure search. -/
def closurePrimitiveQueryBudget
    (candidateCount : Nat) : Nat → Nat
  | 0 =>
      0
  | fuel + 1 =>
      viaPrimitiveQueryBudget
          (closurePrimitiveQueryBudget
            candidateCount
            fuel)
          candidateCount +
        1

/-- Recursive composition-candidate budget of the bounded closure search. -/
def closureCompositionCandidateBudget
    (candidateCount : Nat) : Nat → Nat
  | 0 =>
      0
  | fuel + 1 =>
      viaCompositionCandidateBudget
        (closureCompositionCandidateBudget
          candidateCount
          fuel)
        candidateCount

/--
Candidate scanning preserves an announced recursive primitive-query bound.
-/
theorem searchClosureViaCandidates_primitiveQueries_le
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (recurse :
      (source target : State) →
        ClosureSearchRun Generator source target)
    (recursiveBudget : Nat)
    (recurseBound :
      ∀ source target : State,
        (recurse source target).stats.primitiveQueries ≤
          recursiveBudget) :
    ∀ (candidates : List State) (source target : State),
      (searchClosureViaCandidates
        recurse candidates source target).stats.primitiveQueries ≤
      viaPrimitiveQueryBudget
        recursiveBudget
        candidates.length := by
  intro candidates
  induction candidates with
  | nil =>
      intro source target
      exact Nat.le_refl 0
  | cons middle rest inductionHypothesis =>
      intro source target
      let first := recurse source middle
      have firstLe :
          first.stats.primitiveQueries ≤ recursiveBudget :=
        recurseBound source middle
      cases firstResult : first.code? with
      | none =>
          let later :=
            searchClosureViaCandidates
              recurse rest source target
          have laterLe :
              later.stats.primitiveQueries ≤
                viaPrimitiveQueryBudget
                  recursiveBudget
                  rest.length :=
            inductionHypothesis source target
          have sumLe :
              first.stats.primitiveQueries +
                  later.stats.primitiveQueries ≤
                recursiveBudget +
                  viaPrimitiveQueryBudget
                    recursiveBudget
                    rest.length :=
            Nat.add_le_add firstLe laterLe
          change
            first.stats.primitiveQueries +
                later.stats.primitiveQueries ≤
              recursiveBudget +
                (recursiveBudget +
                  viaPrimitiveQueryBudget
                    recursiveBudget
                    rest.length)
          exact
            Nat.le_trans
              sumLe
              (Nat.le_add_left
                (recursiveBudget +
                  viaPrimitiveQueryBudget
                    recursiveBudget
                    rest.length)
                recursiveBudget)
      | some firstCode =>
          let second := recurse middle target
          have secondLe :
              second.stats.primitiveQueries ≤ recursiveBudget :=
            recurseBound middle target
          cases secondResult : second.code? with
          | some secondCode =>
              have pairLe :
                  first.stats.primitiveQueries +
                      second.stats.primitiveQueries ≤
                    recursiveBudget + recursiveBudget :=
                Nat.add_le_add firstLe secondLe
              change
                first.stats.primitiveQueries +
                    second.stats.primitiveQueries ≤
                  recursiveBudget +
                    (recursiveBudget +
                      viaPrimitiveQueryBudget
                        recursiveBudget
                        rest.length)
              exact
                Nat.le_trans
                  pairLe
                  (Nat.add_le_add
                    (Nat.le_refl recursiveBudget)
                    (Nat.le_add_right
                      recursiveBudget
                      (viaPrimitiveQueryBudget
                        recursiveBudget
                        rest.length)))
          | none =>
              let later :=
                searchClosureViaCandidates
                  recurse rest source target
              have laterLe :
                  later.stats.primitiveQueries ≤
                    viaPrimitiveQueryBudget
                      recursiveBudget
                      rest.length :=
                inductionHypothesis source target
              have firstSecondLe :
                  first.stats.primitiveQueries +
                      second.stats.primitiveQueries ≤
                    recursiveBudget + recursiveBudget :=
                Nat.add_le_add firstLe secondLe
              have allLe :
                  (first.stats.primitiveQueries +
                      second.stats.primitiveQueries) +
                    later.stats.primitiveQueries ≤
                  (recursiveBudget + recursiveBudget) +
                    viaPrimitiveQueryBudget
                      recursiveBudget
                      rest.length :=
                Nat.add_le_add firstSecondLe laterLe
              change
                (first.stats.primitiveQueries +
                    second.stats.primitiveQueries) +
                  later.stats.primitiveQueries ≤
                recursiveBudget +
                  (recursiveBudget +
                    viaPrimitiveQueryBudget
                      recursiveBudget
                      rest.length)
              exact
                Eq.mp
                  (congrArg
                    (fun value =>
                      (first.stats.primitiveQueries +
                          second.stats.primitiveQueries) +
                        later.stats.primitiveQueries ≤
                      value)
                    (Nat.add_assoc
                      recursiveBudget
                      recursiveBudget
                      (viaPrimitiveQueryBudget
                        recursiveBudget
                        rest.length)))
                  allLe

/--
Candidate scanning preserves an announced recursive composition-candidate
bound.
-/
theorem searchClosureViaCandidates_compositionCandidates_le
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (recurse :
      (source target : State) →
        ClosureSearchRun Generator source target)
    (recursiveBudget : Nat)
    (recurseBound :
      ∀ source target : State,
        (recurse source target).stats.compositionCandidates ≤
          recursiveBudget) :
    ∀ (candidates : List State) (source target : State),
      (searchClosureViaCandidates
        recurse candidates source target).stats.compositionCandidates ≤
      viaCompositionCandidateBudget
        recursiveBudget
        candidates.length := by
  intro candidates
  induction candidates with
  | nil =>
      intro source target
      exact Nat.le_refl 0
  | cons middle rest inductionHypothesis =>
      intro source target
      let first := recurse source middle
      have firstLe :
          first.stats.compositionCandidates ≤ recursiveBudget :=
        recurseBound source middle
      cases firstResult : first.code? with
      | none =>
          let later :=
            searchClosureViaCandidates
              recurse rest source target
          have laterLe :
              later.stats.compositionCandidates ≤
                viaCompositionCandidateBudget
                  recursiveBudget
                  rest.length :=
            inductionHypothesis source target
          have sumLe :
              first.stats.compositionCandidates +
                  later.stats.compositionCandidates ≤
                recursiveBudget +
                  viaCompositionCandidateBudget
                    recursiveBudget
                    rest.length :=
            Nat.add_le_add firstLe laterLe
          have widened :
              first.stats.compositionCandidates +
                    later.stats.compositionCandidates ≤
                recursiveBudget +
                  (recursiveBudget +
                    viaCompositionCandidateBudget
                      recursiveBudget
                      rest.length) :=
            Nat.le_trans
              sumLe
              (Nat.le_add_left
                (recursiveBudget +
                  viaCompositionCandidateBudget
                    recursiveBudget
                    rest.length)
                recursiveBudget)
          change
            first.stats.compositionCandidates +
                  later.stats.compositionCandidates +
                1 ≤
              recursiveBudget +
                  (recursiveBudget +
                    viaCompositionCandidateBudget
                      recursiveBudget
                      rest.length) +
                1
          exact
            Nat.add_le_add_right widened 1
      | some firstCode =>
          let second := recurse middle target
          have secondLe :
              second.stats.compositionCandidates ≤ recursiveBudget :=
            recurseBound middle target
          cases secondResult : second.code? with
          | some secondCode =>
              have pairLe :
                  first.stats.compositionCandidates +
                      second.stats.compositionCandidates ≤
                    recursiveBudget + recursiveBudget :=
                Nat.add_le_add firstLe secondLe
              have widened :
                  first.stats.compositionCandidates +
                      second.stats.compositionCandidates ≤
                    recursiveBudget +
                      (recursiveBudget +
                        viaCompositionCandidateBudget
                          recursiveBudget
                          rest.length) :=
                Nat.le_trans
                  pairLe
                  (Nat.add_le_add
                    (Nat.le_refl recursiveBudget)
                    (Nat.le_add_right
                      recursiveBudget
                      (viaCompositionCandidateBudget
                        recursiveBudget
                        rest.length)))
              change
                first.stats.compositionCandidates +
                      second.stats.compositionCandidates +
                    1 ≤
                  recursiveBudget +
                      (recursiveBudget +
                        viaCompositionCandidateBudget
                          recursiveBudget
                          rest.length) +
                    1
              exact
                Nat.add_le_add_right widened 1
          | none =>
              let later :=
                searchClosureViaCandidates
                  recurse rest source target
              have laterLe :
                  later.stats.compositionCandidates ≤
                    viaCompositionCandidateBudget
                      recursiveBudget
                      rest.length :=
                inductionHypothesis source target
              have allLe :
                  (first.stats.compositionCandidates +
                      second.stats.compositionCandidates) +
                    later.stats.compositionCandidates ≤
                  (recursiveBudget + recursiveBudget) +
                    viaCompositionCandidateBudget
                      recursiveBudget
                      rest.length :=
                Nat.add_le_add
                  (Nat.add_le_add firstLe secondLe)
                  laterLe
              have associated :
                  (first.stats.compositionCandidates +
                      second.stats.compositionCandidates) +
                    later.stats.compositionCandidates ≤
                  recursiveBudget +
                    (recursiveBudget +
                      viaCompositionCandidateBudget
                        recursiveBudget
                        rest.length) :=
                Eq.mp
                  (congrArg
                    (fun value =>
                      (first.stats.compositionCandidates +
                          second.stats.compositionCandidates) +
                        later.stats.compositionCandidates ≤
                      value)
                    (Nat.add_assoc
                      recursiveBudget
                      recursiveBudget
                      (viaCompositionCandidateBudget
                        recursiveBudget
                        rest.length)))
                  allLe
              change
                ((first.stats.compositionCandidates +
                    second.stats.compositionCandidates) +
                  later.stats.compositionCandidates) +
                    1 ≤
                  recursiveBudget +
                    (recursiveBudget +
                      viaCompositionCandidateBudget
                        recursiveBudget
                        rest.length) +
                    1
              exact
                Nat.add_le_add_right associated 1

/-- Primitive relation queries are bounded solely by fuel and candidate count. -/
theorem searchTransportClosureBounded_primitiveQueries_le
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State) :
    ∀ (fuel : Nat) (source target : State),
      (searchTransportClosureBounded
        primitive candidates fuel source target).stats.primitiveQueries ≤
      closurePrimitiveQueryBudget
        candidates.length
        fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro source target
      exact Nat.le_refl 0
  | succ fuel inductionHypothesis =>
      intro source target
      cases direct : primitive.find source target with
      | some witness =>
          change
            1 ≤
              viaPrimitiveQueryBudget
                  (closurePrimitiveQueryBudget
                    candidates.length
                    fuel)
                  candidates.length +
                1
          exact
            Nat.le_add_left
              1
              (viaPrimitiveQueryBudget
                (closurePrimitiveQueryBudget
                  candidates.length
                  fuel)
                candidates.length)
      | none =>
          let via :=
            searchClosureViaCandidates
              (fun left right =>
                searchTransportClosureBounded
                  primitive
                  candidates
                  fuel
                  left
                  right)
              candidates
              source
              target
          have viaLe :
              via.stats.primitiveQueries ≤
                viaPrimitiveQueryBudget
                  (closurePrimitiveQueryBudget
                    candidates.length
                    fuel)
                  candidates.length :=
            searchClosureViaCandidates_primitiveQueries_le
              (fun left right =>
                searchTransportClosureBounded
                  primitive
                  candidates
                  fuel
                  left
                  right)
              (closurePrimitiveQueryBudget
                candidates.length
                fuel)
              inductionHypothesis
              candidates
              source
              target
          change
            via.stats.primitiveQueries + 1 ≤
              viaPrimitiveQueryBudget
                  (closurePrimitiveQueryBudget
                    candidates.length
                    fuel)
                  candidates.length +
                1
          exact
            Nat.add_le_add_right viaLe 1

/-- Composition candidates are bounded solely by fuel and candidate count. -/
theorem searchTransportClosureBounded_compositionCandidates_le
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (candidates : List State) :
    ∀ (fuel : Nat) (source target : State),
      (searchTransportClosureBounded
        primitive candidates fuel source target).stats.compositionCandidates ≤
      closureCompositionCandidateBudget
        candidates.length
        fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro source target
      exact Nat.le_refl 0
  | succ fuel inductionHypothesis =>
      intro source target
      cases direct : primitive.find source target with
      | some witness =>
          exact Nat.zero_le _
      | none =>
          exact
            searchClosureViaCandidates_compositionCandidates_le
              (fun left right =>
                searchTransportClosureBounded
                  primitive
                  candidates
                  fuel
                  left
                  right)
              (closureCompositionCandidateBudget
                candidates.length
                fuel)
              inductionHypothesis
              candidates
              source
              target

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.viaPrimitiveQueryBudget
#print axioms ConstitutiveSearch.viaCompositionCandidateBudget
#print axioms ConstitutiveSearch.closurePrimitiveQueryBudget
#print axioms ConstitutiveSearch.closureCompositionCandidateBudget
#print axioms ConstitutiveSearch.searchClosureViaCandidates_primitiveQueries_le
#print axioms ConstitutiveSearch.searchClosureViaCandidates_compositionCandidates_le
#print axioms ConstitutiveSearch.searchTransportClosureBounded_primitiveQueries_le
#print axioms ConstitutiveSearch.searchTransportClosureBounded_compositionCandidates_le
/- AXIOM_AUDIT_END -/
