import Init.Omega
import ConstitutiveSearch.SequentialPrimitiveExecution

/-!
# Local primitive-path search on an ordered state chain

Global ClosureSearch explores an unordered candidate domain to discover a
composed relation between two endpoints.  When the constitution already
supplies an ordered chain of intermediate states, that global discovery problem
can be replaced by adjacent primitive searches.

PrimitiveStateChain stores only the ordered states, not relation witnesses.
searchPrimitiveStateChain reconstructs those witnesses executablely by querying
the announced primitive RelationSearch on each adjacent pair.

If all adjacent queries succeed, the result is a PrimitiveHitPath and therefore
a TransportCode.  The search then has exact source-level control cost:
* one primitive query per chain edge;
* zero composition-candidate queries.

No satisfiability or semantic acceptance decision is introduced here.
-/

namespace ConstitutiveSearch

universe uGenerator

/-- Ordered finite chain of states, without relation witnesses. -/
inductive PrimitiveStateChain
    (State : Type) :
    State → State → Type where
  | identity
      (state : State) :
      PrimitiveStateChain State state state
  | step
      {source target : State}
      (middle : State)
      (tail :
        PrimitiveStateChain
          State
          middle
          target) :
      PrimitiveStateChain
        State
        source
        target

namespace PrimitiveStateChain

/-- Number of adjacent edges in the ordered chain. -/
def length
    {State : Type}
    {source target : State} :
    PrimitiveStateChain
      State
      source
      target →
    Nat
  | .identity _ =>
      0
  | .step _ tail =>
      tail.length + 1

end PrimitiveStateChain

/-- One executable primitive-search hit, with the exact returned witness. -/
structure PrimitiveSearchHit
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (source target : State) where
  witness : Generator source target
  exactFind :
    primitive.find source target =
      some witness

/-- Package one RelationSearch result into explicit hit evidence when present. -/
def findPrimitiveHit?
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (source target : State) :
    Option
      (PrimitiveSearchHit
        primitive
        source
        target) :=
  match exactFind :
      primitive.find source target with
  | none =>
      none
  | some witness =>
      some
        { witness := witness
          exactFind := exactFind }

/-- Any exact primitive-search equality yields a packaged primitive hit. -/
theorem findPrimitiveHit?_some_of_exact
    {State : Type}
    {Generator : State → State → Type uGenerator}
    {primitive : RelationSearch Generator}
    {source target : State}
    {witness : Generator source target}
    (exactFind :
      primitive.find source target =
        some witness) :
    ∃ hit :
        PrimitiveSearchHit
          primitive
          source
          target,
      findPrimitiveHit?
          primitive
          source
          target =
        some hit := by
  unfold findPrimitiveHit?
  rw [exactFind]
  exact ⟨_, rfl⟩

/-- Result of executable adjacent primitive search on one ordered state chain. -/
structure PrimitiveStateChainSearchRun
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    (source target : State) where
  path? :
    Option
      (PrimitiveHitPath
        primitive
        source
        target)
  stats : ClosureSearchStats

/--
Search only adjacent pairs of an already ordered chain.

On the first failed adjacent primitive query, the search stops.  Successful
prefix queries are therefore never followed by candidate enumeration.
-/
def searchPrimitiveStateChain
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator) :
    {source target : State} →
      PrimitiveStateChain
        State
        source
        target →
      PrimitiveStateChainSearchRun
        primitive
        source
        target
  | _, _, .identity state =>
      { path? :=
          some
            (.identity state)
        stats :=
          ClosureSearchStats.zero }
  | source, target, .step middle tail =>
      match
        findPrimitiveHit?
          primitive
          source
          middle with
      | none =>
          { path? := none
            stats :=
              ClosureSearchStats.withPrimitiveQuery
                ClosureSearchStats.zero }
      | some edge =>
          let later :=
            searchPrimitiveStateChain
              primitive
              tail
          match later.path? with
          | none =>
              { path? := none
                stats :=
                  ClosureSearchStats.withPrimitiveQuery
                    later.stats }
          | some path =>
              { path? :=
                  some
                    (.step
                      edge.exactFind
                      path)
                stats :=
                  ClosureSearchStats.withPrimitiveQuery
                    later.stats }

/-- Local chain search never inspects a composition candidate. -/
theorem searchPrimitiveStateChain_compositionCandidates_zero
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (chain :
      PrimitiveStateChain
        State
        source
        target) :
    (searchPrimitiveStateChain
      primitive
      chain).stats.compositionCandidates =
      0 := by
  induction chain with
  | identity state =>
      rfl
  | @step source target middle tail inductionHypothesis =>
      cases firstHit :
          findPrimitiveHit?
            primitive
            source
            middle with
      | none =>
          simp only [
            searchPrimitiveStateChain,
            firstHit,
            ClosureSearchStats.withPrimitiveQuery,
            ClosureSearchStats.zero
          ]
      | some edge =>
          cases laterFound :
              (searchPrimitiveStateChain
                primitive
                tail).path? with
          | none =>
              simp only [
                searchPrimitiveStateChain,
                firstHit,
                laterFound,
                ClosureSearchStats.withPrimitiveQuery
              ]
              exact inductionHypothesis
          | some path =>
              simp only [
                searchPrimitiveStateChain,
                firstHit,
                laterFound,
                ClosureSearchStats.withPrimitiveQuery
              ]
              exact inductionHypothesis

/-- The local chain search never performs more primitive queries than edges. -/
theorem searchPrimitiveStateChain_primitiveQueries_le_length
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (chain :
      PrimitiveStateChain
        State
        source
        target) :
    (searchPrimitiveStateChain
      primitive
      chain).stats.primitiveQueries ≤
      chain.length := by
  induction chain with
  | identity state =>
      exact Nat.le_refl 0
  | @step source target middle tail inductionHypothesis =>
      cases firstHit :
          findPrimitiveHit?
            primitive
            source
            middle with
      | none =>
          simp only [
            searchPrimitiveStateChain,
            firstHit,
            ClosureSearchStats.withPrimitiveQuery,
            ClosureSearchStats.zero,
            PrimitiveStateChain.length
          ]
          omega
      | some edge =>
          cases laterFound :
              (searchPrimitiveStateChain
                primitive
                tail).path? with
          | none =>
              simp only [
                searchPrimitiveStateChain,
                firstHit,
                laterFound,
                ClosureSearchStats.withPrimitiveQuery,
                PrimitiveStateChain.length
              ]
              omega
          | some path =>
              simp only [
                searchPrimitiveStateChain,
                firstHit,
                laterFound,
                ClosureSearchStats.withPrimitiveQuery,
                PrimitiveStateChain.length
              ]
              omega

/-- A successful local chain search reconstructs a path with the same length. -/
theorem searchPrimitiveStateChain_found_path_length
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (chain :
      PrimitiveStateChain
        State
        source
        target)
    {path :
      PrimitiveHitPath
        primitive
        source
        target}
    (found :
      (searchPrimitiveStateChain
        primitive
        chain).path? =
          some path) :
    path.length =
      chain.length := by
  induction chain with
  | identity state =>
      simp only [
        searchPrimitiveStateChain
      ] at found
      injection found with pathExact
      subst path
      rfl
  | @step source target middle tail inductionHypothesis =>
      cases firstHit :
          findPrimitiveHit?
            primitive
            source
            middle with
      | none =>
          simp only [
            searchPrimitiveStateChain,
            firstHit
          ] at found
          cases found
      | some edge =>
          cases laterFound :
              (searchPrimitiveStateChain
                primitive
                tail).path? with
          | none =>
              simp only [
                searchPrimitiveStateChain,
                firstHit,
                laterFound
              ] at found
              cases found
          | some tailPath =>
              simp only [
                searchPrimitiveStateChain,
                firstHit,
                laterFound
              ] at found
              injection found with pathExact
              subst path
              change
                tailPath.length + 1 =
                  tail.length + 1
              rw [
                inductionHypothesis
                  laterFound
              ]

/--
On success, local chain search performs exactly one primitive query per edge.
-/
theorem searchPrimitiveStateChain_found_primitiveQueries
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (chain :
      PrimitiveStateChain
        State
        source
        target)
    {path :
      PrimitiveHitPath
        primitive
        source
        target}
    (found :
      (searchPrimitiveStateChain
        primitive
        chain).path? =
          some path) :
    (searchPrimitiveStateChain
      primitive
      chain).stats.primitiveQueries =
      chain.length := by
  induction chain with
  | identity state =>
      rfl
  | @step source target middle tail inductionHypothesis =>
      cases firstHit :
          findPrimitiveHit?
            primitive
            source
            middle with
      | none =>
          simp only [
            searchPrimitiveStateChain,
            firstHit
          ] at found
          cases found
      | some edge =>
          cases laterFound :
              (searchPrimitiveStateChain
                primitive
                tail).path? with
          | none =>
              simp only [
                searchPrimitiveStateChain,
                firstHit,
                laterFound
              ] at found
              cases found
          | some tailPath =>
              simp only [
                searchPrimitiveStateChain,
                firstHit,
                laterFound,
                ClosureSearchStats.withPrimitiveQuery,
                PrimitiveStateChain.length
              ] at found ⊢
              rw [
                inductionHypothesis
                  laterFound
              ]
              omega

/-- Successful local path reconstruction compiles to a code of chain length. -/
theorem searchPrimitiveStateChain_found_code_size
    {State : Type}
    {Generator : State → State → Type uGenerator}
    (primitive : RelationSearch Generator)
    {source target : State}
    (chain :
      PrimitiveStateChain
        State
        source
        target)
    {path :
      PrimitiveHitPath
        primitive
        source
        target}
    (found :
      (searchPrimitiveStateChain
        primitive
        chain).path? =
          some path) :
    path.toTransportCode.size =
      chain.length := by
  calc
    path.toTransportCode.size
        =
      path.length :=
        path.toTransportCode_size
    _ =
      chain.length :=
        searchPrimitiveStateChain_found_path_length
          primitive
          chain
          found

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.PrimitiveStateChain
#print axioms ConstitutiveSearch.PrimitiveStateChain.length
#print axioms ConstitutiveSearch.PrimitiveSearchHit
#print axioms ConstitutiveSearch.findPrimitiveHit?
#print axioms ConstitutiveSearch.findPrimitiveHit?_some_of_exact
#print axioms ConstitutiveSearch.PrimitiveStateChainSearchRun
#print axioms ConstitutiveSearch.searchPrimitiveStateChain
#print axioms ConstitutiveSearch.searchPrimitiveStateChain_compositionCandidates_zero
#print axioms ConstitutiveSearch.searchPrimitiveStateChain_primitiveQueries_le_length
#print axioms ConstitutiveSearch.searchPrimitiveStateChain_found_path_length
#print axioms ConstitutiveSearch.searchPrimitiveStateChain_found_primitiveQueries
#print axioms ConstitutiveSearch.searchPrimitiveStateChain_found_code_size
/- AXIOM_AUDIT_END -/
