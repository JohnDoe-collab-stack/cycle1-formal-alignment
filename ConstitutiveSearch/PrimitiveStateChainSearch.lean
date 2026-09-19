import Init.Omega
import ConstitutiveSearch.SequentialPrimitiveExecution

/-!
# Local primitive-code search on an ordered state chain

Global ClosureSearch explores an unordered candidate domain to discover a
composed relation between two endpoints.  When the constitution already
supplies an ordered chain of intermediate states, that global discovery problem
can be replaced by adjacent primitive searches.

PrimitiveStateChain stores only the ordered states, not relation witnesses.
searchPrimitiveStateChain queries the announced primitive RelationSearch on
each adjacent pair and directly compiles successful witnesses into a
TransportCode.

If all adjacent queries succeed, the result is a code whose atom count is
exactly the chain length.  The executable control cost is then:
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

/-- Result of executable adjacent primitive search on one ordered state chain. -/
structure PrimitiveStateChainSearchRun
    {State : Type}
    (Generator : State → State → Type uGenerator)
    (source target : State) where
  code? :
    Option
      (TransportClosure
        Generator
        source
        target)
  stats : ClosureSearchStats

/--
Search only adjacent pairs of an already ordered chain.

On the first failed adjacent primitive query, the search stops.  On success,
the found witness is composed directly with the recursively reconstructed code.
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
        Generator
        source
        target
  | _, _, .identity state =>
      { code? :=
          some
            (.identity state)
        stats :=
          ClosureSearchStats.zero }
  | source, target, .step middle tail =>
      match
        primitive.find source middle with
      | none =>
          { code? := none
            stats :=
              ClosureSearchStats.withPrimitiveQuery
                ClosureSearchStats.zero }
      | some witness =>
          let later :=
            searchPrimitiveStateChain
              primitive
              tail
          match later.code? with
          | none =>
              { code? := none
                stats :=
                  ClosureSearchStats.withPrimitiveQuery
                    later.stats }
          | some code =>
              { code? :=
                  some
                    (.compose
                      (.atom witness)
                      code)
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
      cases firstFound :
          primitive.find source middle with
      | none =>
          simp only [
            searchPrimitiveStateChain,
            firstFound,
            ClosureSearchStats.withPrimitiveQuery,
            ClosureSearchStats.zero
          ]
      | some witness =>
          cases laterFound :
              (searchPrimitiveStateChain
                primitive
                tail).code? with
          | none =>
              simp only [
                searchPrimitiveStateChain,
                firstFound,
                laterFound,
                ClosureSearchStats.withPrimitiveQuery
              ]
              exact inductionHypothesis
          | some code =>
              simp only [
                searchPrimitiveStateChain,
                firstFound,
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
      cases firstFound :
          primitive.find source middle with
      | none =>
          simp only [
            searchPrimitiveStateChain,
            firstFound,
            ClosureSearchStats.withPrimitiveQuery,
            ClosureSearchStats.zero,
            PrimitiveStateChain.length
          ]
          omega
      | some witness =>
          cases laterFound :
              (searchPrimitiveStateChain
                primitive
                tail).code? with
          | none =>
              simp only [
                searchPrimitiveStateChain,
                firstFound,
                laterFound,
                ClosureSearchStats.withPrimitiveQuery,
                PrimitiveStateChain.length
              ]
              omega
          | some code =>
              simp only [
                searchPrimitiveStateChain,
                firstFound,
                laterFound,
                ClosureSearchStats.withPrimitiveQuery,
                PrimitiveStateChain.length
              ]
              omega

/-- On success, local chain search performs exactly one primitive query per edge. -/
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
    {code :
      TransportClosure
        Generator
        source
        target}
    (found :
      (searchPrimitiveStateChain
        primitive
        chain).code? =
          some code) :
    (searchPrimitiveStateChain
      primitive
      chain).stats.primitiveQueries =
      chain.length := by
  induction chain with
  | identity state =>
      rfl
  | @step source target middle tail inductionHypothesis =>
      cases firstFound :
          primitive.find source middle with
      | none =>
          simp only [
            searchPrimitiveStateChain,
            firstFound
          ] at found
          cases found
      | some witness =>
          cases laterFound :
              (searchPrimitiveStateChain
                primitive
                tail).code? with
          | none =>
              simp only [
                searchPrimitiveStateChain,
                firstFound,
                laterFound
              ] at found
              cases found
          | some tailCode =>
              simp only [
                searchPrimitiveStateChain,
                firstFound,
                laterFound,
                ClosureSearchStats.withPrimitiveQuery,
                PrimitiveStateChain.length
              ] at found ⊢
              rw [
                inductionHypothesis
                  laterFound
              ]

/-- A successfully reconstructed local code has exactly one atom per chain edge. -/
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
    {code :
      TransportClosure
        Generator
        source
        target}
    (found :
      (searchPrimitiveStateChain
        primitive
        chain).code? =
          some code) :
    code.size =
      chain.length := by
  induction chain with
  | identity state =>
      simp only [
        searchPrimitiveStateChain
      ] at found
      injection found with codeExact
      subst code
      rfl
  | @step source target middle tail inductionHypothesis =>
      cases firstFound :
          primitive.find source middle with
      | none =>
          simp only [
            searchPrimitiveStateChain,
            firstFound
          ] at found
          cases found
      | some witness =>
          cases laterFound :
              (searchPrimitiveStateChain
                primitive
                tail).code? with
          | none =>
              simp only [
                searchPrimitiveStateChain,
                firstFound,
                laterFound
              ] at found
              cases found
          | some tailCode =>
              simp only [
                searchPrimitiveStateChain,
                firstFound,
                laterFound
              ] at found
              injection found with codeExact
              subst code
              change
                1 + tailCode.size =
                  tail.length + 1
              rw [
                inductionHypothesis
                  laterFound
              ]
              exact
                Nat.add_comm
                  1
                  tail.length

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.PrimitiveStateChain
#print axioms ConstitutiveSearch.PrimitiveStateChain.length
#print axioms ConstitutiveSearch.PrimitiveStateChainSearchRun
#print axioms ConstitutiveSearch.searchPrimitiveStateChain
#print axioms ConstitutiveSearch.searchPrimitiveStateChain_compositionCandidates_zero
#print axioms ConstitutiveSearch.searchPrimitiveStateChain_primitiveQueries_le_length
#print axioms ConstitutiveSearch.searchPrimitiveStateChain_found_primitiveQueries
#print axioms ConstitutiveSearch.searchPrimitiveStateChain_found_code_size
/- AXIOM_AUDIT_END -/
