import ConstitutiveSearch.ConstitutiveWidth

/-!
# Constructive normalization of finite search frontiers

This module extends certified pair reduction to arbitrary finite frontiers.
The normalization remains relative to one executable relation search. A failed
search is never reinterpreted as semantic non-existence.

The construction is insertion-based. The tail is normalized first. A new head
state is then compared against the already irreducible retained tail. Positive
directional witnesses absorb one state into another. An unresolved comparison
keeps both states and continues with the remaining tail.

To prove final irreducibility without adding any external ordering assumption,
the insertion result carries a provenance invariant: every retained state is
either the inserted state itself or a state already present in the irreducible
tail.
-/

namespace ConstitutiveSearch

universe uState uRelation uCompletion

namespace FrontierCompletion

/-- Reorder the first two frontier states without changing any completion data. -/
def swapFirstTwo
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {first second : State}
    {rest : List State} :
    FrontierTransport Completion
      (first :: second :: rest)
      (second :: first :: rest) :=
  { map := fun frontier =>
      match frontier with
      | .head firstCompletion =>
          .tail (.head firstCompletion)
      | .tail (.head secondCompletion) =>
          .head secondCompletion
      | .tail (.tail tailCompletion) =>
          .tail (.tail tailCompletion) }

/-- Lift a frontier transport under one preserved head state. -/
def prependTransport
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {head : State}
    {source target : List State}
    (transport : FrontierTransport Completion source target) :
    FrontierTransport Completion
      (head :: source)
      (head :: target) :=
  { map := fun frontier =>
      match frontier with
      | .head headCompletion =>
          .head headCompletion
      | .tail tailCompletion =>
          .tail (transport.map tailCompletion) }

end FrontierCompletion

/--
Result of inserting one state into an already search-irreducible frontier.
`retainedFromSource` is the local provenance invariant needed to reconstruct
irreducibility after unresolved comparisons.
-/
structure InsertIrreducibleReduction
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (search : RelationSearch Relation)
    (state : State)
    (rest : List State) where
  retained : List State
  transport : FrontierTransport Completion (state :: rest) retained
  irreducible : SearchIrreducible search retained
  retainedFromSource :
    ∀ candidate : State,
      candidate ∈ retained →
        candidate = state ∨ candidate ∈ rest

namespace InsertIrreducibleReduction

/-- Width is measured only after the insertion reduction has been built. -/
def width
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    {search : RelationSearch Relation}
    {state : State}
    {rest : List State}
    (reduction :
      InsertIrreducibleReduction
        (Completion := Completion) search state rest) : Nat :=
  reduction.retained.length

end InsertIrreducibleReduction

/--
Insert one state into an irreducible frontier by executable pair search.

A forward witness from the inserted state into the current head absorbs the
inserted state. A backward witness absorbs the current head and continues with
the inserted state. An unresolved pair keeps the current head and recursively
continues the comparison against the remaining tail.
-/
def insertIntoIrreducible
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (search : RelationSearch Relation)
    (action : RelationalContinuationAction Relation Completion)
    (state : State) :
    (rest : List State) →
      SearchIrreducible search rest →
        InsertIrreducibleReduction
          (Completion := Completion) search state rest
  | [], _ =>
      { retained := [state]
        transport := ContinuationTransport.identity [state]
        irreducible := SearchIrreducible.singleton search state
        retainedFromSource := fun candidate member => by
          cases member with
          | head => exact Or.inl rfl
          | tail _ impossible => cases impossible }
  | current :: tail, restIrreducible =>
      let currentAgainstTail := restIrreducible.1
      let tailIrreducible := restIrreducible.2
      match classification : search.classifyPairCertified state current with
      | .bidirectional forward _backward _forwardFound _backwardFound =>
          { retained := current :: tail
            transport :=
              FrontierCompletion.absorbFirstIntoSecond
                (rest := tail)
                (action.toTransport forward)
            irreducible := restIrreducible
            retainedFromSource := fun _candidate member =>
              Or.inr member }
      | .forwardOnly forward _forwardFound _backwardNotFound =>
          { retained := current :: tail
            transport :=
              FrontierCompletion.absorbFirstIntoSecond
                (rest := tail)
                (action.toTransport forward)
            irreducible := restIrreducible
            retainedFromSource := fun _candidate member =>
              Or.inr member }
      | .backwardOnly backward _forwardNotFound _backwardFound =>
          let recursive :=
            insertIntoIrreducible
              search action state tail tailIrreducible
          { retained := recursive.retained
            transport :=
              (FrontierCompletion.absorbSecondIntoFirst
                (rest := tail)
                (action.toTransport backward)).trans
                recursive.transport
            irreducible := recursive.irreducible
            retainedFromSource := fun candidate member => by
              cases recursive.retainedFromSource candidate member with
              | inl inserted =>
                  exact Or.inl inserted
              | inr tailMember =>
                  exact Or.inr (List.mem_cons_of_mem current tailMember) }
      | .unresolved forwardNotFound backwardNotFound =>
          let recursive :=
            insertIntoIrreducible
              search action state tail tailIrreducible
          have currentAgainstRetained :
              ∀ other : State,
                other ∈ recursive.retained →
                  search.find current other = none ∧
                    search.find other current = none := by
            intro other member
            cases recursive.retainedFromSource other member with
            | inl inserted =>
                cases inserted
                exact ⟨backwardNotFound, forwardNotFound⟩
            | inr tailMember =>
                exact currentAgainstTail other tailMember
          { retained := current :: recursive.retained
            transport :=
              (FrontierCompletion.swapFirstTwo
                (Completion := Completion)
                (first := state)
                (second := current)
                (rest := tail)).trans
                (FrontierCompletion.prependTransport
                  (head := current)
                  recursive.transport)
            irreducible :=
              ⟨currentAgainstRetained, recursive.irreducible⟩
            retainedFromSource := fun candidate member => by
              cases member with
              | head =>
                  exact Or.inr (List.mem_cons_self)
              | tail _ recursiveMember =>
                  cases recursive.retainedFromSource candidate recursiveMember with
                  | inl inserted =>
                      exact Or.inl inserted
                  | inr tailMember =>
                      exact Or.inr (List.mem_cons_of_mem current tailMember) }

/--
Normalize any finite frontier to a search-relative irreducible frontier while
constructively transporting every positive completion.
-/
def normalizeFrontier
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (search : RelationSearch Relation)
    (action : RelationalContinuationAction Relation Completion) :
    (source : List State) →
      IrreducibleFrontierReduction
        (Completion := Completion) search source
  | [] =>
      IrreducibleFrontierReduction.empty search
  | state :: tail =>
      let tailReduction := normalizeFrontier search action tail
      let inserted :=
        insertIntoIrreducible
          search action state
          tailReduction.retained
          tailReduction.irreducible
      { retained := inserted.retained
        transport :=
          (FrontierCompletion.prependTransport
            (head := state)
            tailReduction.transport).trans
            inserted.transport
        irreducible := inserted.irreducible }

/-- Derived normalized width of an arbitrary finite frontier. -/
def normalizedWidth
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (search : RelationSearch Relation)
    (action : RelationalContinuationAction Relation Completion)
    (source : List State) : Nat :=
  (normalizeFrontier search action source).width

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.FrontierCompletion.swapFirstTwo
#print axioms ConstitutiveSearch.FrontierCompletion.prependTransport
#print axioms ConstitutiveSearch.InsertIrreducibleReduction
#print axioms ConstitutiveSearch.InsertIrreducibleReduction.width
#print axioms ConstitutiveSearch.insertIntoIrreducible
#print axioms ConstitutiveSearch.normalizeFrontier
#print axioms ConstitutiveSearch.normalizedWidth
/- AXIOM_AUDIT_END -/
