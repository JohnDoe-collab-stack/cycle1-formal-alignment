import ConstitutiveSearch.FiniteFrontierNormalization

/-!
# Constructive preservation of finite search frontiers

A directional frontier transport is sufficient to prove that a positive source
completion is not lost.  A decision procedure also needs the retained frontier
to remain interpretable in the source frontier.

This module records the two directions separately.  They are not required to be
inverse functions.  In particular, the backward map of an absorption is only
the structural inclusion of the retained states into the original frontier.
No inverse of the directional continuation transport is manufactured.
-/

namespace ConstitutiveSearch

universe uState uCompletion uRelation

/--
Two directional frontier transports witnessing preservation of positive
completion existence in both directions.

No round-trip law is included.
-/
structure FrontierPreservation
    {State : Type uState}
    (Completion : State → Type uCompletion)
    (source target : List State) where
  forward : FrontierTransport Completion source target
  backward : FrontierTransport Completion target source

namespace FrontierPreservation

/-- Every frontier preserves itself. -/
def identity
    {State : Type uState}
    {Completion : State → Type uCompletion}
    (frontier : List State) :
    FrontierPreservation Completion frontier frontier :=
  { forward := ContinuationTransport.identity frontier
    backward := ContinuationTransport.identity frontier }

/-- Frontier preservations compose without requiring either side to be invertible. -/
def trans
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {first second third : List State}
    (left : FrontierPreservation Completion first second)
    (right : FrontierPreservation Completion second third) :
    FrontierPreservation Completion first third :=
  { forward := left.forward.trans right.forward
    backward := right.backward.trans left.backward }

/-- Positive completion existence is equivalent across a preservation witness. -/
theorem nonempty_iff
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {source target : List State}
    (preservation : FrontierPreservation Completion source target) :
    Nonempty (FrontierCompletion Completion source) ↔
      Nonempty (FrontierCompletion Completion target) := by
  constructor
  · exact preservation.forward.preservesExistence
  · exact preservation.backward.preservesExistence

/--
An exact binary split preserves the frontier in both directions.  The backward
map uses the split merger and leaves the untouched tail unchanged.
-/
def expandHead
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {parent left right : State}
    {rest : List State}
    (splitter : ExactBinarySplit Completion parent left right) :
    FrontierPreservation Completion
      (parent :: rest)
      (left :: right :: rest) :=
  { forward := FrontierCompletion.expandHead splitter
    backward :=
      { map := fun frontier =>
          match frontier with
          | .head leftCompletion =>
              .head (splitter.merge (.inl leftCompletion))
          | .tail (.head rightCompletion) =>
              .head (splitter.merge (.inr rightCompletion))
          | .tail (.tail restCompletion) =>
              .tail restCompletion } }

/--
Absorb the first state into the second while retaining a structural inclusion
from the retained frontier back into the source frontier.
-/
def absorbFirstIntoSecond
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {first second : State}
    {rest : List State}
    (transport : ContinuationTransport Completion first second) :
    FrontierPreservation Completion
      (first :: second :: rest)
      (second :: rest) :=
  { forward := FrontierCompletion.absorbFirstIntoSecond transport
    backward :=
      { map := fun frontier =>
          match frontier with
          | .head secondCompletion =>
              .tail (.head secondCompletion)
          | .tail restCompletion =>
              .tail (.tail restCompletion) } }

/-- Symmetric preservation for absorption of the second state into the first. -/
def absorbSecondIntoFirst
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {first second : State}
    {rest : List State}
    (transport : ContinuationTransport Completion second first) :
    FrontierPreservation Completion
      (first :: second :: rest)
      (first :: rest) :=
  { forward := FrontierCompletion.absorbSecondIntoFirst transport
    backward :=
      { map := fun frontier =>
          match frontier with
          | .head firstCompletion =>
              .head firstCompletion
          | .tail restCompletion =>
              .tail (.tail restCompletion) } }

/-- Swapping the first two frontier states is preservation in both directions. -/
def swapFirstTwo
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {first second : State}
    {rest : List State} :
    FrontierPreservation Completion
      (first :: second :: rest)
      (second :: first :: rest) :=
  { forward := FrontierCompletion.swapFirstTwo
    backward := FrontierCompletion.swapFirstTwo }

/-- Preserve one unchanged head state above an existing frontier preservation. -/
def prepend
    {State : Type uState}
    {Completion : State → Type uCompletion}
    {head : State}
    {source target : List State}
    (preservation : FrontierPreservation Completion source target) :
    FrontierPreservation Completion
      (head :: source)
      (head :: target) :=
  { forward := FrontierCompletion.prependTransport preservation.forward
    backward := FrontierCompletion.prependTransport preservation.backward }

end FrontierPreservation

/--
Insertion into an already irreducible frontier with preservation in both
directions.  The retained-state provenance invariant is kept explicit because
it is also needed to rebuild irreducibility after unresolved comparisons.
-/
structure PreservingInsertReduction
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (search : RelationSearch Relation)
    (state : State)
    (rest : List State) where
  retained : List State
  preservation : FrontierPreservation Completion (state :: rest) retained
  irreducible : SearchIrreducible search retained
  retainedFromSource :
    ∀ candidate : State,
      candidate ∈ retained →
        candidate = state ∨ candidate ∈ rest

/--
Insert one state into a search-irreducible frontier while preserving positive
completion existence in both directions.
-/
def insertIntoIrreduciblePreserving
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (search : RelationSearch Relation)
    (action : RelationalContinuationAction Relation Completion)
    (state : State) :
    (rest : List State) →
      SearchIrreducible search rest →
        PreservingInsertReduction
          (Completion := Completion) search state rest
  | [], _ =>
      { retained := [state]
        preservation := FrontierPreservation.identity [state]
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
            preservation :=
              FrontierPreservation.absorbFirstIntoSecond
                (rest := tail)
                (action.toTransport forward)
            irreducible := restIrreducible
            retainedFromSource := fun _candidate member =>
              Or.inr member }
      | .forwardOnly forward _forwardFound _backwardNotFound =>
          { retained := current :: tail
            preservation :=
              FrontierPreservation.absorbFirstIntoSecond
                (rest := tail)
                (action.toTransport forward)
            irreducible := restIrreducible
            retainedFromSource := fun _candidate member =>
              Or.inr member }
      | .backwardOnly backward _forwardNotFound _backwardFound =>
          let recursive :=
            insertIntoIrreduciblePreserving
              search action state tail tailIrreducible
          { retained := recursive.retained
            preservation :=
              (FrontierPreservation.absorbSecondIntoFirst
                (rest := tail)
                (action.toTransport backward)).trans
                recursive.preservation
            irreducible := recursive.irreducible
            retainedFromSource := fun candidate member => by
              cases recursive.retainedFromSource candidate member with
              | inl inserted =>
                  exact Or.inl inserted
              | inr tailMember =>
                  exact Or.inr (List.mem_cons_of_mem current tailMember) }
      | .unresolved forwardNotFound backwardNotFound =>
          let recursive :=
            insertIntoIrreduciblePreserving
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
            preservation :=
              (FrontierPreservation.swapFirstTwo
                (Completion := Completion)
                (first := state)
                (second := current)
                (rest := tail)).trans
                (FrontierPreservation.prepend
                  (head := current)
                  recursive.preservation)
            irreducible :=
              ⟨currentAgainstRetained, recursive.irreducible⟩
            retainedFromSource := fun candidate member => by
              cases member with
              | head =>
                  exact Or.inr List.mem_cons_self
              | tail _ recursiveMember =>
                  cases recursive.retainedFromSource candidate recursiveMember with
                  | inl inserted =>
                      exact Or.inl inserted
                  | inr tailMember =>
                      exact Or.inr (List.mem_cons_of_mem current tailMember) }

/--
An irreducible finite frontier reduction that preserves positive completion
existence in both directions.
-/
structure PreservingIrreducibleFrontierReduction
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (search : RelationSearch Relation)
    (source : List State) where
  retained : List State
  preservation : FrontierPreservation Completion source retained
  irreducible : SearchIrreducible search retained

namespace PreservingIrreducibleFrontierReduction

/-- Width remains derived only after the retained frontier is constructed. -/
def width
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    {search : RelationSearch Relation}
    {source : List State}
    (reduction :
      PreservingIrreducibleFrontierReduction
        (Completion := Completion) search source) : Nat :=
  reduction.retained.length

/-- Positive completion existence is equivalent before and after the reduction. -/
theorem nonempty_iff
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    {search : RelationSearch Relation}
    {source : List State}
    (reduction :
      PreservingIrreducibleFrontierReduction
        (Completion := Completion) search source) :
    Nonempty (FrontierCompletion Completion source) ↔
      Nonempty (FrontierCompletion Completion reduction.retained) :=
  reduction.preservation.nonempty_iff

end PreservingIrreducibleFrontierReduction

/--
Normalize any finite frontier while preserving positive completion existence in
both directions.  This is the preservation-aware counterpart of
`normalizeFrontier`.
-/
def normalizeFrontierPreserving
    {State : Type uState}
    {Relation : State → State → Type uRelation}
    {Completion : State → Type uCompletion}
    (search : RelationSearch Relation)
    (action : RelationalContinuationAction Relation Completion) :
    (source : List State) →
      PreservingIrreducibleFrontierReduction
        (Completion := Completion) search source
  | [] =>
      { retained := []
        preservation := FrontierPreservation.identity []
        irreducible := SearchIrreducible.nil search }
  | state :: tail =>
      let tailReduction := normalizeFrontierPreserving search action tail
      let inserted :=
        insertIntoIrreduciblePreserving
          search action state
          tailReduction.retained
          tailReduction.irreducible
      { retained := inserted.retained
        preservation :=
          (FrontierPreservation.prepend
            (head := state)
            tailReduction.preservation).trans
            inserted.preservation
        irreducible := inserted.irreducible }

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.FrontierPreservation
#print axioms ConstitutiveSearch.FrontierPreservation.identity
#print axioms ConstitutiveSearch.FrontierPreservation.trans
#print axioms ConstitutiveSearch.FrontierPreservation.nonempty_iff
#print axioms ConstitutiveSearch.FrontierPreservation.expandHead
#print axioms ConstitutiveSearch.FrontierPreservation.absorbFirstIntoSecond
#print axioms ConstitutiveSearch.FrontierPreservation.absorbSecondIntoFirst
#print axioms ConstitutiveSearch.PreservingInsertReduction
#print axioms ConstitutiveSearch.insertIntoIrreduciblePreserving
#print axioms ConstitutiveSearch.PreservingIrreducibleFrontierReduction
#print axioms ConstitutiveSearch.PreservingIrreducibleFrontierReduction.nonempty_iff
#print axioms ConstitutiveSearch.normalizeFrontierPreserving
/- AXIOM_AUDIT_END -/
