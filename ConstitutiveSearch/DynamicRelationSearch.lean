import ConstitutiveSearch.FrontierTrajectory
import ConstitutiveSearch.AcceptedFrontierNormalization

/-!
# Relation search indexed by constituted state

This module makes relation availability depend on the current constitutive
state itself.

The search space is therefore not modelled as one fixed relation graph explored
for longer. A change in the constituted state may change which relation type
is inhabited and which witnesses the executable search can reconstruct.
-/

namespace ConstitutiveSearch

universe uConstitution uRelation

/--
Positive action of relations whose witness type depends on the whole current
constitutive state.
-/
structure ConstitutiveRelationalAction
    (system : SearchSystem)
    (Constitution : Type uConstitution)
    (Relation :
      ConstitutiveState system Constitution →
        system.State → system.State → Type uRelation) where
  toTransport :
    {current : ConstitutiveState system Constitution} →
      {source target : system.State} →
        Relation current source target →
          AcceptingContinuationTransport system source target

/--
Executable relation reconstruction at one current constituted state.

The relation family itself is indexed by the current state, so changing
constitution can change the available witness space without changing the
compared states.
-/
structure ConstitutiveRelationSearch
    (system : SearchSystem)
    (Constitution : Type uConstitution)
    (Relation :
      ConstitutiveState system Constitution →
        system.State → system.State → Type uRelation) where
  find :
    (current : ConstitutiveState system Constitution) →
      (source target : system.State) →
        Option (Relation current source target)

namespace ConstitutiveRelationalAction

/-- Freeze a dynamic action at one current constituted state. -/
def freeze
    {system : SearchSystem}
    {Constitution : Type uConstitution}
    {Relation :
      ConstitutiveState system Constitution →
        system.State → system.State → Type uRelation}
    (action :
      ConstitutiveRelationalAction
        system
        Constitution
        Relation)
    (current : ConstitutiveState system Constitution) :
    AcceptedRelationalAction
      system
      (Relation current) :=
  { toTransport := fun witness =>
      action.toTransport witness }

end ConstitutiveRelationalAction

namespace ConstitutiveRelationSearch

/-- Freeze dynamic relation search at one constituted state. -/
def freeze
    {system : SearchSystem}
    {Constitution : Type uConstitution}
    {Relation :
      ConstitutiveState system Constitution →
        system.State → system.State → Type uRelation}
    (search :
      ConstitutiveRelationSearch
        system
        Constitution
        Relation)
    (current : ConstitutiveState system Constitution) :
    RelationSearch (Relation current) :=
  { find := fun source target =>
      search.find current source target }

/--
Search one accepted transport using exactly the information currently
constituted.
-/
def findAcceptedTransport
    {system : SearchSystem}
    {Constitution : Type uConstitution}
    {Relation :
      ConstitutiveState system Constitution →
        system.State → system.State → Type uRelation}
    (search :
      ConstitutiveRelationSearch
        system
        Constitution
        Relation)
    (action :
      ConstitutiveRelationalAction
        system
        Constitution
        Relation)
    (current : ConstitutiveState system Constitution)
    (source target : system.State) :
    Option (AcceptingContinuationTransport system source target) :=
  (search.freeze current).findAcceptedTransport
    (action.freeze current)
    source
    target

/--
Normalize the same frontier relative to the relations reconstructible at one
specific constituted state.
-/
def normalizeAt
    {system : SearchSystem}
    {Constitution : Type uConstitution}
    {Relation :
      ConstitutiveState system Constitution →
        system.State → system.State → Type uRelation}
    (search :
      ConstitutiveRelationSearch
        system
        Constitution
        Relation)
    (action :
      ConstitutiveRelationalAction
        system
        Constitution
        Relation)
    (current : ConstitutiveState system Constitution)
    (frontier : List system.State) :
    AcceptedIrreducibleFrontierReduction
      (search.freeze current)
      frontier :=
  normalizeAcceptedFrontier
    (search.freeze current)
    (action.freeze current)
    frontier

end ConstitutiveRelationSearch

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.ConstitutiveRelationalAction
#print axioms ConstitutiveSearch.ConstitutiveRelationSearch
#print axioms ConstitutiveSearch.ConstitutiveRelationalAction.freeze
#print axioms ConstitutiveSearch.ConstitutiveRelationSearch.freeze
#print axioms ConstitutiveSearch.ConstitutiveRelationSearch.findAcceptedTransport
#print axioms ConstitutiveSearch.ConstitutiveRelationSearch.normalizeAt
/- AXIOM_AUDIT_END -/
