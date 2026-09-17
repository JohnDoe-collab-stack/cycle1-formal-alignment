import ConstitutiveSearch.RelationalTransport

namespace ConstitutiveSearch.Tests.RelationalTransportRegression

open ConstitutiveSearch

inductive State
  | strong
  | weak
  | isolated

inductive Relation : State → State → Type
  | dropConstraint : Relation .strong .weak

def Completion : State → Type
  | .strong => Bool
  | .weak => Unit
  | .isolated => Unit

def action : RelationalContinuationAction Relation Completion :=
  { act := by
      intro source target witness completion
      cases witness
      exact () }

def search : RelationSearch Relation :=
  { find := fun source target =>
      match source, target with
      | .strong, .weak => some Relation.dropConstraint
      | _, _ => none }

/-- The executable search finds only the structurally justified direction. -/
theorem strongWeak_kind :
    (search.classifyPair State.strong State.weak).kind =
      PairSearchResult.Kind.forwardOnly := by
  rfl

/-- Reversing the query exposes the same witness as a backward-only result. -/
theorem weakStrong_kind :
    (search.classifyPair State.weak State.strong).kind =
      PairSearchResult.Kind.backwardOnly := by
  rfl

/-- An unrelated pair remains unresolved instead of being refuted. -/
theorem weakIsolated_kind :
    (search.classifyPair State.weak State.isolated).kind =
      PairSearchResult.Kind.unresolved := by
  rfl

/-- A successful structural witness produces an actual continuation transport. -/
def strongToWeakTransport :
    ContinuationTransport Completion State.strong State.weak :=
  action.toTransport Relation.dropConstraint

theorem strongToWeak_false :
    strongToWeakTransport.map false = () := by
  rfl

theorem strongToWeak_true :
    strongToWeakTransport.map true = () := by
  rfl

/-- The executable transport search succeeds exactly on the supported pair. -/
theorem findTransport_strongWeak_succeeds :
    search.findTransport action State.strong State.weak ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

/-- Search failure remains an `Option.none`, with no negative theorem attached. -/
theorem findTransport_weakIsolated_unresolved :
    search.findTransport action State.weak State.isolated = none := by
  rfl

end ConstitutiveSearch.Tests.RelationalTransportRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.RelationalTransportRegression.action
#print axioms ConstitutiveSearch.Tests.RelationalTransportRegression.search
#print axioms ConstitutiveSearch.Tests.RelationalTransportRegression.strongWeak_kind
#print axioms ConstitutiveSearch.Tests.RelationalTransportRegression.strongToWeakTransport
#print axioms ConstitutiveSearch.Tests.RelationalTransportRegression.findTransport_strongWeak_succeeds
/- AXIOM_AUDIT_END -/