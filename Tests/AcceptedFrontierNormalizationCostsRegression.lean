import ConstitutiveSearch.AcceptedFrontierNormalizationCosts

namespace ConstitutiveSearch.Tests.AcceptedFrontierNormalizationCostsRegression

inductive DemoState where
  | a
  | b
  | c
  deriving DecidableEq

open DemoState

abbrev DemoContinuation (_state : DemoState) : Type := Nat

def DemoAccept (_state : DemoState) (value : Nat) : Prop :=
  value = 1

def demoSystem : SearchSystem :=
  { State := DemoState
    Continuation := DemoContinuation
    Accept := DemoAccept }

inductive NoRelation : DemoState → DemoState → Type

def noSearch : RelationSearch NoRelation :=
  { find := fun _ _ => none }

def noAction :
    AcceptedRelationalAction
      demoSystem
      NoRelation :=
  { toTransport := fun witness => nomatch witness }

def frontier : List DemoState := [a, b, c]

theorem retainedWidth3 :
    (normalizeAcceptedFrontier
      noSearch
      noAction
      frontier).retained.length = 3 := by
  rfl

theorem classifications3 :
    normalizationPairClassificationCount
        noSearch
        noAction
        frontier =
      3 := by
  rfl

theorem findCalls3 :
    normalizationFindCallCount
        noSearch
        noAction
        frontier =
      6 := by
  rfl

theorem classifications3_le_quadratic :
    normalizationPairClassificationCount
        noSearch
        noAction
        frontier ≤
      normalizationPairClassificationQuadraticBudget
        frontier.length :=
  normalizationPairClassificationCount_le_quadratic
    noSearch
    noAction
    frontier

theorem findCalls3_le_quadratic :
    normalizationFindCallCount
        noSearch
        noAction
        frontier ≤
      normalizationFindCallQuadraticBudget
        frontier.length :=
  normalizationFindCallCount_le_quadratic
    noSearch
    noAction
    frontier

end ConstitutiveSearch.Tests.AcceptedFrontierNormalizationCostsRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierNormalizationCostsRegression.retainedWidth3
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierNormalizationCostsRegression.classifications3
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierNormalizationCostsRegression.findCalls3
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierNormalizationCostsRegression.classifications3_le_quadratic
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierNormalizationCostsRegression.findCalls3_le_quadratic
/- AXIOM_AUDIT_END -/
