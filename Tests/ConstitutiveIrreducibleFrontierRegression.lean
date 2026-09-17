import ConstitutiveSearch.IrreducibleFrontier

namespace ConstitutiveSearch.Tests.IrreducibleFrontierRegression

inductive State
  | strong
  | weak
  | separate

inductive Relation : State → State → Type
  | strongToWeak : Relation .strong .weak

abbrev Completion (_ : State) := Unit

def action : RelationalContinuationAction Relation Completion :=
  { act := fun _ _ => () }

/-- Exhaustive constructive search for the only relation witness in this test. -/
def findRelation : (source target : State) → Option (Relation source target)
  | .strong, .strong => none
  | .strong, .weak => some .strongToWeak
  | .strong, .separate => none
  | .weak, .strong => none
  | .weak, .weak => none
  | .weak, .separate => none
  | .separate, .strong => none
  | .separate, .weak => none
  | .separate, .separate => none

def search : RelationSearch Relation :=
  { find := findRelation }

/-- The available directional relation reduces the pair to one retained state. -/
def reducedStrongWeak :=
  reducePair search action State.strong State.weak

example : reducedStrongWeak.retained = [State.weak] := rfl

example : reducedStrongWeak.width = 1 := rfl

/-- An unresolved pair remains as a two-state search-relative irreducible frontier. -/
def reducedStrongSeparate :=
  reducePair search action State.strong State.separate

example : reducedStrongSeparate.retained = [State.strong, State.separate] := rfl

example : reducedStrongSeparate.width = 2 := rfl

example : SearchIrreducible search reducedStrongSeparate.retained :=
  reducedStrongSeparate.irreducible

/-- Reduction preserves an actual frontier completion constructively. -/
def strongFrontierCompletion :
    FrontierCompletion Completion [State.strong, State.weak] :=
  .head ()

example :
    FrontierCompletion Completion reducedStrongWeak.retained :=
  reducedStrongWeak.transport.map strongFrontierCompletion

end ConstitutiveSearch.Tests.IrreducibleFrontierRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.IrreducibleFrontierRegression.action
#print axioms ConstitutiveSearch.Tests.IrreducibleFrontierRegression.findRelation
#print axioms ConstitutiveSearch.Tests.IrreducibleFrontierRegression.search
#print axioms ConstitutiveSearch.Tests.IrreducibleFrontierRegression.reducedStrongWeak
#print axioms ConstitutiveSearch.Tests.IrreducibleFrontierRegression.reducedStrongSeparate
/- AXIOM_AUDIT_END -/