import ConstitutiveSearch.ConstitutiveWidth

namespace ConstitutiveSearch.Tests.ConstitutiveWidthRegression

inductive State
  | strong
  | weak
  | separate

inductive Relation : State → State → Type
  | strongToWeak : Relation .strong .weak

abbrev Completion (_ : State) := Unit

def action : RelationalContinuationAction Relation Completion :=
  { act := fun _ _ => () }

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

/-- Pair reduction is lifted without changing its width. -/
def pairReduction :=
  reducePair search action State.strong State.weak

def generalReduction :
    IrreducibleFrontierReduction
      (Completion := Completion)
      search
      [State.strong, State.weak] :=
  IrreducibleFrontierReduction.ofPair pairReduction

theorem general_width_one : generalReduction.width = 1 := by
  rfl

/-- An already irreducible unresolved pair keeps width two. -/
def unresolvedPair :=
  reducePair search action State.strong State.separate

def unresolvedGeneral :
    IrreducibleFrontierReduction
      (Completion := Completion)
      search
      [State.strong, State.separate] :=
  IrreducibleFrontierReduction.ofPair unresolvedPair

theorem unresolved_width_two : unresolvedGeneral.width = 2 := by
  rfl

/-- Width is derived after the reduction while source completion existence is preserved. -/
def sourceCompletion :
    FrontierCompletion Completion [State.strong, State.weak] :=
  .head ()

def retainedCompletion :
    FrontierCompletion Completion generalReduction.retained :=
  generalReduction.mapCompletion sourceCompletion

theorem retained_nonempty :
    Nonempty (FrontierCompletion Completion generalReduction.retained) :=
  ⟨retainedCompletion⟩

end ConstitutiveSearch.Tests.ConstitutiveWidthRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ConstitutiveWidthRegression.action
#print axioms ConstitutiveSearch.Tests.ConstitutiveWidthRegression.findRelation
#print axioms ConstitutiveSearch.Tests.ConstitutiveWidthRegression.generalReduction
#print axioms ConstitutiveSearch.Tests.ConstitutiveWidthRegression.general_width_one
#print axioms ConstitutiveSearch.Tests.ConstitutiveWidthRegression.unresolvedGeneral
#print axioms ConstitutiveSearch.Tests.ConstitutiveWidthRegression.unresolved_width_two
#print axioms ConstitutiveSearch.Tests.ConstitutiveWidthRegression.retained_nonempty
/- AXIOM_AUDIT_END -/