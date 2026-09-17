import ConstitutiveSearch.FiniteFrontierNormalization

namespace ConstitutiveSearch.Tests.FiniteFrontierNormalizationRegression

inductive DemoState where
  | a
  | b
  | c
  deriving DecidableEq

open DemoState

/-- Two positive structural absorptions, both ending at `c`. -/
inductive DemoRelation : DemoState → DemoState → Type where
  | aToC : DemoRelation .a .c
  | bToC : DemoRelation .b .c

abbrev DemoCompletion (_state : DemoState) : Type := Nat

/-- The relation action preserves the completion payload. -/
def demoAction :
    RelationalContinuationAction DemoRelation DemoCompletion :=
  { act := fun _relation completion => completion }

/--
Exhaustive executable search for exactly the two declared structural relations.
Writing the dependent cases as equations keeps the regression axiom-free.
-/
def findDemoRelation :
    (source target : DemoState) → Option (DemoRelation source target)
  | .a, .a => none
  | .a, .b => none
  | .a, .c => some .aToC
  | .b, .a => none
  | .b, .b => none
  | .b, .c => some .bToC
  | .c, .a => none
  | .c, .b => none
  | .c, .c => none

/-- Executable search exposing the exhaustive relation finder. -/
def demoSearch : RelationSearch DemoRelation :=
  { find := findDemoRelation }

/-- Three states normalize constructively to the single absorbing state `c`. -/
def normalizedABC :=
  normalizeFrontier demoSearch demoAction [a, b, c]

theorem normalizedABC_retained :
    normalizedABC.retained = [c] := by
  rfl

theorem normalizedABC_width :
    normalizedABC.width = 1 := by
  rfl

/-- An unresolved pair is retained rather than silently classified impossible. -/
def normalizedAB :=
  normalizeFrontier demoSearch demoAction [a, b]

theorem normalizedAB_width :
    normalizedAB.width = 2 := by
  rfl

/-- A concrete completion survives the complete three-state normalization. -/
def sourceCompletion :
    FrontierCompletion DemoCompletion [a, b, c] :=
  .head 17

def retainedCompletion :
    FrontierCompletion DemoCompletion normalizedABC.retained :=
  normalizedABC.transport.map sourceCompletion

example : Nonempty (FrontierCompletion DemoCompletion normalizedABC.retained) :=
  ⟨retainedCompletion⟩

end ConstitutiveSearch.Tests.FiniteFrontierNormalizationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.FiniteFrontierNormalizationRegression.DemoRelation
#print axioms ConstitutiveSearch.Tests.FiniteFrontierNormalizationRegression.demoAction
#print axioms ConstitutiveSearch.Tests.FiniteFrontierNormalizationRegression.findDemoRelation
#print axioms ConstitutiveSearch.Tests.FiniteFrontierNormalizationRegression.demoSearch
#print axioms ConstitutiveSearch.Tests.FiniteFrontierNormalizationRegression.normalizedABC
#print axioms ConstitutiveSearch.Tests.FiniteFrontierNormalizationRegression.normalizedABC_retained
#print axioms ConstitutiveSearch.Tests.FiniteFrontierNormalizationRegression.normalizedABC_width
#print axioms ConstitutiveSearch.Tests.FiniteFrontierNormalizationRegression.normalizedAB_width
#print axioms ConstitutiveSearch.Tests.FiniteFrontierNormalizationRegression.retainedCompletion
/- AXIOM_AUDIT_END -/
