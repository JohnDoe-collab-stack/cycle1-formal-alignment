import ConstitutiveSearch.ClosureSearch

namespace ConstitutiveSearch.Tests.ClosureSearchRegression

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

inductive PrimitiveRelation : DemoState → DemoState → Type where
  | aToB : PrimitiveRelation a b
  | bToC : PrimitiveRelation b c

def primitiveAction :
    AcceptedRelationalAction
      demoSystem
      PrimitiveRelation :=
  { toTransport := fun witness =>
      match witness with
      | .aToB =>
          { map := fun value => value
            preservesAccept := fun _ accepted => accepted }
      | .bToC =>
          { map := fun value => value
            preservesAccept := fun _ accepted => accepted } }

def findPrimitive :
    (source target : DemoState) →
      Option (PrimitiveRelation source target)
  | .a, .a => none
  | .a, .b => some .aToB
  | .a, .c => none
  | .b, .a => none
  | .b, .b => none
  | .b, .c => some .bToC
  | .c, .a => none
  | .c, .b => none
  | .c, .c => none

def primitiveSearch : RelationSearch PrimitiveRelation :=
  { find := findPrimitive }

def fuelOne :=
  searchTransportClosureBounded
    primitiveSearch
    [b]
    1
    a
    c

theorem fuelOne_not_found :
    fuelOne.code? = none := by
  rfl

theorem fuelOne_primitive_queries :
    fuelOne.stats.primitiveQueries = 1 := by
  rfl

theorem fuelOne_candidates :
    fuelOne.stats.compositionCandidates = 1 := by
  rfl

def fuelTwo :=
  searchTransportClosureBounded
    primitiveSearch
    [b]
    2
    a
    c

theorem fuelTwo_found :
    fuelTwo.code? ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

theorem fuelTwo_code_size :
    match fuelTwo.code? with
    | some code => code.size = 2
    | none => False := by
  rfl

theorem fuelTwo_primitive_queries :
    fuelTwo.stats.primitiveQueries = 3 := by
  rfl

theorem fuelTwo_candidates :
    fuelTwo.stats.compositionCandidates = 1 := by
  rfl

def boundedSearch :
    RelationSearch (TransportClosure PrimitiveRelation) :=
  boundedTransportClosureSearch
    primitiveSearch
    [b]
    2

theorem boundedSearch_a_c_present :
    boundedSearch.find a c ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

def boundedReduction :=
  normalizeWithTransportClosure
    primitiveAction
    boundedSearch
    [a, c]

theorem boundedReduction_width_one :
    boundedReduction.width = 1 := by
  rfl

theorem boundedReduction_retained_c :
    boundedReduction.retained = [c] := by
  rfl

end ConstitutiveSearch.Tests.ClosureSearchRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ClosureSearchRegression.PrimitiveRelation
#print axioms ConstitutiveSearch.Tests.ClosureSearchRegression.primitiveAction
#print axioms ConstitutiveSearch.Tests.ClosureSearchRegression.primitiveSearch
#print axioms ConstitutiveSearch.Tests.ClosureSearchRegression.fuelOne
#print axioms ConstitutiveSearch.Tests.ClosureSearchRegression.fuelOne_not_found
#print axioms ConstitutiveSearch.Tests.ClosureSearchRegression.fuelTwo
#print axioms ConstitutiveSearch.Tests.ClosureSearchRegression.fuelTwo_found
#print axioms ConstitutiveSearch.Tests.ClosureSearchRegression.fuelTwo_code_size
#print axioms ConstitutiveSearch.Tests.ClosureSearchRegression.fuelTwo_primitive_queries
#print axioms ConstitutiveSearch.Tests.ClosureSearchRegression.fuelTwo_candidates
#print axioms ConstitutiveSearch.Tests.ClosureSearchRegression.boundedSearch
#print axioms ConstitutiveSearch.Tests.ClosureSearchRegression.boundedSearch_a_c_present
#print axioms ConstitutiveSearch.Tests.ClosureSearchRegression.boundedReduction
#print axioms ConstitutiveSearch.Tests.ClosureSearchRegression.boundedReduction_width_one
#print axioms ConstitutiveSearch.Tests.ClosureSearchRegression.boundedReduction_retained_c
/- AXIOM_AUDIT_END -/
