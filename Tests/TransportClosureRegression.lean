import ConstitutiveSearch.TransportClosure

namespace ConstitutiveSearch.Tests.TransportClosureRegression

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

/-- Primitive structural relations deliberately omit a direct a-to-c witness. -/
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

theorem direct_a_c_absent :
    primitiveSearch.find a c = none := by
  rfl

/-- The direct engine therefore keeps the pair a,c unresolved. -/
def directReduction :=
  normalizeAcceptedFrontier
    primitiveSearch
    primitiveAction
    [a, c]

theorem direct_width_two :
    directReduction.width = 2 := by
  rfl

/-- Explicit compositional certificate through the intermediate state b. -/
def aToCCode :
    TransportClosure PrimitiveRelation a c :=
  TransportClosure.compose
    (TransportClosure.ofGenerator PrimitiveRelation.aToB)
    (TransportClosure.ofGenerator PrimitiveRelation.bToC)

theorem aToCCode_size :
    aToCCode.size = 2 := by
  rfl

/--
Executable closure search used by this separator.  It exposes the explicit
two-atom code for a-to-c; it is not claimed to be an exhaustive generic closure
algorithm.
-/
def findClosure :
    (source target : DemoState) →
      Option (TransportClosure PrimitiveRelation source target)
  | .a, .a => none
  | .a, .b =>
      some
        (TransportClosure.ofGenerator
          PrimitiveRelation.aToB)
  | .a, .c =>
      some aToCCode
  | .b, .a => none
  | .b, .b => none
  | .b, .c =>
      some
        (TransportClosure.ofGenerator
          PrimitiveRelation.bToC)
  | .c, .a => none
  | .c, .b => none
  | .c, .c => none

def closureSearch :
    RelationSearch (TransportClosure PrimitiveRelation) :=
  { find := findClosure }

theorem closure_a_c_present :
    closureSearch.find a c ≠ none := by
  intro impossible
  change some aToCCode = none at impossible
  cases impossible

def closureReduction :=
  normalizeWithTransportClosure
    primitiveAction
    closureSearch
    [a, c]

theorem closure_width_one :
    closureReduction.width = 1 := by
  rfl

theorem closure_retained_c :
    closureReduction.retained = [c] := by
  rfl

/-- The composed code is still a total acceptance-preserving transport. -/
def acceptedA : demoSystem.Continuation a := by
  change Nat
  exact 1

theorem acceptedA_accept :
    demoSystem.Accept a acceptedA := by
  rfl

theorem composed_preserves_viable :
    demoSystem.Viable a → demoSystem.Viable c :=
  aToCCode.preservesViable primitiveAction

end ConstitutiveSearch.Tests.TransportClosureRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.TransportClosureRegression.PrimitiveRelation
#print axioms ConstitutiveSearch.Tests.TransportClosureRegression.primitiveAction
#print axioms ConstitutiveSearch.Tests.TransportClosureRegression.primitiveSearch
#print axioms ConstitutiveSearch.Tests.TransportClosureRegression.direct_a_c_absent
#print axioms ConstitutiveSearch.Tests.TransportClosureRegression.directReduction
#print axioms ConstitutiveSearch.Tests.TransportClosureRegression.direct_width_two
#print axioms ConstitutiveSearch.Tests.TransportClosureRegression.aToCCode
#print axioms ConstitutiveSearch.Tests.TransportClosureRegression.aToCCode_size
#print axioms ConstitutiveSearch.Tests.TransportClosureRegression.closureSearch
#print axioms ConstitutiveSearch.Tests.TransportClosureRegression.closure_a_c_present
#print axioms ConstitutiveSearch.Tests.TransportClosureRegression.closureReduction
#print axioms ConstitutiveSearch.Tests.TransportClosureRegression.closure_width_one
#print axioms ConstitutiveSearch.Tests.TransportClosureRegression.closure_retained_c
#print axioms ConstitutiveSearch.Tests.TransportClosureRegression.composed_preserves_viable
/- AXIOM_AUDIT_END -/
