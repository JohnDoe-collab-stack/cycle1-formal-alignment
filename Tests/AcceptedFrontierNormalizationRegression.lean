import ConstitutiveSearch.AcceptedFrontierNormalization

namespace ConstitutiveSearch.Tests.AcceptedFrontierNormalizationRegression

inductive DemoState where
  | a
  | b
  | c
  deriving DecidableEq

open DemoState

/-- Structural continuations are all natural numbers. -/
abbrev DemoContinuation (_state : DemoState) : Type := Nat

/-- Acceptance differs by state and is not stored in the continuation type. -/
def DemoAccept : DemoState → Nat → Prop
  | .a, value => value = 1
  | .b, value => value = 2
  | .c, value => value = 1 ∨ value = 2

def demoSystem : SearchSystem :=
  { State := DemoState
    Continuation := DemoContinuation
    Accept := DemoAccept }

/-- Two positive relations merge the accepted content of a and b into c. -/
inductive DemoRelation : DemoState → DemoState → Type where
  | aToC : DemoRelation .a .c
  | bToC : DemoRelation .b .c

/-- Each witness acts on every structural continuation by identity. -/
def demoAction :
    AcceptedRelationalAction demoSystem DemoRelation :=
  { toTransport := fun witness =>
      match witness with
      | .aToC =>
          { map := fun value => value
            preservesAccept := by
              intro value accepted
              exact Or.inl accepted }
      | .bToC =>
          { map := fun value => value
            preservesAccept := by
              intro value accepted
              exact Or.inr accepted } }

/-- Exhaustive executable search for exactly the declared relations. -/
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

def demoSearch : RelationSearch DemoRelation :=
  { find := findDemoRelation }

/-- Automatic hardened normalization absorbs a and b into c. -/
def normalizedABC :=
  normalizeAcceptedFrontier
    demoSearch
    demoAction
    [a, b, c]

theorem normalizedABC_retained :
    normalizedABC.retained = [c] := by
  rfl

theorem normalizedABC_width :
    normalizedABC.width = 1 := by
  rfl

/-- Search failure retains an unresolved pair. -/
def normalizedAB :=
  normalizeAcceptedFrontier
    demoSearch
    demoAction
    [a, b]

theorem normalizedAB_width :
    normalizedAB.width = 2 := by
  rfl

/-- The source frontier is viable through state a. -/
theorem source_viable :
    FrontierViable demoSystem [a, b, c] := by
  exact ⟨.head 1, rfl⟩

/-- Complete automatic normalization preserves viability in both directions. -/
theorem normalizedABC_viable_iff :
    FrontierViable demoSystem [a, b, c] ↔
      FrontierViable demoSystem normalizedABC.retained :=
  normalizedABC.viable_iff

theorem retained_viable :
    FrontierViable demoSystem normalizedABC.retained :=
  normalizedABC_viable_iff.mp source_viable

/--
Rejected continuations remain structural inputs to the automatic normalizer.
They are not upgraded into accepted witnesses by transport.
-/
def rejectedSource :
    FrontierContinuation demoSystem [a, b, c] :=
  .head 99

def rejectedRetained :
    FrontierContinuation demoSystem normalizedABC.retained :=
  normalizedABC.preservation.forward.map rejectedSource

theorem rejectedRetained_not_accepted :
    ¬ FrontierAccept
        demoSystem
        normalizedABC.retained
        rejectedRetained := by
  change ¬ (99 = 1 ∨ 99 = 2)
  decide

end ConstitutiveSearch.Tests.AcceptedFrontierNormalizationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierNormalizationRegression.demoAction
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierNormalizationRegression.demoSearch
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierNormalizationRegression.normalizedABC
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierNormalizationRegression.normalizedABC_retained
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierNormalizationRegression.normalizedABC_width
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierNormalizationRegression.normalizedAB_width
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierNormalizationRegression.source_viable
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierNormalizationRegression.normalizedABC_viable_iff
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierNormalizationRegression.retained_viable
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierNormalizationRegression.rejectedRetained
#print axioms ConstitutiveSearch.Tests.AcceptedFrontierNormalizationRegression.rejectedRetained_not_accepted
/- AXIOM_AUDIT_END -/
