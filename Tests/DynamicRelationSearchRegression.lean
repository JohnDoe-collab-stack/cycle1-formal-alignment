import ConstitutiveSearch.DynamicRelationSearch

namespace ConstitutiveSearch.Tests.DynamicRelationSearchRegression

inductive DemoState where
  | left
  | right
  deriving DecidableEq

open DemoState

abbrev DemoContinuation (_state : DemoState) : Type := Nat

/-- Both states accept exactly the same distinguished structural continuation. -/
def DemoAccept : DemoState → Nat → Prop
  | .left, value => value = 1
  | .right, value => value = 1

def demoSystem : SearchSystem :=
  { State := DemoState
    Continuation := DemoContinuation
    Accept := DemoAccept }

/--
The two constitutive states have exactly the same search frontier.  They differ
only by whether one structural anchor has been constituted.
-/
def beforeAnchor : ConstitutiveState demoSystem Bool :=
  { frontier := [left, right]
    constitution := false }

def afterAnchor : ConstitutiveState demoSystem Bool :=
  { frontier := [left, right]
    constitution := true }

theorem frontier_unchanged :
    beforeAnchor.frontier = afterAnchor.frontier := by
  rfl

/-- The path can constitute the anchor without changing the frontier. -/
inductive AnchorConstitutes : Bool → Bool → Type where
  | acquire : AnchorConstitutes false true

def acquireAnchor :
    ConstitutiveStep
      demoSystem
      AnchorConstitutes
      beforeAnchor
      afterAnchor :=
  { preservation :=
      AcceptedFrontierPreservation.identity
        demoSystem
        [left, right]
    constitutes := .acquire }

/--
A relation witness is available only in a current state whose constitution
contains the anchor, and only in the left-to-right direction.
-/
structure AnchoredRelation
    (current : ConstitutiveState demoSystem Bool)
    (source target : DemoState) : Type where
  anchor : current.constitution = true
  sourceExact : source = left
  targetExact : target = right

/-- An anchored relation acts on every structural continuation by identity. -/
def anchoredAction :
    ConstitutiveRelationalAction
      demoSystem
      Bool
      AnchoredRelation :=
  { toTransport := fun relation => by
      cases relation.sourceExact
      cases relation.targetExact
      exact
        { map := fun value => value
          preservesAccept := by
            intro value accepted
            exact accepted } }

/--
Executable reconstruction.  The exact same pair of search states is unresolved
before the anchor is constituted and becomes related afterwards.
-/
def findAnchoredRelation :
    (current : ConstitutiveState demoSystem Bool) →
      (source target : DemoState) →
        Option (AnchoredRelation current source target)
  | current, .left, .right =>
      if anchor : current.constitution = true then
        some
          { anchor := anchor
            sourceExact := rfl
            targetExact := rfl }
      else
        none
  | _current, .left, .left => none
  | _current, .right, .left => none
  | _current, .right, .right => none

def anchoredSearch :
    ConstitutiveRelationSearch
      demoSystem
      Bool
      AnchoredRelation :=
  { find := findAnchoredRelation }

/-- Before constitution, the relation is not reconstructible. -/
theorem relation_absent_before :
    anchoredSearch.find
        beforeAnchor
        left
        right = none := by
  rfl

/-- After constitution, the same pair produces a positive relation witness. -/
theorem relation_present_after :
    anchoredSearch.find
        afterAnchor
        left
        right ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

/-- The reverse relation remains absent even after constitution. -/
theorem reverse_still_absent_after :
    anchoredSearch.find
        afterAnchor
        right
        left = none := by
  rfl

def beforeReduction :=
  anchoredSearch.normalizeAt
    anchoredAction
    beforeAnchor
    beforeAnchor.frontier

def afterReduction :=
  anchoredSearch.normalizeAt
    anchoredAction
    afterAnchor
    afterAnchor.frontier

/-- With no anchor, the unchanged two-state frontier is irreducible for this engine. -/
theorem width_before :
    beforeReduction.width = 2 := by
  rfl

/-- Once the path constitutes the anchor, the same frontier reduces to one state. -/
theorem width_after :
    afterReduction.width = 1 := by
  rfl

theorem retained_after :
    afterReduction.retained = [right] := by
  rfl

/-- A concrete accepted structural continuation witnesses viability before constitution. -/
def acceptedLeft : demoSystem.Continuation left := by
  change Nat
  exact 1

theorem acceptedLeft_accept :
    demoSystem.Accept left acceptedLeft := by
  rfl

theorem viable_before :
    FrontierViable demoSystem beforeAnchor.frontier := by
  exact ⟨.head acceptedLeft, acceptedLeft_accept⟩

/-- Constituting the anchor itself preserves the semantic search question. -/
theorem anchor_step_viable_iff :
    FrontierViable demoSystem beforeAnchor.frontier ↔
      FrontierViable demoSystem afterAnchor.frontier :=
  acquireAnchor.viable_iff

/-- The new reduction still preserves viability after the relation becomes available. -/
theorem reduced_after_viable :
    FrontierViable demoSystem afterReduction.retained :=
  afterReduction.viable_iff.mp
    (anchor_step_viable_iff.mp viable_before)

end ConstitutiveSearch.Tests.DynamicRelationSearchRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.DynamicRelationSearchRegression.beforeAnchor
#print axioms ConstitutiveSearch.Tests.DynamicRelationSearchRegression.afterAnchor
#print axioms ConstitutiveSearch.Tests.DynamicRelationSearchRegression.frontier_unchanged
#print axioms ConstitutiveSearch.Tests.DynamicRelationSearchRegression.AnchorConstitutes
#print axioms ConstitutiveSearch.Tests.DynamicRelationSearchRegression.acquireAnchor
#print axioms ConstitutiveSearch.Tests.DynamicRelationSearchRegression.AnchoredRelation
#print axioms ConstitutiveSearch.Tests.DynamicRelationSearchRegression.anchoredAction
#print axioms ConstitutiveSearch.Tests.DynamicRelationSearchRegression.anchoredSearch
#print axioms ConstitutiveSearch.Tests.DynamicRelationSearchRegression.relation_absent_before
#print axioms ConstitutiveSearch.Tests.DynamicRelationSearchRegression.relation_present_after
#print axioms ConstitutiveSearch.Tests.DynamicRelationSearchRegression.reverse_still_absent_after
#print axioms ConstitutiveSearch.Tests.DynamicRelationSearchRegression.beforeReduction
#print axioms ConstitutiveSearch.Tests.DynamicRelationSearchRegression.afterReduction
#print axioms ConstitutiveSearch.Tests.DynamicRelationSearchRegression.width_before
#print axioms ConstitutiveSearch.Tests.DynamicRelationSearchRegression.width_after
#print axioms ConstitutiveSearch.Tests.DynamicRelationSearchRegression.retained_after
#print axioms ConstitutiveSearch.Tests.DynamicRelationSearchRegression.anchor_step_viable_iff
#print axioms ConstitutiveSearch.Tests.DynamicRelationSearchRegression.reduced_after_viable
/- AXIOM_AUDIT_END -/
