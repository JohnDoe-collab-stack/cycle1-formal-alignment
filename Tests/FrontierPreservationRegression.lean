import ConstitutiveSearch.FrontierPreservation

namespace ConstitutiveSearch.Tests.FrontierPreservationRegression

inductive State where
  | left
  | right
  deriving DecidableEq

open State

def Completion : State → Type
  | .left => Bool
  | .right => Unit

/-- Every left completion can be absorbed into the right state. -/
def leftToRight :
    ContinuationTransport Completion .left .right :=
  { map := fun _ => () }

/-- The absorption itself preserves positive existence in both directions. -/
def absorption :
    FrontierPreservation Completion [.left, .right] [.right] :=
  FrontierPreservation.absorbFirstIntoSecond leftToRight

theorem absorption_nonempty_iff :
    Nonempty (FrontierCompletion Completion [.left, .right]) ↔
      Nonempty (FrontierCompletion Completion [.right]) :=
  absorption.nonempty_iff

/-- A retained right completion embeds back into the original frontier. -/
def retainedRight :
    FrontierCompletion Completion [.right] :=
  .head ()

def restoredSource :
    FrontierCompletion Completion [.left, .right] :=
  absorption.backward.map retainedRight

example : Nonempty (FrontierCompletion Completion [.left, .right]) :=
  ⟨restoredSource⟩

/-- One proof-relevant relation used by the finite normalizer. -/
inductive Relation : State → State → Type where
  | leftToRight : Relation .left .right

/-- Exhaustive executable relation search. -/
def relationSearch : RelationSearch Relation :=
  { find := fun source target =>
      match source, target with
      | .left, .right => some .leftToRight
      | .left, .left => none
      | .right, .left => none
      | .right, .right => none }

/-- Relation witnesses act on completion spaces. -/
def relationAction :
    RelationalContinuationAction Relation Completion :=
  { act := fun relation completion =>
      match relation with
      | .leftToRight => () }

/-- Preservation-aware normalization absorbs left into right. -/
def normalized :=
  normalizeFrontierPreserving
    relationSearch relationAction [.left, .right]

theorem normalized_retained_exact :
    normalized.retained = [.right] := by
  rfl

theorem normalized_width_one :
    normalized.width = 1 := by
  rfl

theorem normalized_nonempty_iff :
    Nonempty (FrontierCompletion Completion [.left, .right]) ↔
      Nonempty (FrontierCompletion Completion normalized.retained) :=
  normalized.nonempty_iff

/-- The reverse preservation map remains executable after normalization. -/
def normalizedRetainedCompletion :
    FrontierCompletion Completion normalized.retained := by
  rw [normalized_retained_exact]
  exact .head ()

def normalizedRestoredSource :
    FrontierCompletion Completion [.left, .right] :=
  normalized.preservation.backward.map normalizedRetainedCompletion

end ConstitutiveSearch.Tests.FrontierPreservationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.FrontierPreservationRegression.absorption
#print axioms ConstitutiveSearch.Tests.FrontierPreservationRegression.absorption_nonempty_iff
#print axioms ConstitutiveSearch.Tests.FrontierPreservationRegression.restoredSource
#print axioms ConstitutiveSearch.Tests.FrontierPreservationRegression.relationSearch
#print axioms ConstitutiveSearch.Tests.FrontierPreservationRegression.relationAction
#print axioms ConstitutiveSearch.Tests.FrontierPreservationRegression.normalized
#print axioms ConstitutiveSearch.Tests.FrontierPreservationRegression.normalized_nonempty_iff
#print axioms ConstitutiveSearch.Tests.FrontierPreservationRegression.normalizedRestoredSource
/- AXIOM_AUDIT_END -/
