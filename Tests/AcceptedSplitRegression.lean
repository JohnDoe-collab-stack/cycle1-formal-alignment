import ConstitutiveSearch.AcceptedFrontierPreservation

namespace ConstitutiveSearch.Tests.AcceptedSplitRegression

open ConstitutiveSearch

inductive SplitState where
  | parent
  | left
  | right

def continuation : SplitState → Type
  | .parent => Bool
  | .left => Unit
  | .right => Unit

def accept :
    (state : SplitState) →
      continuation state →
        Prop
  | .parent, value => value = true
  | .left, _ => False
  | .right, _ => True

def system : SearchSystem :=
  { State := SplitState
    Continuation := continuation
    Accept := accept }

def splitter :
    AcceptingExactBinarySplit
      system
      SplitState.parent
      SplitState.left
      SplitState.right :=
  { split := fun value =>
      match value with
      | false => .inl ()
      | true => .inr ()
    merge := fun branch =>
      match branch with
      | .inl _ => false
      | .inr _ => true
    splitMerge := by
      intro branch
      cases branch <;> rfl
    mergeSplit := by
      intro value
      cases value <;> rfl
    splitPreservesAccept := by
      intro value accepted
      cases value with
      | false =>
          cases accepted
      | true =>
          exact True.intro
    mergePreservesAccept := by
      intro branch accepted
      cases branch with
      | inl _ =>
          exact False.elim accepted
      | inr _ =>
          rfl }

/-- The parent is viable through its true structural continuation. -/
theorem parent_viable :
    system.Viable SplitState.parent :=
  ⟨true, rfl⟩

/-- The left branch is structurally inhabited but semantically non-viable. -/
theorem left_not_viable :
    ¬ system.Viable SplitState.left := by
  intro viable
  rcases viable with ⟨_continuation, impossible⟩
  exact impossible

/-- The right branch is viable. -/
theorem right_viable :
    system.Viable SplitState.right :=
  ⟨(), True.intro⟩

/-- Exact structural splitting recovers the semantic OR law for viability. -/
theorem parent_viable_iff_branches :
    system.Viable SplitState.parent ↔
      system.Viable SplitState.left ∨
        system.Viable SplitState.right :=
  splitter.viable_iff

def expansion :
    AcceptedFrontierPreservation
      system
      [SplitState.parent]
      [SplitState.left, SplitState.right] :=
  AcceptedFrontierPreservation.expandHead splitter

/-- Frontier expansion preserves viability without embedding acceptance in the carrier. -/
theorem expansion_viable_iff :
    FrontierViable system [SplitState.parent] ↔
      FrontierViable system [SplitState.left, SplitState.right] :=
  expansion.viable_iff

/-- Accepted parent continuation transported to the correct right branch. -/
def parentAccepted :
    system.frontierSystem.AcceptedContinuation [SplitState.parent] :=
  ⟨.head true, rfl⟩

def expandedAccepted :
    system.frontierSystem.AcceptedContinuation
      [SplitState.left, SplitState.right] :=
  expansion.forward.toAcceptedTransport.map parentAccepted

end ConstitutiveSearch.Tests.AcceptedSplitRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.AcceptedSplitRegression.splitter
#print axioms ConstitutiveSearch.Tests.AcceptedSplitRegression.parent_viable
#print axioms ConstitutiveSearch.Tests.AcceptedSplitRegression.left_not_viable
#print axioms ConstitutiveSearch.Tests.AcceptedSplitRegression.right_viable
#print axioms ConstitutiveSearch.Tests.AcceptedSplitRegression.parent_viable_iff_branches
#print axioms ConstitutiveSearch.Tests.AcceptedSplitRegression.expansion
#print axioms ConstitutiveSearch.Tests.AcceptedSplitRegression.expansion_viable_iff
#print axioms ConstitutiveSearch.Tests.AcceptedSplitRegression.expandedAccepted
/- AXIOM_AUDIT_END -/
