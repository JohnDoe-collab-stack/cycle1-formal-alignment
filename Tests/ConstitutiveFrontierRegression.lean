import ConstitutiveSearch.FrontierReduction

namespace ConstitutiveSearch.Tests.FrontierReductionRegression

open ConstitutiveSearch

inductive State
  | parent
  | left
  | right
  | rest

def Completion : State → Type
  | .parent => Bool
  | .left => Unit
  | .right => Unit
  | .rest => Unit

def split :
    ExactBinarySplit Completion State.parent State.left State.right :=
  { split := fun completion =>
      match completion with
      | false => .inl ()
      | true => .inr ()
    merge := fun branch =>
      match branch with
      | .inl _ => false
      | .inr _ => true
    splitMerge := by
      intro branch
      cases branch with
      | inl completion =>
          cases completion
          rfl
      | inr completion =>
          cases completion
          rfl
    mergeSplit := by
      intro completion
      cases completion <;> rfl }

def leftToRight :
    ContinuationTransport Completion State.left State.right :=
  { map := fun _ => () }

def rightToLeft :
    ContinuationTransport Completion State.right State.left :=
  { map := fun _ => () }

def parentLeftCompletion :
    FrontierCompletion Completion [State.parent] :=
  .head false

def parentRightCompletion :
    FrontierCompletion Completion [State.parent] :=
  .head true

/-- A parent completion entering the left successor survives left absorption. -/
theorem leftBranch_survivesAbsorption :
    (FrontierCompletion.expandThenAbsorbLeft split leftToRight).map
        parentLeftCompletion =
      (FrontierCompletion.head () :
        FrontierCompletion Completion [State.right]) := by
  rfl

/-- A parent completion already entering the retained successor is unchanged. -/
theorem rightBranch_survivesAbsorption :
    (FrontierCompletion.expandThenAbsorbLeft split leftToRight).map
        parentRightCompletion =
      (FrontierCompletion.head () :
        FrontierCompletion Completion [State.right]) := by
  rfl

def tailCompletion :
    FrontierCompletion Completion [State.parent, State.rest] :=
  .tail (.head ())

/-- Expanding and reducing the head preserves unrelated frontier completions. -/
theorem unrelatedTail_isPreserved :
    (FrontierCompletion.expandThenAbsorbLeft split leftToRight).map
        tailCompletion =
      (FrontierCompletion.tail (.head ()) :
        FrontierCompletion Completion [State.right, State.rest]) := by
  rfl

/-- The symmetric right-to-left reduction is also constructive. -/
theorem rightAbsorption_isSymmetric :
    (FrontierCompletion.expandThenAbsorbRight split rightToLeft).map
        parentRightCompletion =
      (FrontierCompletion.head () :
        FrontierCompletion Completion [State.left]) := by
  rfl

end ConstitutiveSearch.Tests.FrontierReductionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.FrontierReductionRegression.split
#print axioms ConstitutiveSearch.Tests.FrontierReductionRegression.leftBranch_survivesAbsorption
#print axioms ConstitutiveSearch.Tests.FrontierReductionRegression.rightBranch_survivesAbsorption
#print axioms ConstitutiveSearch.Tests.FrontierReductionRegression.unrelatedTail_isPreserved
#print axioms ConstitutiveSearch.Tests.FrontierReductionRegression.rightAbsorption_isSymmetric
/- AXIOM_AUDIT_END -/