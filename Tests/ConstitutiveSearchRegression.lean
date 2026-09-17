import ConstitutiveSearch.ContinuationTransport

namespace ConstitutiveSearch.Tests.ContinuationTransportRegression

open ConstitutiveSearch

inductive BinaryState
  | parent
  | left
  | right

def BinaryCompletion : BinaryState → Type
  | .parent => Bool
  | .left => Unit
  | .right => Unit

def binarySplit :
    ExactBinarySplit
      BinaryCompletion BinaryState.parent BinaryState.left BinaryState.right :=
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
    ContinuationTransport
      BinaryCompletion BinaryState.left BinaryState.right :=
  { map := fun _ => () }

/-- Both parent completions survive after the left branch is absorbed rightward. -/
theorem parentCompletion_reducesRight
    (completion : BinaryCompletion BinaryState.parent) :
    (binarySplit.eliminateLeft leftToRight).map completion = () := by
  cases completion <;> rfl

/-- Positive parent existence is constructively retained on the right. -/
def parentExistence_reducesRight :
    Nonempty (BinaryCompletion BinaryState.parent) →
      Nonempty (BinaryCompletion BinaryState.right) :=
  binarySplit.eliminateLeft_preservesExistence leftToRight

inductive SparseState
  | dead
  | live

def SparseCompletion : SparseState → Type
  | .dead => Empty
  | .live => Unit

/-- A directional transport may exist without any reverse transport. -/
def deadToLive :
    ContinuationTransport SparseCompletion SparseState.dead SparseState.live :=
  { map := fun impossible => nomatch impossible }

/-- No reverse transport can be manufactured from the directional one. -/
theorem noLiveToDead
    (transport :
      ContinuationTransport SparseCompletion SparseState.live SparseState.dead) :
    False := by
  exact nomatch transport.map ()

inductive CollapseState
  | many
  | one

def CollapseCompletion : CollapseState → Type
  | .many => Bool
  | .one => Unit

/-- Existence-preserving continuation transport does not require injectivity. -/
def manyToOne :
    ContinuationTransport CollapseCompletion CollapseState.many CollapseState.one :=
  { map := fun _ => () }

theorem manyToOne_notInjective :
    ¬ Function.Injective manyToOne.map := by
  intro injective
  have falseEqualsTrue : false = true :=
    injective rfl
  cases falseEqualsTrue

end ConstitutiveSearch.Tests.ContinuationTransportRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.ContinuationTransportRegression.binarySplit
#print axioms ConstitutiveSearch.Tests.ContinuationTransportRegression.parentCompletion_reducesRight
#print axioms ConstitutiveSearch.Tests.ContinuationTransportRegression.deadToLive
#print axioms ConstitutiveSearch.Tests.ContinuationTransportRegression.noLiveToDead
#print axioms ConstitutiveSearch.Tests.ContinuationTransportRegression.manyToOne_notInjective
/- AXIOM_AUDIT_END -/