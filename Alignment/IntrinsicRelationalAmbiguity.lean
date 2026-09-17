import Alignment.IntrinsicRelationalEquivalence
import Alignment.IntrinsicRelationalRigidity

/-!
# Exact ambiguity of intrinsic relational alignment

Once common anchors are removed, bare relational structure does not generally
select one compatible exact correspondence. The obstruction is not vague
non-uniqueness. It is exact automorphism freedom.

This module packages relation-preserving exact self-transports and proves that,
after one compatible exact alignment is fixed, every second compatible exact
alignment is obtained by postcomposing the first with a relation-preserving
automorphism of the target. Conversely, every such automorphism produces a new
compatible alignment.

Thus compatible alignments form a constructive torsor-like family under target
relational automorphisms. No quotient or classical choice is introduced. When
`RelationallyRigid` holds, the family collapses pointwise to one correspondence,
as already proved by `IntrinsicRelationalRigidity`.
-/

namespace Alignment
namespace GenesisReconstruction

universe uSource uTarget uValue

/-- A reversible self-transport preserving one intrinsic binary relation. -/
structure RelationAutomorphism
    {Carrier : Type uTarget}
    {Value : Type uValue}
    (relation : Carrier → Carrier → Value) where
  transport : ExactTypeTransport Carrier Carrier
  preservesRelation :
    (first second : Carrier) →
      relation (transport.forward first) (transport.forward second) =
        relation first second

namespace RelationAutomorphism

/-- The identity self-transport is a relation automorphism. -/
def reflexive
    {Carrier : Type uTarget}
    {Value : Type uValue}
    (relation : Carrier → Carrier → Value) :
    RelationAutomorphism relation :=
  { transport := ExactTypeTransport.reflexive Carrier
    preservesRelation := by
      intro first second
      rfl }

/-- Relation automorphisms compose constructively. -/
def compose
    {Carrier : Type uTarget}
    {Value : Type uValue}
    {relation : Carrier → Carrier → Value}
    (first second : RelationAutomorphism relation) :
    RelationAutomorphism relation :=
  { transport := first.transport.compose second.transport
    preservesRelation := by
      intro left right
      calc
        relation
            (second.transport.forward (first.transport.forward left))
            (second.transport.forward (first.transport.forward right)) =
          relation
            (first.transport.forward left)
            (first.transport.forward right) :=
          second.preservesRelation
            (first.transport.forward left)
            (first.transport.forward right)
        _ = relation left right := first.preservesRelation left right }

/-- Exactness reflects relation preservation to the inverse self-map. -/
theorem backward_preservesRelation
    {Carrier : Type uTarget}
    {Value : Type uValue}
    {relation : Carrier → Carrier → Value}
    (automorphism : RelationAutomorphism relation)
    (first second : Carrier) :
    relation
        (automorphism.transport.backward first)
        (automorphism.transport.backward second) =
      relation first second := by
  calc
    relation
        (automorphism.transport.backward first)
        (automorphism.transport.backward second) =
      relation
        (automorphism.transport.forward
          (automorphism.transport.backward first))
        (automorphism.transport.forward
          (automorphism.transport.backward second)) :=
      (automorphism.preservesRelation
        (automorphism.transport.backward first)
        (automorphism.transport.backward second)).symm
    _ = relation first
          (automorphism.transport.forward
            (automorphism.transport.backward second)) :=
      congrArg
        (fun identity =>
          relation identity
            (automorphism.transport.forward
              (automorphism.transport.backward second)))
        (automorphism.transport.backwardForward first)
    _ = relation first second :=
      congrArg
        (relation first)
        (automorphism.transport.backwardForward second)

/-- The inverse exact transport is itself a relation automorphism. -/
def reverse
    {Carrier : Type uTarget}
    {Value : Type uValue}
    {relation : Carrier → Carrier → Value}
    (automorphism : RelationAutomorphism relation) :
    RelationAutomorphism relation :=
  { transport := automorphism.transport.reverse
    preservesRelation := automorphism.backward_preservesRelation }

end RelationAutomorphism

namespace IntrinsicCompatibleExactAlignment

/-- Postcompose one compatible alignment with a target relation automorphism. -/
def postcompose
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (alignment : IntrinsicCompatibleExactAlignment context)
    (automorphism : RelationAutomorphism context.targetRelation) :
    IntrinsicCompatibleExactAlignment context :=
  { transport := alignment.transport.compose automorphism.transport
    preservesRelation := by
      intro first second
      calc
        context.targetRelation
            (automorphism.transport.forward
              (alignment.transport.forward first))
            (automorphism.transport.forward
              (alignment.transport.forward second)) =
          context.targetRelation
            (alignment.transport.forward first)
            (alignment.transport.forward second) :=
          automorphism.preservesRelation
            (alignment.transport.forward first)
            (alignment.transport.forward second)
        _ = context.sourceRelation first second :=
          alignment.preservesRelation first second }

/--
The target difference between two compatible alignments is exactly a target
relation automorphism.
-/
def differenceAutomorphism
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (first second : IntrinsicCompatibleExactAlignment context) :
    RelationAutomorphism context.targetRelation :=
  { transport := first.targetDifference second
    preservesRelation := first.targetDifference_preservesRelation second }

/--
Every second compatible alignment is recovered by postcomposing the first with
their target difference automorphism.
-/
theorem postcompose_difference_forward
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (first second : IntrinsicCompatibleExactAlignment context)
    (identity : Source) :
    (first.postcompose (first.differenceAutomorphism second)).transport.forward
        identity =
      second.transport.forward identity := by
  change
    second.transport.forward
        (first.transport.backward (first.transport.forward identity)) =
      second.transport.forward identity
  rw [first.transport.forwardBackward]

/-- The backward map is recovered by the same automorphism action. -/
theorem postcompose_difference_backward
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (first second : IntrinsicCompatibleExactAlignment context)
    (identity : Target) :
    (first.postcompose (first.differenceAutomorphism second)).transport.backward
        identity =
      second.transport.backward identity := by
  change
    first.transport.backward
        (first.transport.forward (second.transport.backward identity)) =
      second.transport.backward identity
  rw [first.transport.forwardBackward]

/--
A target automorphism that moves one target identity necessarily produces a
different compatible alignment, witnessed on the source preimage of that
identity.
-/
theorem postcompose_differs_of_moves_target
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (alignment : IntrinsicCompatibleExactAlignment context)
    (automorphism : RelationAutomorphism context.targetRelation)
    (target : Target)
    (moves : automorphism.transport.forward target ≠ target) :
    (alignment.postcompose automorphism).transport.forward
        (alignment.transport.backward target) ≠
      alignment.transport.forward
        (alignment.transport.backward target) := by
  intro equality
  have fixed : automorphism.transport.forward target = target := by
    calc
      automorphism.transport.forward target =
        automorphism.transport.forward
          (alignment.transport.forward
            (alignment.transport.backward target)) :=
        congrArg automorphism.transport.forward
          (alignment.transport.backwardForward target).symm
      _ = alignment.transport.forward
          (alignment.transport.backward target) := equality
      _ = target := alignment.transport.backwardForward target
  exact moves fixed

/--
Relational rigidity is equivalent to pointwise triviality of every packaged
relation automorphism.
-/
theorem relationallyRigid_iff_automorphisms_fixed
    {Carrier : Type uTarget}
    {Value : Type uValue}
    {relation : Carrier → Carrier → Value} :
    RelationallyRigid relation ↔
      ((automorphism : RelationAutomorphism relation) →
        (identity : Carrier) →
          automorphism.transport.forward identity = identity) := by
  constructor
  · intro rigid automorphism identity
    exact rigid automorphism.transport automorphism.preservesRelation identity
  · intro fixed automorphism preserves identity
    exact fixed
      { transport := automorphism
        preservesRelation := preserves }
      identity

end IntrinsicCompatibleExactAlignment

end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.RelationAutomorphism
#print axioms Alignment.GenesisReconstruction.RelationAutomorphism.reflexive
#print axioms Alignment.GenesisReconstruction.RelationAutomorphism.compose
#print axioms Alignment.GenesisReconstruction.RelationAutomorphism.backward_preservesRelation
#print axioms Alignment.GenesisReconstruction.RelationAutomorphism.reverse
#print axioms Alignment.GenesisReconstruction.IntrinsicCompatibleExactAlignment.postcompose
#print axioms Alignment.GenesisReconstruction.IntrinsicCompatibleExactAlignment.differenceAutomorphism
#print axioms Alignment.GenesisReconstruction.IntrinsicCompatibleExactAlignment.postcompose_difference_forward
#print axioms Alignment.GenesisReconstruction.IntrinsicCompatibleExactAlignment.postcompose_difference_backward
#print axioms Alignment.GenesisReconstruction.IntrinsicCompatibleExactAlignment.postcompose_differs_of_moves_target
#print axioms Alignment.GenesisReconstruction.IntrinsicCompatibleExactAlignment.relationallyRigid_iff_automorphisms_fixed
/- AXIOM_AUDIT_END -/