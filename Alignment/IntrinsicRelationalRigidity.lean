import Alignment.IntrinsicRelationalMediator

/-!
# Intrinsic relational rigidity

Removing an externally supplied anchor family exposes a second question that
must not be hidden: even a fully relation-preserving exact correspondence need
not be unique when the target relational structure has a nontrivial
self-automorphism.

This module isolates that ambiguity.  Target relational rigidity states that
every exact target self-transport preserving the local binary relation fixes
every target identity.  Under that condition, any two intrinsic compatible
exact alignments have the same forward map pointwise, and exactness then forces
their backward maps as well.

Thus the remaining ambiguity after mediator existence is precisely structural
automorphism ambiguity at the initial layer.
-/

namespace Alignment
namespace GenesisReconstruction

universe uSource uTarget uValue

/-- Exact self-transports preserving one local binary relation are pointwise trivial. -/
def RelationallyRigid
    {Carrier : Type uTarget}
    {Value : Type uValue}
    (relation : Carrier → Carrier → Value) : Prop :=
  ∀ automorphism : ExactTypeTransport Carrier Carrier,
    ((first second : Carrier) →
      relation (automorphism.forward first) (automorphism.forward second) =
        relation first second) →
    (identity : Carrier) → automorphism.forward identity = identity

namespace IntrinsicCompatibleExactAlignment

/-- Forward relation preservation plus exactness reflects to the backward map. -/
theorem backward_preservesRelation
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (alignment : IntrinsicCompatibleExactAlignment context)
    (first second : Target) :
    context.sourceRelation
        (alignment.transport.backward first)
        (alignment.transport.backward second) =
      context.targetRelation first second := by
  calc
    context.sourceRelation
        (alignment.transport.backward first)
        (alignment.transport.backward second) =
      context.targetRelation
        (alignment.transport.forward (alignment.transport.backward first))
        (alignment.transport.forward (alignment.transport.backward second)) :=
      (alignment.preservesRelation
        (alignment.transport.backward first)
        (alignment.transport.backward second)).symm
    _ = context.targetRelation
          first
          (alignment.transport.forward (alignment.transport.backward second)) :=
      congrArg
        (fun identity =>
          context.targetRelation identity
            (alignment.transport.forward (alignment.transport.backward second)))
        (alignment.transport.backwardForward first)
    _ = context.targetRelation first second :=
      congrArg
        (context.targetRelation first)
        (alignment.transport.backwardForward second)

/-- Compare two compatible alignments by the target automorphism taking the first to the second. -/
def targetDifference
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (first second : IntrinsicCompatibleExactAlignment context) :
    ExactTypeTransport Target Target :=
  first.transport.reverse.compose second.transport

/-- The comparison automorphism preserves the target's intrinsic relation. -/
theorem targetDifference_preservesRelation
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (first second : IntrinsicCompatibleExactAlignment context)
    (left right : Target) :
    context.targetRelation
        ((first.targetDifference second).forward left)
        ((first.targetDifference second).forward right) =
      context.targetRelation left right := by
  change
    context.targetRelation
        (second.transport.forward (first.transport.backward left))
        (second.transport.forward (first.transport.backward right)) =
      context.targetRelation left right
  exact
    (second.preservesRelation
      (first.transport.backward left)
      (first.transport.backward right)).trans
        (first.backward_preservesRelation left right)

/-- Target relational rigidity removes all remaining forward ambiguity. -/
theorem forward_unique_of_targetRigidity
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (targetRigid : RelationallyRigid context.targetRelation)
    (first second : IntrinsicCompatibleExactAlignment context)
    (identity : Source) :
    first.transport.forward identity = second.transport.forward identity := by
  have fixed :=
    targetRigid
      (first.targetDifference second)
      (first.targetDifference_preservesRelation second)
      (first.transport.forward identity)
  change
    second.transport.forward
        (first.transport.backward (first.transport.forward identity)) =
      first.transport.forward identity at fixed
  rw [first.transport.forwardBackward] at fixed
  exact fixed.symm

/-- Backward maps are forced once target rigidity fixes the forward correspondence. -/
theorem backward_unique_of_targetRigidity
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (targetRigid : RelationallyRigid context.targetRelation)
    (first second : IntrinsicCompatibleExactAlignment context)
    (identity : Target) :
    first.transport.backward identity = second.transport.backward identity :=
  ExactTypeTransport.backward_eq_of_forward_eq
    first.transport
    second.transport
    (first.forward_unique_of_targetRigidity targetRigid second)
    identity

end IntrinsicCompatibleExactAlignment

end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.RelationallyRigid
#print axioms Alignment.GenesisReconstruction.IntrinsicCompatibleExactAlignment.backward_preservesRelation
#print axioms Alignment.GenesisReconstruction.IntrinsicCompatibleExactAlignment.targetDifference
#print axioms Alignment.GenesisReconstruction.IntrinsicCompatibleExactAlignment.targetDifference_preservesRelation
#print axioms Alignment.GenesisReconstruction.IntrinsicCompatibleExactAlignment.forward_unique_of_targetRigidity
#print axioms Alignment.GenesisReconstruction.IntrinsicCompatibleExactAlignment.backward_unique_of_targetRigidity
/- AXIOM_AUDIT_END -/