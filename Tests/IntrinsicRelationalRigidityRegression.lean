import Alignment.IntrinsicRelationalRigidity
import Tests.IntrinsicRelationalMediatorRegression

namespace Alignment.Tests.IntrinsicRelationalRigidityRegression

open GenesisReconstruction
open IntrinsicRelationalMediatorRegression

/-! ## The symmetric separator really has automorphism ambiguity -/

theorem symmetricRelation_not_rigid :
    ¬ RelationallyRigid symmetricRelation := by
  intro rigid
  have fixed :=
    rigid swapTransport swap_preserves_symmetricRelation false
  change true = false at fixed
  cases fixed

/-! ## A directed two-point relation has no nontrivial exact automorphism -/

theorem targetRelation_rigid :
    RelationallyRigid targetRelation := by
  intro automorphism preserves identity
  have originFixed :
      automorphism.forward TargetNode.origin = TargetNode.origin := by
    cases originImage : automorphism.forward TargetNode.origin with
    | origin =>
        rfl
    | successor =>
        have edge := preserves TargetNode.origin TargetNode.successor
        rw [originImage] at edge
        cases successorImage : automorphism.forward TargetNode.successor with
        | origin =>
            rw [successorImage] at edge
            cases edge
        | successor =>
            rw [successorImage] at edge
            cases edge
  cases identity with
  | origin =>
      exact originFixed
  | successor =>
      cases successorImage : automorphism.forward TargetNode.successor with
      | origin =>
          have sameImage :
              automorphism.forward TargetNode.origin =
                automorphism.forward TargetNode.successor :=
            originFixed.trans successorImage.symm
          have impossible : TargetNode.origin = TargetNode.successor :=
            forward_injective automorphism sameImage
          cases impossible
      | successor =>
          rfl

/-! ## Rigidity forces independently constructed compatible alignments to agree -/

def directForward : SourceNode → TargetNode
  | .root => .origin
  | .next => .successor

def directBackward : TargetNode → SourceNode
  | .origin => .root
  | .successor => .next

def directTransport : ExactTypeTransport SourceNode TargetNode :=
  { forward := directForward
    backward := directBackward
    forwardBackward := by
      intro identity
      cases identity <;> rfl
    backwardForward := by
      intro identity
      cases identity <;> rfl }

def directAlignment : IntrinsicCompatibleExactAlignment context :=
  { transport := directTransport
    preservesRelation := by
      intro first second
      cases first <;> cases second <;> rfl }

def mediatorAlignment : IntrinsicCompatibleExactAlignment context :=
  { transport := mediator.toExactTransport
    preservesRelation := by
      intro first second
      cases first <;> cases second <;> rfl }

theorem rigid_target_forces_forward_agreement
    (identity : SourceNode) :
    mediatorAlignment.transport.forward identity =
      directAlignment.transport.forward identity :=
  mediatorAlignment.forward_unique_of_targetRigidity
    targetRelation_rigid directAlignment identity

theorem rigid_target_forces_backward_agreement
    (identity : TargetNode) :
    mediatorAlignment.transport.backward identity =
      directAlignment.transport.backward identity :=
  mediatorAlignment.backward_unique_of_targetRigidity
    targetRelation_rigid directAlignment identity

end Alignment.Tests.IntrinsicRelationalRigidityRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.IntrinsicRelationalRigidityRegression.symmetricRelation_not_rigid
#print axioms Alignment.Tests.IntrinsicRelationalRigidityRegression.targetRelation_rigid
#print axioms Alignment.Tests.IntrinsicRelationalRigidityRegression.directTransport
#print axioms Alignment.Tests.IntrinsicRelationalRigidityRegression.directAlignment
#print axioms Alignment.Tests.IntrinsicRelationalRigidityRegression.mediatorAlignment
#print axioms Alignment.Tests.IntrinsicRelationalRigidityRegression.rigid_target_forces_forward_agreement
#print axioms Alignment.Tests.IntrinsicRelationalRigidityRegression.rigid_target_forces_backward_agreement
/- AXIOM_AUDIT_END -/