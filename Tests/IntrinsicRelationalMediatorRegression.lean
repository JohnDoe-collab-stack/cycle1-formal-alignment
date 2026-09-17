import Alignment.IntrinsicRelationalMediator

namespace Alignment.Tests.IntrinsicRelationalMediatorRegression

open GenesisReconstruction

/-! ## Positive reconstruction without a supplied common anchor type -/

inductive SourceNode
  | root
  | next

inductive TargetNode
  | origin
  | successor

/-- Source-local binary relation. -/
def sourceRelation (source target : SourceNode) : Bool :=
  match source with
  | .root =>
      match target with
      | .root => false
      | .next => true
  | .next => false

/-- The same relational shape on a distinct target carrier. -/
def targetRelation (source target : TargetNode) : Bool :=
  match source with
  | .origin =>
      match target with
      | .origin => false
      | .successor => true
  | .successor => false

theorem sourceSelfProfile_separates :
    ProfileSeparates
      (fun identity anchor : SourceNode => sourceRelation anchor identity) := by
  intro first second agreement
  cases first <;> cases second
  · rfl
  · have impossible := agreement SourceNode.root
    cases impossible
  · have impossible := agreement SourceNode.root
    cases impossible
  · rfl

theorem targetSelfProfile_separates :
    ProfileSeparates
      (fun identity anchor : TargetNode => targetRelation anchor identity) := by
  intro first second agreement
  cases first <;> cases second
  · rfl
  · have impossible := agreement TargetNode.origin
    cases impossible
  · have impossible := agreement TargetNode.origin
    cases impossible
  · rfl

def context :
    IntrinsicRelationalContext SourceNode TargetNode Bool :=
  { sourceRelation := sourceRelation
    targetRelation := targetRelation
    sourceSeparates := sourceSelfProfile_separates
    targetSeparates := targetSelfProfile_separates }

/--
The mediator pairs are the common anchors.  No independent anchor carrier or
anchor maps are supplied to `context`.
-/
inductive Pair
  | roots
  | successors

def pairSource : Pair → SourceNode
  | .roots => .root
  | .successors => .next

def pairTarget : Pair → TargetNode
  | .roots => .origin
  | .successors => .successor

def sourceWitness :
    (identity : SourceNode) → { pair : Pair // pairSource pair = identity }
  | .root => ⟨.roots, rfl⟩
  | .next => ⟨.successors, rfl⟩

def targetWitness :
    (identity : TargetNode) → { pair : Pair // pairTarget pair = identity }
  | .origin => ⟨.roots, rfl⟩
  | .successor => ⟨.successors, rfl⟩

theorem pair_preservesRelation
    (first second : Pair) :
    targetRelation (pairTarget first) (pairTarget second) =
      sourceRelation (pairSource first) (pairSource second) := by
  cases first <;> cases second <;> rfl

def mediator : RelationalMediator context :=
  { Pair := Pair
    source := pairSource
    target := pairTarget
    sourceWitness := sourceWitness
    targetWitness := targetWitness
    preservesRelation := pair_preservesRelation }

/-- The derived mediator anchors separate the source carrier. -/
theorem derived_source_anchors_separate :
    ProfileSeparates
      (fun identity pair =>
        context.sourceRelation (mediator.source pair) identity) :=
  mediator.sourceProfileSeparates

/-- The derived mediator anchors separate the target carrier. -/
theorem derived_target_anchors_separate :
    ProfileSeparates
      (fun identity pair =>
        context.targetRelation (mediator.target pair) identity) :=
  mediator.targetProfileSeparates

/-- Exact transport is reconstructed from the pair mediator. -/
theorem mediator_forward_next :
    mediator.toExactTransport.forward SourceNode.next = TargetNode.successor := by
  rfl

theorem mediator_backward_successor :
    mediator.toExactTransport.backward TargetNode.successor = SourceNode.next := by
  rfl

/-- The reconstructed transport propagates through arbitrary requested genesis depth. -/
theorem mediator_depth_three_preservesGenesis :
    PreservesGenesis (mediator.finiteTransport 3) :=
  mediator.finiteTransport_preservesGenesis 3

/-! ## Separator: mediator existence is not yet canonical reconstruction -/

/-- A symmetric two-point relation with a nontrivial automorphism. -/
def symmetricRelation (source target : Bool) : Bool :=
  match source, target with
  | false, false => true
  | true, true => true
  | false, true => false
  | true, false => false

theorem symmetricSelfProfile_separates :
    ProfileSeparates
      (fun identity anchor : Bool => symmetricRelation anchor identity) := by
  intro first second agreement
  cases first <;> cases second
  · rfl
  · have impossible := agreement false
    cases impossible
  · have impossible := agreement true
    cases impossible
  · rfl

def symmetricContext :
    IntrinsicRelationalContext Bool Bool Bool :=
  { sourceRelation := symmetricRelation
    targetRelation := symmetricRelation
    sourceSeparates := symmetricSelfProfile_separates
    targetSeparates := symmetricSelfProfile_separates }

def swapBool : Bool → Bool
  | false => true
  | true => false

theorem swapBool_involutive
    (value : Bool) :
    swapBool (swapBool value) = value := by
  cases value <;> rfl

def swapTransport : ExactTypeTransport Bool Bool :=
  { forward := swapBool
    backward := swapBool
    forwardBackward := swapBool_involutive
    backwardForward := swapBool_involutive }

theorem swap_preserves_symmetricRelation
    (first second : Bool) :
    symmetricRelation (swapBool first) (swapBool second) =
      symmetricRelation first second := by
  cases first <;> cases second <;> rfl

def identityAlignment :
    IntrinsicCompatibleExactAlignment symmetricContext :=
  { transport := ExactTypeTransport.reflexive Bool
    preservesRelation := by
      intro first second
      rfl }

def swapAlignment :
    IntrinsicCompatibleExactAlignment symmetricContext :=
  { transport := swapTransport
    preservesRelation := swap_preserves_symmetricRelation }

/--
Two valid intrinsic mediators can reconstruct different transports when the
local relational structure has a genuine automorphism.  Removing an external
anchor family therefore does not by itself provide a canonical mediator.
-/
theorem mediator_existence_does_not_force_unique_alignment :
    identityAlignment.toRelationalMediator.toExactTransport.forward false ≠
      swapAlignment.toRelationalMediator.toExactTransport.forward false := by
  change false ≠ true
  intro equality
  cases equality

end Alignment.Tests.IntrinsicRelationalMediatorRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.IntrinsicRelationalMediatorRegression.context
#print axioms Alignment.Tests.IntrinsicRelationalMediatorRegression.mediator
#print axioms Alignment.Tests.IntrinsicRelationalMediatorRegression.derived_source_anchors_separate
#print axioms Alignment.Tests.IntrinsicRelationalMediatorRegression.derived_target_anchors_separate
#print axioms Alignment.Tests.IntrinsicRelationalMediatorRegression.mediator_forward_next
#print axioms Alignment.Tests.IntrinsicRelationalMediatorRegression.mediator_backward_successor
#print axioms Alignment.Tests.IntrinsicRelationalMediatorRegression.mediator_depth_three_preservesGenesis
#print axioms Alignment.Tests.IntrinsicRelationalMediatorRegression.symmetricContext
#print axioms Alignment.Tests.IntrinsicRelationalMediatorRegression.swapTransport
#print axioms Alignment.Tests.IntrinsicRelationalMediatorRegression.identityAlignment
#print axioms Alignment.Tests.IntrinsicRelationalMediatorRegression.swapAlignment
#print axioms Alignment.Tests.IntrinsicRelationalMediatorRegression.mediator_existence_does_not_force_unique_alignment
/- AXIOM_AUDIT_END -/