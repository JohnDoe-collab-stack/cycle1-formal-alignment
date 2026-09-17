import Alignment.AnchoredRelationReconstruction

namespace Alignment.Tests.AnchoredRelationReconstructionRegression

open GenesisReconstruction

inductive SourceNode
  | root
  | next

inductive TargetNode
  | origin
  | successor

/-- A one-edge local relation on the source carrier. -/
def sourceRelation : SourceNode → SourceNode → Bool
  | .root, .next => true
  | _, _ => false

/-- The same relational shape on a different target carrier. -/
def targetRelation : TargetNode → TargetNode → Bool
  | .origin, .successor => true
  | _, _ => false

/-- One aligned structural anchor is enough to distinguish both nodes here. -/
def sourceAnchor : Unit → SourceNode :=
  fun _ => .root

def targetAnchor : Unit → TargetNode :=
  fun _ => .origin

def forward : SourceNode → TargetNode
  | .root => .origin
  | .next => .successor

def backward : TargetNode → SourceNode
  | .origin => .root
  | .successor => .next

theorem sourceAnchoredProfile_separates :
    ProfileSeparates
      (fun identity anchor => sourceRelation (sourceAnchor anchor) identity) := by
  intro first second agreement
  cases first <;> cases second
  · rfl
  · have impossible := agreement ()
    cases impossible
  · have impossible := agreement ()
    cases impossible
  · rfl

theorem targetAnchoredProfile_separates :
    ProfileSeparates
      (fun identity anchor => targetRelation (targetAnchor anchor) identity) := by
  intro first second agreement
  cases first <;> cases second
  · rfl
  · have impossible := agreement ()
    cases impossible
  · have impossible := agreement ()
    cases impossible
  · rfl

theorem forward_preservesAnchors :
    ∀ identity : SourceNode,
      ∀ anchor : Unit,
        targetRelation (targetAnchor anchor) (forward identity) =
          sourceRelation (sourceAnchor anchor) identity := by
  intro identity anchor
  cases identity <;> cases anchor <;> rfl

theorem backward_preservesAnchors :
    ∀ identity : TargetNode,
      ∀ anchor : Unit,
        sourceRelation (sourceAnchor anchor) (backward identity) =
          targetRelation (targetAnchor anchor) identity := by
  intro identity anchor
  cases identity <;> cases anchor <;> rfl

def anchoredResolver :
    BidirectionalAnchoredRelationResolver
      SourceNode TargetNode Unit Bool :=
  { sourceRelation := sourceRelation
    targetRelation := targetRelation
    sourceAnchor := sourceAnchor
    targetAnchor := targetAnchor
    forward := forward
    backward := backward
    sourceSeparates := sourceAnchoredProfile_separates
    targetSeparates := targetAnchoredProfile_separates
    forwardPreservesAnchors := forward_preservesAnchors
    backwardPreservesAnchors := backward_preservesAnchors }

/-- Exactness is derived from the anchored relational profiles. -/
theorem anchoredResolver_source_roundTrip :
    anchoredResolver.toExactTransport.backward
        (anchoredResolver.toExactTransport.forward SourceNode.next) =
      SourceNode.next :=
  anchoredResolver.toExactTransport.forwardBackward SourceNode.next

theorem anchoredResolver_target_roundTrip :
    anchoredResolver.toExactTransport.forward
        (anchoredResolver.toExactTransport.backward TargetNode.successor) =
      TargetNode.successor :=
  anchoredResolver.toExactTransport.backwardForward TargetNode.successor

/-- The reconstructed finite alignment preserves all later fresh strata. -/
theorem anchoredResolver_depth_two_preservesGenesis :
    PreservesGenesis (anchoredResolver.finiteTransport 2) :=
  anchoredResolver.finiteTransport_preservesGenesis 2

/-- The old initial identity is transported according to the anchored relation. -/
theorem anchoredResolver_depth_two_initial_next :
    (anchoredResolver.finiteTransport 2).forward
        (IteratedCarrier.embedInitial 2 SourceNode.next) =
      IteratedCarrier.embedInitial 2 TargetNode.successor := by
  rfl

/-- With no anchors, the induced profile cannot separate a two-point carrier. -/
theorem emptyAnchors_not_separating :
    ¬ ProfileSeparates
      (fun (_ : Bool) (anchor : Empty) => nomatch anchor) := by
  intro separates
  have impossible : false = true :=
    separates false true (by
      intro anchor
      exact nomatch anchor)
  cases impossible

end Alignment.Tests.AnchoredRelationReconstructionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.AnchoredRelationReconstructionRegression.anchoredResolver
#print axioms Alignment.Tests.AnchoredRelationReconstructionRegression.anchoredResolver_source_roundTrip
#print axioms Alignment.Tests.AnchoredRelationReconstructionRegression.anchoredResolver_target_roundTrip
#print axioms Alignment.Tests.AnchoredRelationReconstructionRegression.anchoredResolver_depth_two_preservesGenesis
#print axioms Alignment.Tests.AnchoredRelationReconstructionRegression.anchoredResolver_depth_two_initial_next
#print axioms Alignment.Tests.AnchoredRelationReconstructionRegression.emptyAnchors_not_separating
/- AXIOM_AUDIT_END -/
