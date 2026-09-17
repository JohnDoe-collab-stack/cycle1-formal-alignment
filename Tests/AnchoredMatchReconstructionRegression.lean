import Alignment.AnchoredMatchReconstruction

namespace Alignment.Tests.AnchoredMatchReconstructionRegression

open GenesisReconstruction

inductive SourceNode
  | root
  | next

inductive TargetNode
  | origin
  | successor

def sourceRelation (source target : SourceNode) : Bool :=
  match source with
  | .root =>
      match target with
      | .root => false
      | .next => true
  | .next => false

def targetRelation (source target : TargetNode) : Bool :=
  match source with
  | .origin =>
      match target with
      | .origin => false
      | .successor => true
  | .successor => false

def sourceAnchor : Unit → SourceNode :=
  fun _ => .root

def targetAnchor : Unit → TargetNode :=
  fun _ => .origin

theorem sourceProfile_separates :
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

theorem targetProfile_separates :
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

def context :
    AnchoredRelationContext SourceNode TargetNode Unit Bool :=
  { sourceRelation := sourceRelation
    targetRelation := targetRelation
    sourceAnchor := sourceAnchor
    targetAnchor := targetAnchor
    sourceSeparates := sourceProfile_separates
    targetSeparates := targetProfile_separates }

/-- Positive target witnesses are produced from the structural match relation. -/
def forwardWitness :
    (source : SourceNode) →
      { target : TargetNode // context.Matches source target }
  | .root => ⟨.origin, by intro anchor; cases anchor; rfl⟩
  | .next => ⟨.successor, by intro anchor; cases anchor; rfl⟩

/-- Positive source witnesses are produced independently in the reverse direction. -/
def backwardWitness :
    (target : TargetNode) →
      { source : SourceNode // context.Matches source target }
  | .origin => ⟨.root, by intro anchor; cases anchor; rfl⟩
  | .successor => ⟨.next, by intro anchor; cases anchor; rfl⟩

def totalMatching : TotalAnchoredMatching context :=
  { forwardWitness := forwardWitness
    backwardWitness := backwardWitness }

/-- The exact transport is derived from structural totality and separation. -/
theorem totalMatching_source_roundTrip :
    totalMatching.toExactTransport.backward
        (totalMatching.toExactTransport.forward SourceNode.next) =
      SourceNode.next :=
  totalMatching.toExactTransport.forwardBackward SourceNode.next

theorem totalMatching_target_roundTrip :
    totalMatching.toExactTransport.forward
        (totalMatching.toExactTransport.backward TargetNode.successor) =
      TargetNode.successor :=
  totalMatching.toExactTransport.backwardForward TargetNode.successor

/-- The structural matching propagates through finite genesis. -/
theorem totalMatching_depth_three_preservesGenesis :
    PreservesGenesis (totalMatching.finiteTransport 3) :=
  totalMatching.finiteTransport_preservesGenesis 3

/-- No independently chosen resolver is needed to align an initial old identity. -/
theorem totalMatching_depth_three_next :
    (totalMatching.finiteTransport 3).forward
        (IteratedCarrier.embedInitial 3 SourceNode.next) =
      IteratedCarrier.embedInitial 3 TargetNode.successor := by
  rfl

/--
A separating structural context need not be total. Here `true` has no target
whose anchored profile matches it.
-/
def partialSourceRelation (_source target : Bool) : Bool :=
  target

def partialTargetRelation (_source _target : Unit) : Bool :=
  false

def partialSourceAnchor : Unit → Bool :=
  fun _ => false

def partialTargetAnchor : Unit → Unit :=
  fun _ => ()

theorem partialSourceProfile_separates :
    ProfileSeparates
      (fun identity anchor =>
        partialSourceRelation (partialSourceAnchor anchor) identity) := by
  intro first second agreement
  exact agreement ()

theorem partialTargetProfile_separates :
    ProfileSeparates
      (fun identity anchor =>
        partialTargetRelation (partialTargetAnchor anchor) identity) := by
  intro first second _
  cases first
  cases second
  rfl

def partialContext :
    AnchoredRelationContext Bool Unit Unit Bool :=
  { sourceRelation := partialSourceRelation
    targetRelation := partialTargetRelation
    sourceAnchor := partialSourceAnchor
    targetAnchor := partialTargetAnchor
    sourceSeparates := partialSourceProfile_separates
    targetSeparates := partialTargetProfile_separates }

theorem true_has_no_structural_target :
    ¬ ∃ target : Unit, partialContext.Matches true target := by
  intro witness
  rcases witness with ⟨target, matchProof⟩
  cases target
  have impossible := matchProof ()
  change false = true at impossible
  cases impossible

end Alignment.Tests.AnchoredMatchReconstructionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.AnchoredMatchReconstructionRegression.context
#print axioms Alignment.Tests.AnchoredMatchReconstructionRegression.forwardWitness
#print axioms Alignment.Tests.AnchoredMatchReconstructionRegression.backwardWitness
#print axioms Alignment.Tests.AnchoredMatchReconstructionRegression.totalMatching
#print axioms Alignment.Tests.AnchoredMatchReconstructionRegression.totalMatching_source_roundTrip
#print axioms Alignment.Tests.AnchoredMatchReconstructionRegression.totalMatching_target_roundTrip
#print axioms Alignment.Tests.AnchoredMatchReconstructionRegression.totalMatching_depth_three_preservesGenesis
#print axioms Alignment.Tests.AnchoredMatchReconstructionRegression.totalMatching_depth_three_next
#print axioms Alignment.Tests.AnchoredMatchReconstructionRegression.partialContext
#print axioms Alignment.Tests.AnchoredMatchReconstructionRegression.true_has_no_structural_target
/- AXIOM_AUDIT_END -/
