import Alignment.AnchoredMatchReconstruction

/-!
# Intrinsic relational mediators

This module removes the requirement that a common anchor family be supplied as
an independent primitive.

Two already constituted carriers retain only their own local binary relations
with values in a common observation type.  A relational mediator is a positive
carrier of source/target pairs covering both sides and preserving the local
relations between every pair of mediator points.

The mediator points themselves can then serve as the common anchor family.
Coverage transports local self-separation to separation by those derived
anchors.  The existing anchored matching layer reconstructs the forward and
backward maps, their round trips, exact transport, and genesis persistence.

This is a reduction of the shared-anchor hypothesis, not yet a construction of
the mediator from raw independent systems.  The next existence problem is to
construct or refute such a mediator without supplying its pairing carrier.
-/

namespace Alignment
namespace GenesisReconstruction

universe uSource uTarget uValue uPair

/--
Two local relational structures with no common anchor type.  Each carrier must
be separated by observations from all identities of that same carrier.
-/
structure IntrinsicRelationalContext
    (Source : Type uSource)
    (Target : Type uTarget)
    (Value : Type uValue) where
  sourceRelation : Source → Source → Value
  targetRelation : Target → Target → Value
  sourceSeparates :
    ProfileSeparates
      (fun identity anchor : Source => sourceRelation anchor identity)
  targetSeparates :
    ProfileSeparates
      (fun identity anchor : Target => targetRelation anchor identity)

/--
A positive common mediator derived from paired local identities rather than an
externally supplied anchor family.

Every source and every target is represented by at least one mediator point.
The relation law says that all mediator pairs see the same local relational
observation on both sides.
-/
structure RelationalMediator
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    (context : IntrinsicRelationalContext Source Target Value) where
  Pair : Type uPair
  source : Pair → Source
  target : Pair → Target
  sourceWitness :
    (identity : Source) → { pair : Pair // source pair = identity }
  targetWitness :
    (identity : Target) → { pair : Pair // target pair = identity }
  preservesRelation :
    (first second : Pair) →
      context.targetRelation (target first) (target second) =
        context.sourceRelation (source first) (source second)

namespace RelationalMediator

/-- Coverage of the source side makes the derived mediator anchors separating. -/
theorem sourceProfileSeparates
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (mediator : RelationalMediator context) :
    ProfileSeparates
      (fun identity pair =>
        context.sourceRelation (mediator.source pair) identity) := by
  intro first second agreement
  apply context.sourceSeparates
  intro anchor
  let witness := mediator.sourceWitness anchor
  calc
    context.sourceRelation anchor first =
        context.sourceRelation (mediator.source witness.1) first :=
      congrArg (fun value => context.sourceRelation value first) witness.2.symm
    _ = context.sourceRelation (mediator.source witness.1) second :=
      agreement witness.1
    _ = context.sourceRelation anchor second :=
      congrArg (fun value => context.sourceRelation value second) witness.2

/-- Coverage of the target side makes the derived mediator anchors separating. -/
theorem targetProfileSeparates
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (mediator : RelationalMediator context) :
    ProfileSeparates
      (fun identity pair =>
        context.targetRelation (mediator.target pair) identity) := by
  intro first second agreement
  apply context.targetSeparates
  intro anchor
  let witness := mediator.targetWitness anchor
  calc
    context.targetRelation anchor first =
        context.targetRelation (mediator.target witness.1) first :=
      congrArg (fun value => context.targetRelation value first) witness.2.symm
    _ = context.targetRelation (mediator.target witness.1) second :=
      agreement witness.1
    _ = context.targetRelation anchor second :=
      congrArg (fun value => context.targetRelation value second) witness.2

/--
The mediator carrier itself is a derived common anchor family.  No independent
`Anchor`, `sourceAnchor`, or `targetAnchor` input remains.
-/
def toAnchoredContext
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (mediator : RelationalMediator context) :
    AnchoredRelationContext Source Target mediator.Pair Value :=
  { sourceRelation := context.sourceRelation
    targetRelation := context.targetRelation
    sourceAnchor := mediator.source
    targetAnchor := mediator.target
    sourceSeparates := mediator.sourceProfileSeparates
    targetSeparates := mediator.targetProfileSeparates }

/--
Every source obtains a target by choosing a mediator point covering that source.
The resulting pair satisfies the derived anchored match relation.
-/
def forwardWitness
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (mediator : RelationalMediator context)
    (identity : Source) :
    { target : Target // mediator.toAnchoredContext.Matches identity target } :=
  let witness := mediator.sourceWitness identity
  ⟨mediator.target witness.1, by
    intro anchor
    exact
      (mediator.preservesRelation anchor witness.1).trans
        (congrArg
          (context.sourceRelation (mediator.source anchor))
          witness.2)⟩

/--
Every target obtains a source symmetrically from target coverage of the same
mediator.
-/
def backwardWitness
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (mediator : RelationalMediator context)
    (identity : Target) :
    { source : Source // mediator.toAnchoredContext.Matches source identity } :=
  let witness := mediator.targetWitness identity
  ⟨mediator.source witness.1, by
    intro anchor
    exact
      (congrArg
        (context.targetRelation (mediator.target anchor))
        witness.2).symm.trans
          (mediator.preservesRelation anchor witness.1)⟩

/-- The derived anchor family is total in both directions. -/
def toTotalMatching
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (mediator : RelationalMediator context) :
    TotalAnchoredMatching mediator.toAnchoredContext :=
  { forwardWitness := mediator.forwardWitness
    backwardWitness := mediator.backwardWitness }

/-- Exact initial transport reconstructed from the intrinsic relational mediator. -/
def toExactTransport
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (mediator : RelationalMediator context) :
    ExactTypeTransport Source Target :=
  mediator.toTotalMatching.toExactTransport

/-- The mediator-induced transport propagates to every requested natural depth. -/
def finiteTransport
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (mediator : RelationalMediator context)
    (depth : Nat) :
    ExactTypeTransport
      (IteratedCarrier Source depth)
      (IteratedCarrier Target depth) :=
  mediator.toTotalMatching.finiteTransport depth

/-- Every mediator-induced natural-depth transport preserves genesis. -/
theorem finiteTransport_preservesGenesis
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (mediator : RelationalMediator context)
    (depth : Nat) :
    PreservesGenesis (mediator.finiteTransport depth) :=
  mediator.toTotalMatching.finiteTransport_preservesGenesis depth

end RelationalMediator

/--
Exact relational compatibility written without a common anchor family.  This
interface is used only to locate the remaining existence problem precisely.
-/
structure IntrinsicCompatibleExactAlignment
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    (context : IntrinsicRelationalContext Source Target Value) where
  transport : ExactTypeTransport Source Target
  preservesRelation :
    (first second : Source) →
      context.targetRelation
          (transport.forward first)
          (transport.forward second) =
        context.sourceRelation first second

namespace IntrinsicCompatibleExactAlignment

/--
Any already available exact relational alignment determines a mediator by using
its source carrier as the pairing carrier.  Therefore merely postulating a
mediator would not solve the upstream existence problem.
-/
def toRelationalMediator
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (alignment : IntrinsicCompatibleExactAlignment context) :
    RelationalMediator context :=
  { Pair := Source
    source := id
    target := alignment.transport.forward
    sourceWitness := fun identity => ⟨identity, rfl⟩
    targetWitness := fun identity =>
      ⟨alignment.transport.backward identity,
        alignment.transport.backwardForward identity⟩
    preservesRelation := alignment.preservesRelation }

/-- Reconstructing through the mediator retains the supplied forward map. -/
theorem mediatorReconstruction_forward
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (alignment : IntrinsicCompatibleExactAlignment context)
    (identity : Source) :
    alignment.toRelationalMediator.toExactTransport.forward identity =
      alignment.transport.forward identity := by
  rfl

/-- Exactness then forces agreement of the reconstructed backward map as well. -/
theorem mediatorReconstruction_backward
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (alignment : IntrinsicCompatibleExactAlignment context)
    (identity : Target) :
    alignment.toRelationalMediator.toExactTransport.backward identity =
      alignment.transport.backward identity :=
  ExactTypeTransport.backward_eq_of_forward_eq
    alignment.toRelationalMediator.toExactTransport
    alignment.transport
    alignment.mediatorReconstruction_forward
    identity

end IntrinsicCompatibleExactAlignment

end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.IntrinsicRelationalContext
#print axioms Alignment.GenesisReconstruction.RelationalMediator
#print axioms Alignment.GenesisReconstruction.RelationalMediator.sourceProfileSeparates
#print axioms Alignment.GenesisReconstruction.RelationalMediator.targetProfileSeparates
#print axioms Alignment.GenesisReconstruction.RelationalMediator.toAnchoredContext
#print axioms Alignment.GenesisReconstruction.RelationalMediator.forwardWitness
#print axioms Alignment.GenesisReconstruction.RelationalMediator.backwardWitness
#print axioms Alignment.GenesisReconstruction.RelationalMediator.toTotalMatching
#print axioms Alignment.GenesisReconstruction.RelationalMediator.toExactTransport
#print axioms Alignment.GenesisReconstruction.RelationalMediator.finiteTransport
#print axioms Alignment.GenesisReconstruction.RelationalMediator.finiteTransport_preservesGenesis
#print axioms Alignment.GenesisReconstruction.IntrinsicCompatibleExactAlignment
#print axioms Alignment.GenesisReconstruction.IntrinsicCompatibleExactAlignment.toRelationalMediator
#print axioms Alignment.GenesisReconstruction.IntrinsicCompatibleExactAlignment.mediatorReconstruction_forward
#print axioms Alignment.GenesisReconstruction.IntrinsicCompatibleExactAlignment.mediatorReconstruction_backward
/- AXIOM_AUDIT_END -/