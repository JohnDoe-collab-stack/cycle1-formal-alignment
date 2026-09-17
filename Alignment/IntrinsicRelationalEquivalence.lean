import Alignment.IntrinsicRelationalMediator

/-!
# Equivalence between relational mediators and compatible exact alignment

The mediator introduced by `IntrinsicRelationalMediator` is not a weaker hidden
notion of alignment. Once its pairing carrier covers both sides and preserves
all intrinsic binary relations, the exact transport reconstructed from that
mediator itself preserves the complete relation.

Conversely, `IntrinsicCompatibleExactAlignment.toRelationalMediator` already
constructs a mediator from any compatible exact alignment. The two directions
therefore contain the same correspondence information at the level of induced
transport. This isolates the remaining upstream problem sharply: construct or
refute a compatible exact relation-preserving correspondence from the two local
relational structures, rather than postulating an anchor family or a mediator.
-/

namespace Alignment
namespace GenesisReconstruction

universe uSource uTarget uValue

namespace RelationalMediator

/--
The exact transport reconstructed from a mediator preserves the full intrinsic
binary relation, not only the anchored profiles used internally by the
reconstruction.
-/
theorem toExactTransport_preservesRelation
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (mediator : RelationalMediator context)
    (first second : Source) :
    context.targetRelation
        (mediator.toExactTransport.forward first)
        (mediator.toExactTransport.forward second) =
      context.sourceRelation first second := by
  let firstWitness := mediator.sourceWitness first
  let secondWitness := mediator.sourceWitness second
  change
    context.targetRelation
        (mediator.target firstWitness.1)
        (mediator.target secondWitness.1) =
      context.sourceRelation first second
  calc
    context.targetRelation
        (mediator.target firstWitness.1)
        (mediator.target secondWitness.1) =
      context.sourceRelation
        (mediator.source firstWitness.1)
        (mediator.source secondWitness.1) :=
      mediator.preservesRelation firstWitness.1 secondWitness.1
    _ = context.sourceRelation first (mediator.source secondWitness.1) :=
      congrArg
        (fun source =>
          context.sourceRelation source (mediator.source secondWitness.1))
        firstWitness.2
    _ = context.sourceRelation first second :=
      congrArg (context.sourceRelation first) secondWitness.2

/-- A relational mediator therefore determines a compatible exact alignment. -/
def toIntrinsicCompatibleExactAlignment
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (mediator : RelationalMediator context) :
    IntrinsicCompatibleExactAlignment context :=
  { transport := mediator.toExactTransport
    preservesRelation := mediator.toExactTransport_preservesRelation }

/--
Passing from a mediator to its compatible alignment and back to a mediator does
not change the induced forward transport.
-/
theorem alignmentMediatorRoundTrip_forward
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (mediator : RelationalMediator context)
    (identity : Source) :
    (RelationalMediator.toExactTransport
      (IntrinsicCompatibleExactAlignment.toRelationalMediator
        (RelationalMediator.toIntrinsicCompatibleExactAlignment mediator))).forward
        identity = mediator.toExactTransport.forward identity :=
  mediator.toIntrinsicCompatibleExactAlignment.mediatorReconstruction_forward
    identity

/-- The induced backward transport is retained as well. -/
theorem alignmentMediatorRoundTrip_backward
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (mediator : RelationalMediator context)
    (identity : Target) :
    (RelationalMediator.toExactTransport
      (IntrinsicCompatibleExactAlignment.toRelationalMediator
        (RelationalMediator.toIntrinsicCompatibleExactAlignment mediator))).backward
        identity = mediator.toExactTransport.backward identity :=
  mediator.toIntrinsicCompatibleExactAlignment.mediatorReconstruction_backward
    identity

end RelationalMediator

namespace IntrinsicCompatibleExactAlignment

/--
Passing from a compatible alignment to its canonical source-indexed mediator
and reconstructing again recovers the original forward correspondence.
-/
theorem relationalMediatorRoundTrip_forward
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (alignment : IntrinsicCompatibleExactAlignment context)
    (identity : Source) :
    (RelationalMediator.toIntrinsicCompatibleExactAlignment
      (IntrinsicCompatibleExactAlignment.toRelationalMediator alignment)).transport.forward
        identity = alignment.transport.forward identity :=
  alignment.mediatorReconstruction_forward identity

/-- The reconstructed backward correspondence is also pointwise unchanged. -/
theorem relationalMediatorRoundTrip_backward
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (alignment : IntrinsicCompatibleExactAlignment context)
    (identity : Target) :
    (RelationalMediator.toIntrinsicCompatibleExactAlignment
      (IntrinsicCompatibleExactAlignment.toRelationalMediator alignment)).transport.backward
        identity = alignment.transport.backward identity :=
  alignment.mediatorReconstruction_backward identity

end IntrinsicCompatibleExactAlignment

end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.RelationalMediator.toExactTransport_preservesRelation
#print axioms Alignment.GenesisReconstruction.RelationalMediator.toIntrinsicCompatibleExactAlignment
#print axioms Alignment.GenesisReconstruction.RelationalMediator.alignmentMediatorRoundTrip_forward
#print axioms Alignment.GenesisReconstruction.RelationalMediator.alignmentMediatorRoundTrip_backward
#print axioms Alignment.GenesisReconstruction.IntrinsicCompatibleExactAlignment.relationalMediatorRoundTrip_forward
#print axioms Alignment.GenesisReconstruction.IntrinsicCompatibleExactAlignment.relationalMediatorRoundTrip_backward
/- AXIOM_AUDIT_END -/