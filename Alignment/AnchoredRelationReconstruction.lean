import Alignment.ConstitutiveProfileReconstruction

/-!
# Reconstruction from anchored constitutive relations

Constitutive profiles can be obtained from relations rather than supplied as
opaque labels. This module specializes profile reconstruction to observations of
how identities stand in relation to a shared family of structural anchors.

The two carriers may be different types and need not share an identity index.
They share only an anchor type and an observation value type. Each side chooses
its own concrete realization of every anchor. An identity is profiled by the
values of the local relation from each realized anchor to that identity.

If these anchored relational profiles separate identities on both sides, and
positive forward and backward resolvers preserve all anchored observations,
then the exact initial transport and every lift to an arbitrary natural-number depth that preserves genesis are
constructed automatically.

The anchor family need not enumerate the carrier. Its role is observational: it
must only be rich enough for the resulting relational profiles to separate the
identities relevant to alignment.
-/

namespace Alignment
namespace GenesisReconstruction

universe uSource uTarget uAnchor uValue

/--
Bidirectional matching data whose structural compatibility is expressed only
through anchored local relations. Exact inverse laws are not fields.
-/
structure BidirectionalAnchoredRelationResolver
    (Source : Type uSource)
    (Target : Type uTarget)
    (Anchor : Type uAnchor)
    (Value : Type uValue) where
  sourceRelation : Source → Source → Value
  targetRelation : Target → Target → Value
  sourceAnchor : Anchor → Source
  targetAnchor : Anchor → Target
  forward : Source → Target
  backward : Target → Source
  sourceSeparates :
    ProfileSeparates
      (fun identity anchor => sourceRelation (sourceAnchor anchor) identity)
  targetSeparates :
    ProfileSeparates
      (fun identity anchor => targetRelation (targetAnchor anchor) identity)
  forwardPreservesAnchors :
    ∀ identity : Source,
      ∀ anchor : Anchor,
        targetRelation (targetAnchor anchor) (forward identity) =
          sourceRelation (sourceAnchor anchor) identity
  backwardPreservesAnchors :
    ∀ identity : Target,
      ∀ anchor : Anchor,
        sourceRelation (sourceAnchor anchor) (backward identity) =
          targetRelation (targetAnchor anchor) identity

namespace BidirectionalAnchoredRelationResolver

/-- The source constitutive profile induced by relations to realized anchors. -/
def sourceProfile
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    (resolver :
      BidirectionalAnchoredRelationResolver Source Target Anchor Value) :
    Source → Anchor → Value :=
  fun identity anchor =>
    resolver.sourceRelation (resolver.sourceAnchor anchor) identity

/-- The target constitutive profile induced by relations to realized anchors. -/
def targetProfile
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    (resolver :
      BidirectionalAnchoredRelationResolver Source Target Anchor Value) :
    Target → Anchor → Value :=
  fun identity anchor =>
    resolver.targetRelation (resolver.targetAnchor anchor) identity

/-- Anchored relational matching is an instance of bidirectional profile matching. -/
def toProfileResolver
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    (resolver :
      BidirectionalAnchoredRelationResolver Source Target Anchor Value) :
    BidirectionalProfileResolver Source Target Anchor Value :=
  { sourceProfile := resolver.sourceProfile
    targetProfile := resolver.targetProfile
    forward := resolver.forward
    backward := resolver.backward
    sourceSeparates := resolver.sourceSeparates
    targetSeparates := resolver.targetSeparates
    forwardPreserves := resolver.forwardPreservesAnchors
    backwardPreserves := resolver.backwardPreservesAnchors }

/-- Exact initial alignment reconstructed from anchored constitutive relations. -/
def toExactTransport
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    (resolver :
      BidirectionalAnchoredRelationResolver Source Target Anchor Value) :
    ExactTypeTransport Source Target :=
  resolver.toProfileResolver.toExactTransport

/-- The relationally reconstructed initial transport preserves every anchor profile. -/
theorem toExactTransport_preservesAnchors
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    (resolver :
      BidirectionalAnchoredRelationResolver Source Target Anchor Value)
    (identity : Source)
    (anchor : Anchor) :
    resolver.targetRelation
        (resolver.targetAnchor anchor)
        (resolver.toExactTransport.forward identity) =
      resolver.sourceRelation
        (resolver.sourceAnchor anchor)
        identity :=
  resolver.forwardPreservesAnchors identity anchor

/-- Canonical alignment at any requested natural-number depth induced by the anchored relational reconstruction. -/
def finiteTransport
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    (resolver :
      BidirectionalAnchoredRelationResolver Source Target Anchor Value)
    (depth : Nat) :
    ExactTypeTransport
      (IteratedCarrier Source depth)
      (IteratedCarrier Target depth) :=
  resolver.toProfileResolver.finiteTransport depth

/-- Anchored relational reconstruction automatically yields genesis preservation. -/
theorem finiteTransport_preservesGenesis
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    (resolver :
      BidirectionalAnchoredRelationResolver Source Target Anchor Value)
    (depth : Nat) :
    PreservesGenesis (resolver.finiteTransport depth) :=
  resolver.toProfileResolver.finiteTransport_preservesGenesis depth

end BidirectionalAnchoredRelationResolver
end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.BidirectionalAnchoredRelationResolver
#print axioms Alignment.GenesisReconstruction.BidirectionalAnchoredRelationResolver.sourceProfile
#print axioms Alignment.GenesisReconstruction.BidirectionalAnchoredRelationResolver.targetProfile
#print axioms Alignment.GenesisReconstruction.BidirectionalAnchoredRelationResolver.toProfileResolver
#print axioms Alignment.GenesisReconstruction.BidirectionalAnchoredRelationResolver.toExactTransport
#print axioms Alignment.GenesisReconstruction.BidirectionalAnchoredRelationResolver.toExactTransport_preservesAnchors
#print axioms Alignment.GenesisReconstruction.BidirectionalAnchoredRelationResolver.finiteTransport
#print axioms Alignment.GenesisReconstruction.BidirectionalAnchoredRelationResolver.finiteTransport_preservesGenesis
/- AXIOM_AUDIT_END -/
