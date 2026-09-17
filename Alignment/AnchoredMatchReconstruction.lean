import Alignment.AnchoredRelationReconstruction

/-!
# Reconstruction from structurally defined anchored matches

The anchored relation layer can be weakened further. Instead of taking forward
and backward resolver functions as primitive data, this module first defines a
matching relation solely from anchored constitutive observations.

A context contains two local relational structures, local realizations of a
shared anchor family, and separation of identities by the resulting anchored
profiles. A source identity and a target identity match when all anchored
observations agree.

Profile separation makes such matches unique on either side. Totality is kept
constructive: for every identity, a matching identity on the other side is
supplied as data in a subtype. From these positive witnesses, the forward and
backward maps are projected, their round-trips are derived from match uniqueness,
and an exact transport is constructed.

Thus the alignment map is no longer an unconstrained primitive. The remaining
existence obligation is explicit and structural: the anchored match relation
must be total in both directions.
-/

namespace Alignment
namespace GenesisReconstruction

universe uSource uTarget uAnchor uValue

/--
Relational data sufficient to define when identities from two distinct carriers
have the same anchored constitutive profile.
-/
structure AnchoredRelationContext
    (Source : Type uSource)
    (Target : Type uTarget)
    (Anchor : Type uAnchor)
    (Value : Type uValue) where
  sourceRelation : Source → Source → Value
  targetRelation : Target → Target → Value
  sourceAnchor : Anchor → Source
  targetAnchor : Anchor → Target
  sourceSeparates :
    ProfileSeparates
      (fun identity anchor => sourceRelation (sourceAnchor anchor) identity)
  targetSeparates :
    ProfileSeparates
      (fun identity anchor => targetRelation (targetAnchor anchor) identity)

namespace AnchoredRelationContext

/-- Two identities match when every anchored constitutive observation agrees. -/
def Matches
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    (context : AnchoredRelationContext Source Target Anchor Value)
    (source : Source)
    (target : Target) : Prop :=
  ∀ anchor : Anchor,
    context.targetRelation (context.targetAnchor anchor) target =
      context.sourceRelation (context.sourceAnchor anchor) source

/-- A source identity has at most one target match. -/
theorem target_unique
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    (context : AnchoredRelationContext Source Target Anchor Value)
    (source : Source)
    (first second : Target)
    (firstMatches : context.Matches source first)
    (secondMatches : context.Matches source second) :
    first = second := by
  apply context.targetSeparates
  intro anchor
  calc
    context.targetRelation (context.targetAnchor anchor) first =
        context.sourceRelation (context.sourceAnchor anchor) source :=
      firstMatches anchor
    _ = context.targetRelation (context.targetAnchor anchor) second :=
      (secondMatches anchor).symm

/-- A target identity has at most one source match. -/
theorem source_unique
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    (context : AnchoredRelationContext Source Target Anchor Value)
    (target : Target)
    (first second : Source)
    (firstMatches : context.Matches first target)
    (secondMatches : context.Matches second target) :
    first = second := by
  apply context.sourceSeparates
  intro anchor
  calc
    context.sourceRelation (context.sourceAnchor anchor) first =
        context.targetRelation (context.targetAnchor anchor) target :=
      (firstMatches anchor).symm
    _ = context.sourceRelation (context.sourceAnchor anchor) second :=
      secondMatches anchor

end AnchoredRelationContext

/--
Positive totality witnesses for the structurally defined match relation. The
chosen identities carry proofs that they satisfy `Matches`.
-/
structure TotalAnchoredMatching
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    (context : AnchoredRelationContext Source Target Anchor Value) where
  forwardWitness :
    (source : Source) → { target : Target // context.Matches source target }
  backwardWitness :
    (target : Target) → { source : Source // context.Matches source target }

namespace TotalAnchoredMatching

/-- Forward map projected from the positive matching witness. -/
def forward
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : TotalAnchoredMatching context) :
    Source → Target :=
  fun source => (matching.forwardWitness source).1

/-- Backward map projected from the positive matching witness. -/
def backward
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : TotalAnchoredMatching context) :
    Target → Source :=
  fun target => (matching.backwardWitness target).1

/-- The projected forward map satisfies the structurally defined match relation. -/
theorem forward_matches
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : TotalAnchoredMatching context)
    (source : Source) :
    context.Matches source (matching.forward source) :=
  (matching.forwardWitness source).2

/-- The projected backward map satisfies the structurally defined match relation. -/
theorem backward_matches
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : TotalAnchoredMatching context)
    (target : Target) :
    context.Matches (matching.backward target) target :=
  (matching.backwardWitness target).2

/-- Match uniqueness derives the source round-trip. -/
theorem forwardBackward
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : TotalAnchoredMatching context)
    (source : Source) :
    matching.backward (matching.forward source) = source := by
  apply context.source_unique (matching.forward source)
  · exact matching.backward_matches (matching.forward source)
  · exact matching.forward_matches source

/-- Match uniqueness derives the target round-trip. -/
theorem backwardForward
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : TotalAnchoredMatching context)
    (target : Target) :
    matching.forward (matching.backward target) = target := by
  apply context.target_unique (matching.backward target)
  · exact matching.forward_matches (matching.backward target)
  · exact matching.backward_matches target

/-- Exact initial transport reconstructed from total structural matching. -/
def toExactTransport
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : TotalAnchoredMatching context) :
    ExactTypeTransport Source Target :=
  { forward := matching.forward
    backward := matching.backward
    forwardBackward := matching.forwardBackward
    backwardForward := matching.backwardForward }

/-- Any two total matchings for one separating context have the same forward map. -/
theorem forward_unique
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (first second : TotalAnchoredMatching context)
    (source : Source) :
    first.forward source = second.forward source :=
  context.target_unique
    source
    (first.forward source)
    (second.forward source)
    (first.forward_matches source)
    (second.forward_matches source)

/-- Any two total matchings for one separating context have the same backward map. -/
theorem backward_unique
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (first second : TotalAnchoredMatching context)
    (target : Target) :
    first.backward target = second.backward target :=
  context.source_unique
    target
    (first.backward target)
    (second.backward target)
    (first.backward_matches target)
    (second.backward_matches target)

/-- Convert total structural matching into the earlier anchored resolver interface. -/
def toAnchoredResolver
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : TotalAnchoredMatching context) :
    BidirectionalAnchoredRelationResolver Source Target Anchor Value :=
  { sourceRelation := context.sourceRelation
    targetRelation := context.targetRelation
    sourceAnchor := context.sourceAnchor
    targetAnchor := context.targetAnchor
    forward := matching.forward
    backward := matching.backward
    sourceSeparates := context.sourceSeparates
    targetSeparates := context.targetSeparates
    forwardPreservesAnchors := matching.forward_matches
    backwardPreservesAnchors := by
      intro identity anchor
      exact (matching.backward_matches identity anchor).symm }

/-- Canonical finite alignment reconstructed from total anchored matching. -/
def finiteTransport
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : TotalAnchoredMatching context)
    (depth : Nat) :
    ExactTypeTransport
      (IteratedCarrier Source depth)
      (IteratedCarrier Target depth) :=
  liftToDepth matching.toExactTransport depth

/-- Structural matching propagates coherently through every finite genesis depth. -/
theorem finiteTransport_preservesGenesis
    {Source : Type uSource}
    {Target : Type uTarget}
    {Anchor : Type uAnchor}
    {Value : Type uValue}
    {context : AnchoredRelationContext Source Target Anchor Value}
    (matching : TotalAnchoredMatching context)
    (depth : Nat) :
    PreservesGenesis (matching.finiteTransport depth) :=
  liftToDepth_preservesGenesis matching.toExactTransport depth

end TotalAnchoredMatching
end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.AnchoredRelationContext
#print axioms Alignment.GenesisReconstruction.AnchoredRelationContext.Matches
#print axioms Alignment.GenesisReconstruction.AnchoredRelationContext.target_unique
#print axioms Alignment.GenesisReconstruction.AnchoredRelationContext.source_unique
#print axioms Alignment.GenesisReconstruction.TotalAnchoredMatching
#print axioms Alignment.GenesisReconstruction.TotalAnchoredMatching.forward
#print axioms Alignment.GenesisReconstruction.TotalAnchoredMatching.backward
#print axioms Alignment.GenesisReconstruction.TotalAnchoredMatching.forwardBackward
#print axioms Alignment.GenesisReconstruction.TotalAnchoredMatching.backwardForward
#print axioms Alignment.GenesisReconstruction.TotalAnchoredMatching.toExactTransport
#print axioms Alignment.GenesisReconstruction.TotalAnchoredMatching.forward_unique
#print axioms Alignment.GenesisReconstruction.TotalAnchoredMatching.backward_unique
#print axioms Alignment.GenesisReconstruction.TotalAnchoredMatching.toAnchoredResolver
#print axioms Alignment.GenesisReconstruction.TotalAnchoredMatching.finiteTransport
#print axioms Alignment.GenesisReconstruction.TotalAnchoredMatching.finiteTransport_preservesGenesis
/- AXIOM_AUDIT_END -/
