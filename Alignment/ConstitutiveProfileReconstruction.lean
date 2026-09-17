import Alignment.ConstitutiveProfileRigidity

/-!
# Reconstruction from constitutive profile resolvers

A separating constitutive profile makes compatible alignment candidates unique.
This module addresses existence one step earlier than `ExactTypeTransport`.

Instead of assuming an exact transport and its inverse laws, we assume only two
positive resolver maps between the initial carriers. Both maps must preserve the
same constitutive profiles, and the profiles must separate identities on both
sides. The inverse laws are then derived from profile preservation and
separation.

Thus an exact initial alignment can be constructed from structural matching data
without postulating bijectivity. Its canonical finite lift preserves genesis,
and every other terminal exact transport with the same reconstructed profile
behavior agrees with that lift pointwise.

The remaining open layer is upstream: constructing the resolver maps themselves
from richer relational data rather than supplying them as positive witnesses.
-/

namespace Alignment
namespace GenesisReconstruction

universe uSource uTarget uProbe uValue

/--
Positive bidirectional matching data between two initial carriers. Exact
round-trips are deliberately not fields of this structure.
-/
structure BidirectionalProfileResolver
    (Source : Type uSource)
    (Target : Type uTarget)
    (Probe : Type uProbe)
    (Value : Type uValue) where
  sourceProfile : Source → Probe → Value
  targetProfile : Target → Probe → Value
  forward : Source → Target
  backward : Target → Source
  sourceSeparates : ProfileSeparates sourceProfile
  targetSeparates : ProfileSeparates targetProfile
  forwardPreserves : PreservesProfile sourceProfile targetProfile forward
  backwardPreserves : PreservesProfile targetProfile sourceProfile backward

namespace BidirectionalProfileResolver

/-- Profile separation derives the source-side round-trip. -/
theorem forwardBackward
    {Source : Type uSource}
    {Target : Type uTarget}
    {Probe : Type uProbe}
    {Value : Type uValue}
    (resolver : BidirectionalProfileResolver Source Target Probe Value)
    (identity : Source) :
    resolver.backward (resolver.forward identity) = identity := by
  apply resolver.sourceSeparates
  intro probe
  calc
    resolver.sourceProfile
        (resolver.backward (resolver.forward identity)) probe =
      resolver.targetProfile (resolver.forward identity) probe :=
        resolver.backwardPreserves (resolver.forward identity) probe
    _ = resolver.sourceProfile identity probe :=
      resolver.forwardPreserves identity probe

/-- Profile separation derives the target-side round-trip. -/
theorem backwardForward
    {Source : Type uSource}
    {Target : Type uTarget}
    {Probe : Type uProbe}
    {Value : Type uValue}
    (resolver : BidirectionalProfileResolver Source Target Probe Value)
    (identity : Target) :
    resolver.forward (resolver.backward identity) = identity := by
  apply resolver.targetSeparates
  intro probe
  calc
    resolver.targetProfile
        (resolver.forward (resolver.backward identity)) probe =
      resolver.sourceProfile (resolver.backward identity) probe :=
        resolver.forwardPreserves (resolver.backward identity) probe
    _ = resolver.targetProfile identity probe :=
      resolver.backwardPreserves identity probe

/-- Construct the exact initial transport from profile-compatible resolvers. -/
def toExactTransport
    {Source : Type uSource}
    {Target : Type uTarget}
    {Probe : Type uProbe}
    {Value : Type uValue}
    (resolver : BidirectionalProfileResolver Source Target Probe Value) :
    ExactTypeTransport Source Target :=
  { forward := resolver.forward
    backward := resolver.backward
    forwardBackward := resolver.forwardBackward
    backwardForward := resolver.backwardForward }

/-- The constructed exact transport retains the supplied forward profile law. -/
theorem toExactTransport_preservesProfile
    {Source : Type uSource}
    {Target : Type uTarget}
    {Probe : Type uProbe}
    {Value : Type uValue}
    (resolver : BidirectionalProfileResolver Source Target Probe Value) :
    PreservesProfile
      resolver.sourceProfile
      resolver.targetProfile
      resolver.toExactTransport.forward :=
  resolver.forwardPreserves

/-- Lift the reconstructed initial alignment through finite constitutive depth. -/
def finiteTransport
    {Source : Type uSource}
    {Target : Type uTarget}
    {Probe : Type uProbe}
    {Value : Type uValue}
    (resolver : BidirectionalProfileResolver Source Target Probe Value)
    (depth : Nat) :
    ExactTypeTransport
      (IteratedCarrier Source depth)
      (IteratedCarrier Target depth) :=
  liftToDepth resolver.toExactTransport depth

/-- Every finite transport reconstructed from profiles preserves genesis. -/
theorem finiteTransport_preservesGenesis
    {Source : Type uSource}
    {Target : Type uTarget}
    {Probe : Type uProbe}
    {Value : Type uValue}
    (resolver : BidirectionalProfileResolver Source Target Probe Value)
    (depth : Nat) :
    PreservesGenesis (resolver.finiteTransport depth) :=
  liftToDepth_preservesGenesis resolver.toExactTransport depth

/--
Every genesis-preserving terminal candidate whose reconstructed initial map
preserves the same profiles agrees with the finite transport built directly
from the resolvers.
-/
theorem finiteTransport_forward_unique
    {Source : Type uSource}
    {Target : Type uTarget}
    {Probe : Type uProbe}
    {Value : Type uValue}
    {depth : Nat}
    (resolver : BidirectionalProfileResolver Source Target Probe Value)
    (candidate :
      ExactTypeTransport
        (IteratedCarrier Source depth)
        (IteratedCarrier Target depth))
    (candidateGenesis : PreservesGenesis candidate)
    (candidateProfile :
      ReconstructedInitialPreservesProfile
        resolver.sourceProfile
        resolver.targetProfile
        candidate
        candidateGenesis)
    (identity : IteratedCarrier Source depth) :
    candidate.forward identity =
      (resolver.finiteTransport depth).forward identity := by
  have initialAgreement :
      ∀ initialIdentity : Source,
        (reconstructInitial candidate candidateGenesis).forward initialIdentity =
          resolver.toExactTransport.forward initialIdentity := by
    intro initialIdentity
    exact
      profilePreserving_forward_unique
        resolver.sourceProfile
        resolver.targetProfile
        resolver.targetSeparates
        (reconstructInitial candidate candidateGenesis).forward
        resolver.toExactTransport.forward
        candidateProfile
        resolver.toExactTransport_preservesProfile
        initialIdentity
  calc
    candidate.forward identity =
        (liftToDepth
          (reconstructInitial candidate candidateGenesis)
          depth).forward identity :=
      reconstruct_forward depth candidate candidateGenesis identity
    _ = (liftToDepth resolver.toExactTransport depth).forward identity :=
      liftToDepth_forward_congr
        (reconstructInitial candidate candidateGenesis)
        resolver.toExactTransport
        initialAgreement
        depth
        identity

/-- Backward uniqueness follows from exactness once the forward map is forced. -/
theorem finiteTransport_backward_unique
    {Source : Type uSource}
    {Target : Type uTarget}
    {Probe : Type uProbe}
    {Value : Type uValue}
    {depth : Nat}
    (resolver : BidirectionalProfileResolver Source Target Probe Value)
    (candidate :
      ExactTypeTransport
        (IteratedCarrier Source depth)
        (IteratedCarrier Target depth))
    (candidateGenesis : PreservesGenesis candidate)
    (candidateProfile :
      ReconstructedInitialPreservesProfile
        resolver.sourceProfile
        resolver.targetProfile
        candidate
        candidateGenesis)
    (identity : IteratedCarrier Target depth) :
    candidate.backward identity =
      (resolver.finiteTransport depth).backward identity :=
  ExactTypeTransport.backward_eq_of_forward_eq
    candidate
    (resolver.finiteTransport depth)
    (resolver.finiteTransport_forward_unique
      candidate
      candidateGenesis
      candidateProfile)
    identity

end BidirectionalProfileResolver
end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.BidirectionalProfileResolver
#print axioms Alignment.GenesisReconstruction.BidirectionalProfileResolver.forwardBackward
#print axioms Alignment.GenesisReconstruction.BidirectionalProfileResolver.backwardForward
#print axioms Alignment.GenesisReconstruction.BidirectionalProfileResolver.toExactTransport
#print axioms Alignment.GenesisReconstruction.BidirectionalProfileResolver.finiteTransport
#print axioms Alignment.GenesisReconstruction.BidirectionalProfileResolver.finiteTransport_preservesGenesis
#print axioms Alignment.GenesisReconstruction.BidirectionalProfileResolver.finiteTransport_forward_unique
#print axioms Alignment.GenesisReconstruction.BidirectionalProfileResolver.finiteTransport_backward_unique
/- AXIOM_AUDIT_END -/
