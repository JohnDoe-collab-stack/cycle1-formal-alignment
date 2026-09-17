import Alignment.GenesisRigidity

/-!
# Constitutive profile rigidity for alignment at arbitrary natural depth

Genesis preservation localizes all remaining natural-depth alignment ambiguity in the
initial carriers. This module gives a structural condition that can remove that
ambiguity without postulating a common carrier of identities.

Each initial carrier is observed through the same probe and value types. A
profile is faithful when its complete family of probe values separates
identities. Two candidate transports are profile-compatible when they preserve
all probe values. Under target-side separation, profile-compatible candidates
have the same forward map.

Combining this with genesis reconstruction at arbitrary natural depth gives uniqueness of the whole
terminal alignment among candidates whose reconstructed initial transports
preserve the constitutive profiles.

The profile interface is deliberately weaker than a common identity index. It
states how identities are structurally distinguished, not which identity on one
side corresponds to which identity on the other. Existence of a compatible
transport remains a separate positive obligation.
-/

namespace Alignment
namespace GenesisReconstruction

universe uSource uTarget uProbe uValue

/-- A complete profile separates identities when equal probe values force identity. -/
def ProfileSeparates
    {Carrier : Type uSource}
    {Probe : Type uProbe}
    {Value : Type uValue}
    (profile : Carrier → Probe → Value) : Prop :=
  ∀ first second : Carrier,
    (∀ probe : Probe, profile first probe = profile second probe) →
      first = second

/-- A map preserves all constitutive profile observations pointwise. -/
def PreservesProfile
    {Source : Type uSource}
    {Target : Type uTarget}
    {Probe : Type uProbe}
    {Value : Type uValue}
    (sourceProfile : Source → Probe → Value)
    (targetProfile : Target → Probe → Value)
    (forward : Source → Target) : Prop :=
  ∀ identity : Source,
    ∀ probe : Probe,
      targetProfile (forward identity) probe =
        sourceProfile identity probe

/--
A separating target profile makes every profile-preserving forward map unique.
No bijectivity assumption is needed for this uniqueness statement.
-/
theorem profilePreserving_forward_unique
    {Source : Type uSource}
    {Target : Type uTarget}
    {Probe : Type uProbe}
    {Value : Type uValue}
    (sourceProfile : Source → Probe → Value)
    (targetProfile : Target → Probe → Value)
    (targetSeparates : ProfileSeparates targetProfile)
    (first second : Source → Target)
    (firstPreserves : PreservesProfile sourceProfile targetProfile first)
    (secondPreserves : PreservesProfile sourceProfile targetProfile second)
    (identity : Source) :
    first identity = second identity := by
  apply targetSeparates
  intro probe
  calc
    targetProfile (first identity) probe =
        sourceProfile identity probe :=
      firstPreserves identity probe
    _ = targetProfile (second identity) probe :=
      (secondPreserves identity probe).symm

/--
Profile preservation imposed on the initial transport reconstructed from one
terminal candidate at an arbitrary natural depth.
-/
def ReconstructedInitialPreservesProfile
    {Source : Type uSource}
    {Target : Type uTarget}
    {Probe : Type uProbe}
    {Value : Type uValue}
    {depth : Nat}
    (sourceProfile : Source → Probe → Value)
    (targetProfile : Target → Probe → Value)
    (transport :
      ExactTypeTransport
        (IteratedCarrier Source depth)
        (IteratedCarrier Target depth))
    (preservesGenesis : PreservesGenesis transport) : Prop :=
  PreservesProfile
    sourceProfile
    targetProfile
    (reconstructInitial transport preservesGenesis).forward

/--
A separating constitutive profile removes all remaining forward ambiguity from
genesis-preserving alignment at arbitrary natural depth.
-/
theorem genesis_forward_unique_of_profileSeparation
    {Source : Type uSource}
    {Target : Type uTarget}
    {Probe : Type uProbe}
    {Value : Type uValue}
    {depth : Nat}
    (sourceProfile : Source → Probe → Value)
    (targetProfile : Target → Probe → Value)
    (targetSeparates : ProfileSeparates targetProfile)
    (first second :
      ExactTypeTransport
        (IteratedCarrier Source depth)
        (IteratedCarrier Target depth))
    (firstGenesis : PreservesGenesis first)
    (secondGenesis : PreservesGenesis second)
    (firstProfile :
      ReconstructedInitialPreservesProfile
        sourceProfile targetProfile first firstGenesis)
    (secondProfile :
      ReconstructedInitialPreservesProfile
        sourceProfile targetProfile second secondGenesis)
    (identity : IteratedCarrier Source depth) :
    first.forward identity = second.forward identity := by
  have initialAgreement :
      ∀ initialIdentity : Source,
        (reconstructInitial first firstGenesis).forward initialIdentity =
          (reconstructInitial second secondGenesis).forward initialIdentity := by
    intro initialIdentity
    exact
      profilePreserving_forward_unique
        sourceProfile
        targetProfile
        targetSeparates
        (reconstructInitial first firstGenesis).forward
        (reconstructInitial second secondGenesis).forward
        firstProfile
        secondProfile
        initialIdentity
  calc
    first.forward identity =
        (liftToDepth
          (reconstructInitial first firstGenesis)
          depth).forward identity :=
      reconstruct_forward depth first firstGenesis identity
    _ = (liftToDepth
          (reconstructInitial second secondGenesis)
          depth).forward identity :=
      liftToDepth_forward_congr
        (reconstructInitial first firstGenesis)
        (reconstructInitial second secondGenesis)
        initialAgreement
        depth
        identity
    _ = second.forward identity :=
      (reconstruct_forward depth second secondGenesis identity).symm

/-- The backward maps are forced as soon as the profile-compatible forward map is. -/
theorem genesis_backward_unique_of_profileSeparation
    {Source : Type uSource}
    {Target : Type uTarget}
    {Probe : Type uProbe}
    {Value : Type uValue}
    {depth : Nat}
    (sourceProfile : Source → Probe → Value)
    (targetProfile : Target → Probe → Value)
    (targetSeparates : ProfileSeparates targetProfile)
    (first second :
      ExactTypeTransport
        (IteratedCarrier Source depth)
        (IteratedCarrier Target depth))
    (firstGenesis : PreservesGenesis first)
    (secondGenesis : PreservesGenesis second)
    (firstProfile :
      ReconstructedInitialPreservesProfile
        sourceProfile targetProfile first firstGenesis)
    (secondProfile :
      ReconstructedInitialPreservesProfile
        sourceProfile targetProfile second secondGenesis)
    (identity : IteratedCarrier Target depth) :
    first.backward identity = second.backward identity :=
  ExactTypeTransport.backward_eq_of_forward_eq
    first
    second
    (genesis_forward_unique_of_profileSeparation
      sourceProfile
      targetProfile
      targetSeparates
      first
      second
      firstGenesis
      secondGenesis
      firstProfile
      secondProfile)
    identity

end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.ProfileSeparates
#print axioms Alignment.GenesisReconstruction.PreservesProfile
#print axioms Alignment.GenesisReconstruction.profilePreserving_forward_unique
#print axioms Alignment.GenesisReconstruction.ReconstructedInitialPreservesProfile
#print axioms Alignment.GenesisReconstruction.genesis_forward_unique_of_profileSeparation
#print axioms Alignment.GenesisReconstruction.genesis_backward_unique_of_profileSeparation
/- AXIOM_AUDIT_END -/
