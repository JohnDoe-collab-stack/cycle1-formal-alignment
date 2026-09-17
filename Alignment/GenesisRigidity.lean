import Alignment.GenesisCharacterization

/-!
# Rigidity of genesis-preserving finite alignment

The finite genesis condition determines every freshly generated stratum, but it
does not by itself choose among exact correspondences already available on the
initial carriers.

This module localizes that ambiguity precisely. Pointwise uniqueness of exact
initial transports is equivalent to pointwise uniqueness of genesis-preserving
transports at every supplied finite depth. Thus finite generation introduces no
new alignment ambiguity, but it also cannot remove a symmetry already present
at the initial layer.

The result is constructive and pointwise. No function extensionality or
quotienting of transports is used.
-/

namespace Alignment
namespace GenesisReconstruction

universe uSource uTarget

/-- All exact transports between the initial carriers have the same forward map. -/
def InitialForwardRigid
    (Source : Type uSource)
    (Target : Type uTarget) : Prop :=
  ∀ first second : ExactTypeTransport Source Target,
    ∀ identity : Source,
      first.forward identity = second.forward identity

/--
All genesis-preserving exact transports at one finite depth have the same
forward map.
-/
def GenesisForwardRigid
    (Source : Type uSource)
    (Target : Type uTarget)
    (depth : Nat) : Prop :=
  ∀ first second :
      ExactTypeTransport
        (IteratedCarrier Source depth)
        (IteratedCarrier Target depth),
    PreservesGenesis first →
    PreservesGenesis second →
    ∀ identity : IteratedCarrier Source depth,
      first.forward identity = second.forward identity

/-- Pointwise agreement of initial transports is preserved by every finite lift. -/
theorem liftToDepth_forward_congr
    {Source : Type uSource}
    {Target : Type uTarget}
    (first second : ExactTypeTransport Source Target)
    (agreement :
      ∀ identity : Source,
        first.forward identity = second.forward identity) :
    (depth : Nat) →
      ∀ identity : IteratedCarrier Source depth,
        (liftToDepth first depth).forward identity =
          (liftToDepth second depth).forward identity
  | 0, identity => agreement identity
  | depth + 1, .inl prior =>
      congrArg Sum.inl
        (liftToDepth_forward_congr first second agreement depth prior)
  | _ + 1, .inr witness => by
      cases witness
      rfl

/-- Initial rigidity forces rigidity of every genesis-preserving finite transport. -/
theorem genesisForwardRigid_of_initialForwardRigid
    {Source : Type uSource}
    {Target : Type uTarget}
    (initialRigid : InitialForwardRigid Source Target)
    (depth : Nat) :
    GenesisForwardRigid Source Target depth := by
  intro first second firstPreserves secondPreserves identity
  calc
    first.forward identity =
        (liftToDepth
          (reconstructInitial first firstPreserves)
          depth).forward identity :=
      reconstruct_forward depth first firstPreserves identity
    _ = (liftToDepth
          (reconstructInitial second secondPreserves)
          depth).forward identity :=
      liftToDepth_forward_congr
        (reconstructInitial first firstPreserves)
        (reconstructInitial second secondPreserves)
        (initialRigid
          (reconstructInitial first firstPreserves)
          (reconstructInitial second secondPreserves))
        depth identity
    _ = second.forward identity :=
      (reconstruct_forward depth second secondPreserves identity).symm

/--
Rigidity at any finite depth reflects back to the initial carriers. Canonical
lifting therefore neither creates nor destroys pointwise transport ambiguity.
-/
theorem initialForwardRigid_of_genesisForwardRigid
    {Source : Type uSource}
    {Target : Type uTarget}
    (depth : Nat)
    (terminalRigid : GenesisForwardRigid Source Target depth) :
    InitialForwardRigid Source Target := by
  intro first second identity
  have terminalAgreement :=
    terminalRigid
      (liftToDepth first depth)
      (liftToDepth second depth)
      (liftToDepth_preservesGenesis first depth)
      (liftToDepth_preservesGenesis second depth)
      (IteratedCarrier.embedInitial depth identity)
  have firstBase :
      (liftToDepth first 0).forward identity = first.forward identity := by
    rfl
  have secondBase :
      (liftToDepth second 0).forward identity = second.forward identity := by
    rfl
  have firstNaturalityRaw :=
    liftToDepth_embedFrom
      first
      (DepthExtension.zeroTo depth)
      identity
  have secondNaturalityRaw :=
    liftToDepth_embedFrom
      second
      (DepthExtension.zeroTo depth)
      identity
  rw [firstBase] at firstNaturalityRaw
  rw [secondBase] at secondNaturalityRaw
  have firstNaturality :
      (liftToDepth first depth).forward
          (IteratedCarrier.embedInitial depth identity) =
        IteratedCarrier.embedInitial depth (first.forward identity) := by
    exact firstNaturalityRaw
  have secondNaturality :
      (liftToDepth second depth).forward
          (IteratedCarrier.embedInitial depth identity) =
        IteratedCarrier.embedInitial depth (second.forward identity) := by
    exact secondNaturalityRaw
  have embeddedAgreement :
      IteratedCarrier.embedInitial depth (first.forward identity) =
        IteratedCarrier.embedInitial depth (second.forward identity) := by
    calc
      IteratedCarrier.embedInitial depth (first.forward identity) =
          (liftToDepth first depth).forward
            (IteratedCarrier.embedInitial depth identity) :=
        firstNaturality.symm
      _ = (liftToDepth second depth).forward
            (IteratedCarrier.embedInitial depth identity) :=
        terminalAgreement
      _ = IteratedCarrier.embedInitial depth (second.forward identity) :=
        secondNaturality
  exact IteratedCarrier.embedInitial_injective depth embeddedAgreement

/--
Initial pointwise rigidity is equivalent to pointwise rigidity of
all genesis-preserving transports at any chosen finite depth.
-/
theorem initialForwardRigid_iff_genesisForwardRigid
    {Source : Type uSource}
    {Target : Type uTarget}
    (depth : Nat) :
    InitialForwardRigid Source Target ↔
      GenesisForwardRigid Source Target depth := by
  constructor
  · intro initialRigid
    exact genesisForwardRigid_of_initialForwardRigid initialRigid depth
  · intro terminalRigid
    exact initialForwardRigid_of_genesisForwardRigid depth terminalRigid

/-- Forward rigidity also forces pointwise uniqueness of the backward maps. -/
theorem genesisBackward_unique_of_forwardRigid
    {Source : Type uSource}
    {Target : Type uTarget}
    {depth : Nat}
    (rigid : GenesisForwardRigid Source Target depth)
    (first second :
      ExactTypeTransport
        (IteratedCarrier Source depth)
        (IteratedCarrier Target depth))
    (firstPreserves : PreservesGenesis first)
    (secondPreserves : PreservesGenesis second)
    (identity : IteratedCarrier Target depth) :
    first.backward identity = second.backward identity :=
  ExactTypeTransport.backward_eq_of_forward_eq
    first second
    (rigid first second firstPreserves secondPreserves)
    identity

end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.InitialForwardRigid
#print axioms Alignment.GenesisReconstruction.GenesisForwardRigid
#print axioms Alignment.GenesisReconstruction.liftToDepth_forward_congr
#print axioms Alignment.GenesisReconstruction.genesisForwardRigid_of_initialForwardRigid
#print axioms Alignment.GenesisReconstruction.initialForwardRigid_of_genesisForwardRigid
#print axioms Alignment.GenesisReconstruction.initialForwardRigid_iff_genesisForwardRigid
#print axioms Alignment.GenesisReconstruction.genesisBackward_unique_of_forwardRigid
/- AXIOM_AUDIT_END -/
