import Alignment.GenesisReconstruction

/-!
# Characterization of genesis-preserving transports at arbitrary natural depth

A terminal exact transport between two constitutive carriers at an arbitrary natural depth is
reconstructible from the initial carriers exactly when it preserves every
fresh-generation stratum.

This packages the reconstruction machinery as a two-way characterization. It
still does not infer a semantic correspondence between initially unrelated
identities. The reconstructed initial transport is the correspondence already
encoded by the terminal exact transport once the fresh strata are required to
remain fixed by genesis depth.
-/

namespace Alignment
namespace GenesisReconstruction

universe uSource uTarget

/--
A terminal transport is reconstructible from an exact transport between the
initial carriers when both of its directions agree pointwise with the canonical
finite lift of that initial transport.
-/
def ReconstructibleFromInitial
    {Source : Type uSource}
    {Target : Type uTarget}
    {depth : Nat}
    (transport :
      ExactTypeTransport
        (IteratedCarrier Source depth)
        (IteratedCarrier Target depth)) : Prop :=
  ∃ initial : ExactTypeTransport Source Target,
    (∀ identity : IteratedCarrier Source depth,
      transport.forward identity =
        (liftToDepth initial depth).forward identity) ∧
    (∀ identity : IteratedCarrier Target depth,
      transport.backward identity =
        (liftToDepth initial depth).backward identity)

/-- Genesis preservation supplies a reconstructed initial alignment. -/
theorem reconstructible_of_preservesGenesis
    {Source : Type uSource}
    {Target : Type uTarget}
    {depth : Nat}
    (transport :
      ExactTypeTransport
        (IteratedCarrier Source depth)
        (IteratedCarrier Target depth))
    (preserves : PreservesGenesis transport) :
    ReconstructibleFromInitial transport := by
  refine ⟨reconstructInitial transport preserves, ?_, ?_⟩
  · exact reconstruct_forward depth transport preserves
  · exact reconstruct_backward depth transport preserves

/-- A canonical lift to the chosen natural depth preserves every fresh-generation stratum. -/
theorem preservesGenesis_of_reconstructible
    {Source : Type uSource}
    {Target : Type uTarget}
    {depth : Nat}
    (transport :
      ExactTypeTransport
        (IteratedCarrier Source depth)
        (IteratedCarrier Target depth))
    (reconstructible : ReconstructibleFromInitial transport) :
    PreservesGenesis transport := by
  rcases reconstructible with ⟨initial, forwardAgreement, _⟩
  intro birth extension
  calc
    transport.forward
        (IteratedCarrier.embedFrom extension
          (@IteratedCarrier.freshAtStep Source birth)) =
      (liftToDepth initial depth).forward
        (IteratedCarrier.embedFrom extension
          (@IteratedCarrier.freshAtStep Source birth)) :=
      forwardAgreement _
    _ = IteratedCarrier.embedFrom extension
          (@IteratedCarrier.freshAtStep Target birth) :=
      liftToDepth_preservesGenesis initial depth extension

/--
Exact transports at arbitrary natural depth preserve genesis if and only if they are canonical
lifts of an exact alignment between the initial carriers.
-/
theorem preservesGenesis_iff_reconstructible
    {Source : Type uSource}
    {Target : Type uTarget}
    {depth : Nat}
    (transport :
      ExactTypeTransport
        (IteratedCarrier Source depth)
        (IteratedCarrier Target depth)) :
    PreservesGenesis transport ↔ ReconstructibleFromInitial transport := by
  constructor
  · exact reconstructible_of_preservesGenesis transport
  · exact preservesGenesis_of_reconstructible transport

end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.ReconstructibleFromInitial
#print axioms Alignment.GenesisReconstruction.reconstructible_of_preservesGenesis
#print axioms Alignment.GenesisReconstruction.preservesGenesis_of_reconstructible
#print axioms Alignment.GenesisReconstruction.preservesGenesis_iff_reconstructible
/- AXIOM_AUDIT_END -/
