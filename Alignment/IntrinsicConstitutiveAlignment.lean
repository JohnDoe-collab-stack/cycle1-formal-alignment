import Alignment.CertifiedFiniteIntrinsicAlignmentDecision
import Alignment.IntrinsicRelationalRigidity

/-!
# Intrinsic constitutive alignment

This module closes the intrinsic alignment layer into one interface.

An intrinsic constitutive alignment consists only of an exact relation-preserving
alignment of the initial constituted carriers.  Arbitrary natural-depth
transport, genesis preservation, and reconstruction of the initial
correspondence are derived rather than stored as extra data.

For finite carriers, the existing exhaustive intrinsic decision is lifted to
this closed interface.  Under target relational rigidity, the resulting
correspondence is pointwise unique at every natural depth.
-/

namespace Alignment
namespace GenesisReconstruction

universe uSource uTarget uValue

/--
The closed intrinsic constitutive alignment object.

No common anchor, mediator, cross-system pairing, depth bound, or supplied
family of terminal transports occurs in the data.  The only stored witness is
the exact initial correspondence that preserves the intrinsic relation.
-/
structure IntrinsicConstitutiveAlignment
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    (context : IntrinsicRelationalContext Source Target Value) where
  initial : IntrinsicCompatibleExactAlignment context

namespace IntrinsicConstitutiveAlignment

/-- Canonical exact transport induced at any requested natural depth. -/
def transportAtDepth
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (alignment : IntrinsicConstitutiveAlignment context)
    (depth : Nat) :
    ExactTypeTransport
      (IteratedCarrier Source depth)
      (IteratedCarrier Target depth) :=
  liftToDepth alignment.initial.transport depth

/-- Every induced natural-depth transport preserves genesis. -/
theorem transportAtDepth_preservesGenesis
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (alignment : IntrinsicConstitutiveAlignment context)
    (depth : Nat) :
    PreservesGenesis (alignment.transportAtDepth depth) :=
  liftToDepth_preservesGenesis alignment.initial.transport depth

/-- The stored initial transport preserves the intrinsic relation. -/
theorem preservesInitialRelation
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (alignment : IntrinsicConstitutiveAlignment context)
    (first second : Source) :
    context.targetRelation
        (alignment.initial.transport.forward first)
        (alignment.initial.transport.forward second) =
      context.sourceRelation first second :=
  alignment.initial.preservesRelation first second

/--
Reconstructing the initial transport from any induced terminal depth recovers
the original forward correspondence pointwise.
-/
theorem reconstructInitial_forward
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (alignment : IntrinsicConstitutiveAlignment context)
    (depth : Nat)
    (identity : Source) :
    (GenesisReconstruction.reconstructInitial
      (alignment.transportAtDepth depth)
      (alignment.transportAtDepth_preservesGenesis depth)).forward identity =
      alignment.initial.transport.forward identity := by
  let reconstructed :=
    GenesisReconstruction.reconstructInitial
      (alignment.transportAtDepth depth)
      (alignment.transportAtDepth_preservesGenesis depth)
  apply IteratedCarrier.embedInitial_injective depth
  calc
    IteratedCarrier.embedInitial depth (reconstructed.forward identity) =
        (liftToDepth reconstructed depth).forward
          (IteratedCarrier.embedInitial depth identity) := by
      symm
      simpa [IteratedCarrier.embedInitial] using
        (liftToDepth_embedFrom
          reconstructed
          (DepthExtension.zeroTo depth)
          identity)
    _ = (alignment.transportAtDepth depth).forward
          (IteratedCarrier.embedInitial depth identity) := by
      symm
      exact
        GenesisReconstruction.reconstruct_forward
          depth
          (alignment.transportAtDepth depth)
          (alignment.transportAtDepth_preservesGenesis depth)
          (IteratedCarrier.embedInitial depth identity)
    _ = IteratedCarrier.embedInitial depth
          (alignment.initial.transport.forward identity) := by
      simpa [IntrinsicConstitutiveAlignment.transportAtDepth,
        IteratedCarrier.embedInitial] using
        (liftToDepth_embedFrom
          alignment.initial.transport
          (DepthExtension.zeroTo depth)
          identity)

/--
The backward map is reconstructed as well, because exact forward agreement
forces exact backward agreement.
-/
theorem reconstructInitial_backward
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (alignment : IntrinsicConstitutiveAlignment context)
    (depth : Nat)
    (identity : Target) :
    (GenesisReconstruction.reconstructInitial
      (alignment.transportAtDepth depth)
      (alignment.transportAtDepth_preservesGenesis depth)).backward identity =
      alignment.initial.transport.backward identity := by
  exact
    ExactTypeTransport.backward_eq_of_forward_eq
      (GenesisReconstruction.reconstructInitial
        (alignment.transportAtDepth depth)
        (alignment.transportAtDepth_preservesGenesis depth))
      alignment.initial.transport
      (alignment.reconstructInitial_forward depth)
      identity

/-- Pointwise equality of initial forward maps propagates to every depth. -/
theorem liftToDepth_forward_congr
    {Source : Type uSource}
    {Target : Type uTarget}
    (first second : ExactTypeTransport Source Target)
    (agreement :
      (identity : Source) → first.forward identity = second.forward identity)
    (depth : Nat)
    (identity : IteratedCarrier Source depth) :
    (liftToDepth first depth).forward identity =
      (liftToDepth second depth).forward identity := by
  induction depth with
  | zero =>
      exact agreement identity
  | succ depth inductionHypothesis =>
      cases identity with
      | inl prior =>
          exact congrArg Sum.inl (inductionHypothesis prior)
      | inr fresh =>
          cases fresh
          rfl

/--
Target relational rigidity makes two intrinsic constitutive alignments agree
pointwise at every natural depth.
-/
theorem transportAtDepth_forward_unique_of_targetRigidity
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (targetRigid : RelationallyRigid context.targetRelation)
    (first second : IntrinsicConstitutiveAlignment context)
    (depth : Nat)
    (identity : IteratedCarrier Source depth) :
    (first.transportAtDepth depth).forward identity =
      (second.transportAtDepth depth).forward identity :=
  liftToDepth_forward_congr
    first.initial.transport
    second.initial.transport
    (first.initial.forward_unique_of_targetRigidity
      targetRigid second.initial)
    depth
    identity

/-- Exactness forces the corresponding backward maps to agree at every depth. -/
theorem transportAtDepth_backward_unique_of_targetRigidity
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (targetRigid : RelationallyRigid context.targetRelation)
    (first second : IntrinsicConstitutiveAlignment context)
    (depth : Nat)
    (identity : IteratedCarrier Target depth) :
    (first.transportAtDepth depth).backward identity =
      (second.transportAtDepth depth).backward identity :=
  ExactTypeTransport.backward_eq_of_forward_eq
    (first.transportAtDepth depth)
    (second.transportAtDepth depth)
    (first.transportAtDepth_forward_unique_of_targetRigidity
      targetRigid second depth)
    identity

end IntrinsicConstitutiveAlignment

namespace FiniteIntrinsicAlignmentDecision

open FiniteAnchoredMatchSearch

/--
Certified finite decision lifted to the closed constitutive alignment object.
The negative branch refutes every closed intrinsic constitutive alignment.
-/
inductive ConstitutiveAlignmentDecision
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    (context : IntrinsicRelationalContext Source Target Value) : Type _ where
  | aligned :
      IntrinsicConstitutiveAlignment context →
      ConstitutiveAlignmentDecision context
  | impossible :
      (IntrinsicConstitutiveAlignment context → False) →
      ConstitutiveAlignmentDecision context

namespace ConstitutiveAlignmentDecision

/-- Executable branch view of the closed constitutive decision. -/
def isAligned
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value} :
    ConstitutiveAlignmentDecision context → Bool
  | .aligned _ => true
  | .impossible _ => false

end ConstitutiveAlignmentDecision

/--
End-to-end finite decision for the closed intrinsic constitutive alignment
object, from complete local carrier listings alone.
-/
def decideConstitutiveAlignmentFromListings
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target) :
    ConstitutiveAlignmentDecision context :=
  match decideAlignmentFromListings context sources targets with
  | .aligned alignment =>
      .aligned ⟨alignment⟩
  | .impossible refute =>
      .impossible (fun alignment => refute alignment.initial)

/-- Existing closed alignment forces the positive certified branch. -/
theorem decideConstitutiveAlignmentFromListings_isAligned_of_alignment
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (alignment : IntrinsicConstitutiveAlignment context) :
    (decideConstitutiveAlignmentFromListings
      context sources targets).isAligned = true := by
  cases decision :
      decideConstitutiveAlignmentFromListings
        context sources targets with
  | aligned found =>
      rfl
  | impossible refute =>
      exact (refute alignment).elim

/-- Independent impossibility forces the negative certified branch. -/
theorem decideConstitutiveAlignmentFromListings_isAligned_false_of_refutation
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    [DecidableEq Source]
    [DecidableEq Target]
    [DecidableEq Value]
    (context : IntrinsicRelationalContext Source Target Value)
    (sources : FiniteListing Source)
    (targets : FiniteListing Target)
    (refute : IntrinsicConstitutiveAlignment context → False) :
    (decideConstitutiveAlignmentFromListings
      context sources targets).isAligned = false := by
  cases decision :
      decideConstitutiveAlignmentFromListings
        context sources targets with
  | aligned alignment =>
      exact (refute alignment).elim
  | impossible noAlignment =>
      rfl

end FiniteIntrinsicAlignmentDecision
end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.IntrinsicConstitutiveAlignment
#print axioms Alignment.GenesisReconstruction.IntrinsicConstitutiveAlignment.transportAtDepth
#print axioms Alignment.GenesisReconstruction.IntrinsicConstitutiveAlignment.transportAtDepth_preservesGenesis
#print axioms Alignment.GenesisReconstruction.IntrinsicConstitutiveAlignment.preservesInitialRelation
#print axioms Alignment.GenesisReconstruction.IntrinsicConstitutiveAlignment.reconstructInitial_forward
#print axioms Alignment.GenesisReconstruction.IntrinsicConstitutiveAlignment.reconstructInitial_backward
#print axioms Alignment.GenesisReconstruction.IntrinsicConstitutiveAlignment.liftToDepth_forward_congr
#print axioms Alignment.GenesisReconstruction.IntrinsicConstitutiveAlignment.transportAtDepth_forward_unique_of_targetRigidity
#print axioms Alignment.GenesisReconstruction.IntrinsicConstitutiveAlignment.transportAtDepth_backward_unique_of_targetRigidity
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.ConstitutiveAlignmentDecision
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.ConstitutiveAlignmentDecision.isAligned
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.decideConstitutiveAlignmentFromListings
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.decideConstitutiveAlignmentFromListings_isAligned_of_alignment
#print axioms Alignment.GenesisReconstruction.FiniteIntrinsicAlignmentDecision.decideConstitutiveAlignmentFromListings_isAligned_false_of_refutation
/- AXIOM_AUDIT_END -/
