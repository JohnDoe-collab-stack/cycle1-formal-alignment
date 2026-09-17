import Alignment.IntrinsicConstitutiveAlignment
import Tests.FiniteIntrinsicAlignmentDecisionRegression
import Tests.IntrinsicRelationalRigidityRegression

namespace Alignment.Tests.IntrinsicConstitutiveAlignmentRegression

open GenesisReconstruction
open GenesisReconstruction.FiniteIntrinsicAlignmentDecision
open FiniteIntrinsicAlignmentDecisionRegression
open FiniteIntrinsicRelationalSearchRegression
open IntrinsicRelationalMediatorRegression
open IntrinsicRelationalRigidityRegression

/-- Package the directed rigid example into the closed alignment interface. -/
def directConstitutiveAlignment :
    IntrinsicConstitutiveAlignment context :=
  ⟨directAlignment⟩

/-- Arbitrary natural-depth transport is genesis-preserving. -/
theorem direct_preservesGenesis_at_arbitrary_depth
    (depth : Nat) :
    PreservesGenesis
      (directConstitutiveAlignment.transportAtDepth depth) :=
  directConstitutiveAlignment.transportAtDepth_preservesGenesis depth

/-- Reconstruction from any terminal depth recovers the initial forward map. -/
theorem direct_reconstructs_initial_forward
    (depth : Nat)
    (identity : SourceNode) :
    (reconstructInitial
      (directConstitutiveAlignment.transportAtDepth depth)
      (directConstitutiveAlignment.transportAtDepth_preservesGenesis depth)).forward
        identity =
      directAlignment.transport.forward identity :=
  directConstitutiveAlignment.reconstructInitial_forward depth identity

/-- Reconstruction from any terminal depth recovers the initial backward map. -/
theorem direct_reconstructs_initial_backward
    (depth : Nat)
    (identity : TargetNode) :
    (reconstructInitial
      (directConstitutiveAlignment.transportAtDepth depth)
      (directConstitutiveAlignment.transportAtDepth_preservesGenesis depth)).backward
        identity =
      directAlignment.transport.backward identity :=
  directConstitutiveAlignment.reconstructInitial_backward depth identity

/-- Package the independently reconstructed mediator alignment as well. -/
def mediatorConstitutiveAlignment :
    IntrinsicConstitutiveAlignment context :=
  ⟨mediatorAlignment⟩

/-- Rigidity forces the two constructions to agree at every natural depth. -/
theorem rigid_target_forces_arbitrary_depth_forward_agreement
    (depth : Nat)
    (identity : IteratedCarrier SourceNode depth) :
    (directConstitutiveAlignment.transportAtDepth depth).forward identity =
      (mediatorConstitutiveAlignment.transportAtDepth depth).forward identity :=
  directConstitutiveAlignment.transportAtDepth_forward_unique_of_targetRigidity
    targetRelation_rigid mediatorConstitutiveAlignment depth identity

/-- The finite certified decision lifts to the closed alignment interface. -/
def symmetricConstitutiveAlignment :
    IntrinsicConstitutiveAlignment symmetricContext :=
  ⟨identityAlignment⟩

theorem symmetric_closed_decision_is_aligned :
    (decideConstitutiveAlignmentFromListings
      symmetricContext boolListing boolListing).isAligned = true :=
  decideConstitutiveAlignmentFromListings_isAligned_of_alignment
    symmetricContext
    boolListing
    boolListing
    symmetricConstitutiveAlignment

/-- Incompatibility is retained as a constructive refutation at the closed layer. -/
theorem incompatible_closed_decision_is_impossible :
    (decideConstitutiveAlignmentFromListings
      incompatibleContext boolListing boolListing).isAligned = false :=
  decideConstitutiveAlignmentFromListings_isAligned_false_of_refutation
    incompatibleContext
    boolListing
    boolListing
    (fun alignment => incompatibleContext_no_alignment_direct alignment.initial)

end Alignment.Tests.IntrinsicConstitutiveAlignmentRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.IntrinsicConstitutiveAlignmentRegression.directConstitutiveAlignment
#print axioms Alignment.Tests.IntrinsicConstitutiveAlignmentRegression.direct_preservesGenesis_at_arbitrary_depth
#print axioms Alignment.Tests.IntrinsicConstitutiveAlignmentRegression.direct_reconstructs_initial_forward
#print axioms Alignment.Tests.IntrinsicConstitutiveAlignmentRegression.direct_reconstructs_initial_backward
#print axioms Alignment.Tests.IntrinsicConstitutiveAlignmentRegression.mediatorConstitutiveAlignment
#print axioms Alignment.Tests.IntrinsicConstitutiveAlignmentRegression.rigid_target_forces_arbitrary_depth_forward_agreement
#print axioms Alignment.Tests.IntrinsicConstitutiveAlignmentRegression.symmetricConstitutiveAlignment
#print axioms Alignment.Tests.IntrinsicConstitutiveAlignmentRegression.symmetric_closed_decision_is_aligned
#print axioms Alignment.Tests.IntrinsicConstitutiveAlignmentRegression.incompatible_closed_decision_is_impossible
/- AXIOM_AUDIT_END -/
