import Alignment.IndependentRelationalAlignment
import Tests.IntrinsicRelationalRigidityRegression

namespace Alignment.Tests.IndependentRelationalAlignmentRegression

open GenesisReconstruction
open IntrinsicRelationalMediatorRegression
open IntrinsicRelationalRigidityRegression

/--
Target-local observations deliberately use a different type from source-local
Boolean observations.
-/
inductive TargetObservation
  | absent
  | edge
deriving DecidableEq

def targetObservationRelation
    (source target : TargetNode) : TargetObservation :=
  match source with
  | .origin =>
      match target with
      | .origin => .absent
      | .successor => .edge
  | .successor => .absent

theorem targetObservationProfile_separates :
    ProfileSeparates
      (fun identity anchor : TargetNode =>
        targetObservationRelation anchor identity) := by
  intro first second agreement
  cases first <;> cases second
  · rfl
  · have impossible := agreement TargetNode.origin
    cases impossible
  · have impossible := agreement TargetNode.origin
    cases impossible
  · rfl

def independentContext :
    IndependentRelationalContext
      SourceNode TargetNode Bool TargetObservation :=
  { sourceRelation := sourceRelation
    targetRelation := targetObservationRelation
    sourceSeparates := sourceSelfProfile_separates
    targetSeparates := targetObservationProfile_separates }

def independentDirectAlignment :
    IndependentCompatibleExactAlignment independentContext :=
  { transport := directTransport
    preservesPattern := by
      intro first second third fourth
      cases first <;> cases second <;> cases third <;> cases fourth <;>
        simp [sourceRelation, targetObservationRelation, directTransport,
          directForward] }

def independentConstitutiveAlignment :
    IndependentConstitutiveAlignment independentContext :=
  ⟨independentDirectAlignment⟩

/--
The independent observation types still induce genesis-preserving transport at
every requested natural depth.
-/
theorem independent_preservesGenesis_at_arbitrary_depth
    (depth : Nat) :
    PreservesGenesis
      (independentConstitutiveAlignment.transportAtDepth depth) :=
  independentConstitutiveAlignment.transportAtDepth_preservesGenesis depth

/--
Reconstruction from arbitrary natural depth recovers the initial alignment even
though the two local observation types are distinct.
-/
theorem independent_reconstructs_initial
    (depth : Nat)
    (identity : SourceNode) :
    (reconstructInitial
      (independentConstitutiveAlignment.transportAtDepth depth)
      (independentConstitutiveAlignment.transportAtDepth_preservesGenesis depth)).forward
        identity =
      directTransport.forward identity :=
  independentConstitutiveAlignment.reconstructInitial_forward depth identity

/--
The previous shared-value interface embeds conservatively into the independent
one.
-/
def oldContextIndependentAlignment :
    IndependentCompatibleExactAlignment context.toIndependent :=
  directAlignment.toIndependent

end Alignment.Tests.IndependentRelationalAlignmentRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.IndependentRelationalAlignmentRegression.TargetObservation
#print axioms Alignment.Tests.IndependentRelationalAlignmentRegression.targetObservationRelation
#print axioms Alignment.Tests.IndependentRelationalAlignmentRegression.targetObservationProfile_separates
#print axioms Alignment.Tests.IndependentRelationalAlignmentRegression.independentContext
#print axioms Alignment.Tests.IndependentRelationalAlignmentRegression.independentDirectAlignment
#print axioms Alignment.Tests.IndependentRelationalAlignmentRegression.independentConstitutiveAlignment
#print axioms Alignment.Tests.IndependentRelationalAlignmentRegression.independent_preservesGenesis_at_arbitrary_depth
#print axioms Alignment.Tests.IndependentRelationalAlignmentRegression.independent_reconstructs_initial
#print axioms Alignment.Tests.IndependentRelationalAlignmentRegression.oldContextIndependentAlignment
/- AXIOM_AUDIT_END -/
