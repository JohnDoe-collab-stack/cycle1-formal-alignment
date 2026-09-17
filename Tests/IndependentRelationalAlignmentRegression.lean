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

def encodeObservation : Bool → TargetObservation
  | false => .absent
  | true => .edge

theorem encodeObservation_injective :
    Function.Injective encodeObservation := by
  intro first second equality
  cases first <;> cases second
  · rfl
  · cases equality
  · cases equality
  · rfl

theorem targetObservationRelation_direct
    (first second : SourceNode) :
    targetObservationRelation
        (directForward first)
        (directForward second) =
      encodeObservation (sourceRelation first second) := by
  cases first <;> cases second <;> rfl

def independentDirectAlignment :
    IndependentCompatibleExactAlignment independentContext :=
  { transport := directTransport
    preservesPattern := by
      intro first second third fourth
      constructor
      · intro sourceEquality
        calc
          independentContext.targetRelation
              (directTransport.forward first)
              (directTransport.forward second) =
            encodeObservation
              (independentContext.sourceRelation first second) := by
                exact targetObservationRelation_direct first second
          _ = encodeObservation
              (independentContext.sourceRelation third fourth) :=
                congrArg encodeObservation sourceEquality
          _ = independentContext.targetRelation
              (directTransport.forward third)
              (directTransport.forward fourth) := by
                exact (targetObservationRelation_direct third fourth).symm
      · intro targetEquality
        apply encodeObservation_injective
        calc
          encodeObservation
              (independentContext.sourceRelation first second) =
            independentContext.targetRelation
              (directTransport.forward first)
              (directTransport.forward second) := by
                exact (targetObservationRelation_direct first second).symm
          _ = independentContext.targetRelation
              (directTransport.forward third)
              (directTransport.forward fourth) := targetEquality
          _ = encodeObservation
              (independentContext.sourceRelation third fourth) := by
                exact targetObservationRelation_direct third fourth }

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
#print axioms Alignment.Tests.IndependentRelationalAlignmentRegression.encodeObservation
#print axioms Alignment.Tests.IndependentRelationalAlignmentRegression.encodeObservation_injective
#print axioms Alignment.Tests.IndependentRelationalAlignmentRegression.targetObservationRelation_direct
#print axioms Alignment.Tests.IndependentRelationalAlignmentRegression.independentDirectAlignment
#print axioms Alignment.Tests.IndependentRelationalAlignmentRegression.independentConstitutiveAlignment
#print axioms Alignment.Tests.IndependentRelationalAlignmentRegression.independent_preservesGenesis_at_arbitrary_depth
#print axioms Alignment.Tests.IndependentRelationalAlignmentRegression.independent_reconstructs_initial
#print axioms Alignment.Tests.IndependentRelationalAlignmentRegression.oldContextIndependentAlignment
/- AXIOM_AUDIT_END -/
