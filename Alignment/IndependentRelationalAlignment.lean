import Alignment.IntrinsicConstitutiveAlignment

/-!
# Independent intrinsic relational observations

The earlier intrinsic relational context removed common anchors, mediators, and
supplied transports, but source and target relations still returned values in
one shared observation type.

This module removes that remaining shared observation carrier. Source and target
relations now have independent local codomains. Cross-realization compatibility
does not compare local observation values directly. It preserves only the
equality pattern generated internally by each local relation.

No map between source and target observation values is supplied or chosen.
-/

namespace Alignment
namespace GenesisReconstruction

universe uSource uTarget uSourceValue uTargetValue uValue

/--
Two locally typed relational structures. No observation carrier is shared
between source and target.
-/
structure IndependentRelationalContext
    (Source : Type uSource)
    (Target : Type uTarget)
    (SourceValue : Type uSourceValue)
    (TargetValue : Type uTargetValue) where
  sourceRelation : Source → Source → SourceValue
  targetRelation : Target → Target → TargetValue
  sourceSeparates :
    ProfileSeparates
      (fun identity anchor : Source => sourceRelation anchor identity)
  targetSeparates :
    ProfileSeparates
      (fun identity anchor : Target => targetRelation anchor identity)

/--
A forward map preserves the intrinsic relational pattern when it preserves,
in both directions, which locally generated relation observations are equal.

Only equality inside each local observation type occurs. No cross-system value
comparison is present.
-/
def PreservesRelationalPattern
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue)
    (forward : Source → Target) : Prop :=
  ∀ first second third fourth : Source,
    (context.sourceRelation first second =
        context.sourceRelation third fourth) ↔
      (context.targetRelation (forward first) (forward second) =
        context.targetRelation (forward third) (forward fourth))

/--
Exact intrinsic alignment with independent local observation codomains.
-/
structure IndependentCompatibleExactAlignment
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue) where
  transport : ExactTypeTransport Source Target
  preservesPattern :
    PreservesRelationalPattern context transport.forward

namespace IntrinsicRelationalContext

/--
A same-valued intrinsic context is a special case of the independent interface.
This is a conservative forgetful translation, not an extra assumption.
-/
def toIndependent
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    (context : IntrinsicRelationalContext Source Target Value) :
    IndependentRelationalContext Source Target Value Value :=
  { sourceRelation := context.sourceRelation
    targetRelation := context.targetRelation
    sourceSeparates := context.sourceSeparates
    targetSeparates := context.targetSeparates }

end IntrinsicRelationalContext

namespace IntrinsicCompatibleExactAlignment

/--
Exact pointwise relation preservation implies preservation of the weaker,
label-free relational equality pattern.
-/
def toIndependent
    {Source : Type uSource}
    {Target : Type uTarget}
    {Value : Type uValue}
    {context : IntrinsicRelationalContext Source Target Value}
    (alignment : IntrinsicCompatibleExactAlignment context) :
    IndependentCompatibleExactAlignment context.toIndependent :=
  { transport := alignment.transport
    preservesPattern := by
      intro first second third fourth
      constructor
      · intro sourceEquality
        calc
          context.targetRelation
              (alignment.transport.forward first)
              (alignment.transport.forward second) =
            context.sourceRelation first second :=
              alignment.preservesRelation first second
          _ = context.sourceRelation third fourth := sourceEquality
          _ = context.targetRelation
              (alignment.transport.forward third)
              (alignment.transport.forward fourth) :=
                (alignment.preservesRelation third fourth).symm
      · intro targetEquality
        calc
          context.sourceRelation first second =
            context.targetRelation
              (alignment.transport.forward first)
              (alignment.transport.forward second) :=
                (alignment.preservesRelation first second).symm
          _ = context.targetRelation
              (alignment.transport.forward third)
              (alignment.transport.forward fourth) := targetEquality
          _ = context.sourceRelation third fourth :=
              alignment.preservesRelation third fourth }

end IntrinsicCompatibleExactAlignment

/--
Pattern rigidity: every exact self-transport preserving the locally generated
equality pattern fixes every identity.
-/
def RelationalPatternRigid
    {Carrier : Type uTarget}
    {Value : Type uTargetValue}
    (relation : Carrier → Carrier → Value) : Prop :=
  ∀ automorphism : ExactTypeTransport Carrier Carrier,
    (∀ first second third fourth : Carrier,
      (relation first second = relation third fourth) ↔
        (relation
            (automorphism.forward first)
            (automorphism.forward second) =
          relation
            (automorphism.forward third)
            (automorphism.forward fourth))) →
    (identity : Carrier) →
      automorphism.forward identity = identity

namespace IndependentCompatibleExactAlignment

/-- Compare two independent alignments by the target self-transport between them. -/
def targetDifference
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    {context :
      IndependentRelationalContext Source Target SourceValue TargetValue}
    (first second : IndependentCompatibleExactAlignment context) :
    ExactTypeTransport Target Target :=
  first.transport.reverse.compose second.transport

/--
The target difference between two pattern-compatible alignments preserves the
target's own relational equality pattern.
-/
theorem targetDifference_preservesPattern
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    {context :
      IndependentRelationalContext Source Target SourceValue TargetValue}
    (first second : IndependentCompatibleExactAlignment context)
    (left right otherLeft otherRight : Target) :
    (context.targetRelation left right =
        context.targetRelation otherLeft otherRight) ↔
      (context.targetRelation
          ((first.targetDifference second).forward left)
          ((first.targetDifference second).forward right) =
        context.targetRelation
          ((first.targetDifference second).forward otherLeft)
          ((first.targetDifference second).forward otherRight)) := by
  constructor
  · intro targetEquality
    have firstTargetEquality :
        context.targetRelation
            (first.transport.forward (first.transport.backward left))
            (first.transport.forward (first.transport.backward right)) =
          context.targetRelation
            (first.transport.forward (first.transport.backward otherLeft))
            (first.transport.forward (first.transport.backward otherRight)) := by
      simpa only [first.transport.backwardForward] using targetEquality
    have sourceEquality :
        context.sourceRelation
            (first.transport.backward left)
            (first.transport.backward right) =
          context.sourceRelation
            (first.transport.backward otherLeft)
            (first.transport.backward otherRight) :=
      (first.preservesPattern
        (first.transport.backward left)
        (first.transport.backward right)
        (first.transport.backward otherLeft)
        (first.transport.backward otherRight)).mpr
          firstTargetEquality
    have secondTargetEquality :=
      (second.preservesPattern
        (first.transport.backward left)
        (first.transport.backward right)
        (first.transport.backward otherLeft)
        (first.transport.backward otherRight)).mp
          sourceEquality
    change
      context.targetRelation
          (second.transport.forward (first.transport.backward left))
          (second.transport.forward (first.transport.backward right)) =
        context.targetRelation
          (second.transport.forward (first.transport.backward otherLeft))
          (second.transport.forward (first.transport.backward otherRight))
    exact secondTargetEquality
  · intro differenceEquality
    change
      context.targetRelation
          (second.transport.forward (first.transport.backward left))
          (second.transport.forward (first.transport.backward right)) =
        context.targetRelation
          (second.transport.forward (first.transport.backward otherLeft))
          (second.transport.forward (first.transport.backward otherRight))
      at differenceEquality
    have sourceEquality :
        context.sourceRelation
            (first.transport.backward left)
            (first.transport.backward right) =
          context.sourceRelation
            (first.transport.backward otherLeft)
            (first.transport.backward otherRight) :=
      (second.preservesPattern
        (first.transport.backward left)
        (first.transport.backward right)
        (first.transport.backward otherLeft)
        (first.transport.backward otherRight)).mpr
          differenceEquality
    have firstTargetEquality :=
      (first.preservesPattern
        (first.transport.backward left)
        (first.transport.backward right)
        (first.transport.backward otherLeft)
        (first.transport.backward otherRight)).mp
          sourceEquality
    simpa only [first.transport.backwardForward] using firstTargetEquality

/-- Target pattern rigidity removes all remaining forward ambiguity. -/
theorem forward_unique_of_targetPatternRigidity
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    {context :
      IndependentRelationalContext Source Target SourceValue TargetValue}
    (targetRigid : RelationalPatternRigid context.targetRelation)
    (first second : IndependentCompatibleExactAlignment context)
    (identity : Source) :
    first.transport.forward identity =
      second.transport.forward identity := by
  have fixed :=
    targetRigid
      (first.targetDifference second)
      (first.targetDifference_preservesPattern second)
      (first.transport.forward identity)
  change
    second.transport.forward
        (first.transport.backward (first.transport.forward identity)) =
      first.transport.forward identity at fixed
  rw [first.transport.forwardBackward] at fixed
  exact fixed.symm

/-- Exactness then forces backward uniqueness as well. -/
theorem backward_unique_of_targetPatternRigidity
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    {context :
      IndependentRelationalContext Source Target SourceValue TargetValue}
    (targetRigid : RelationalPatternRigid context.targetRelation)
    (first second : IndependentCompatibleExactAlignment context)
    (identity : Target) :
    first.transport.backward identity =
      second.transport.backward identity :=
  ExactTypeTransport.backward_eq_of_forward_eq
    first.transport
    second.transport
    (first.forward_unique_of_targetPatternRigidity targetRigid second)
    identity

end IndependentCompatibleExactAlignment

/--
Closed constitutive alignment with independent local observation codomains.
Natural-depth persistence and reconstruction are derived from the initial
pattern-compatible exact transport.
-/
structure IndependentConstitutiveAlignment
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    (context :
      IndependentRelationalContext Source Target SourceValue TargetValue) where
  initial : IndependentCompatibleExactAlignment context

namespace IndependentConstitutiveAlignment

def transportAtDepth
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    {context :
      IndependentRelationalContext Source Target SourceValue TargetValue}
    (alignment : IndependentConstitutiveAlignment context)
    (depth : Nat) :
    ExactTypeTransport
      (IteratedCarrier Source depth)
      (IteratedCarrier Target depth) :=
  liftToDepth alignment.initial.transport depth

theorem transportAtDepth_preservesGenesis
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    {context :
      IndependentRelationalContext Source Target SourceValue TargetValue}
    (alignment : IndependentConstitutiveAlignment context)
    (depth : Nat) :
    PreservesGenesis (alignment.transportAtDepth depth) :=
  liftToDepth_preservesGenesis alignment.initial.transport depth

theorem reconstructInitial_forward
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    {context :
      IndependentRelationalContext Source Target SourceValue TargetValue}
    (alignment : IndependentConstitutiveAlignment context)
    (depth : Nat)
    (identity : Source) :
    (reconstructInitial
      (alignment.transportAtDepth depth)
      (alignment.transportAtDepth_preservesGenesis depth)).forward identity =
      alignment.initial.transport.forward identity := by
  let reconstructed :=
    reconstructInitial
      (alignment.transportAtDepth depth)
      (alignment.transportAtDepth_preservesGenesis depth)
  apply IteratedCarrier.embedInitial_injective depth
  calc
    IteratedCarrier.embedInitial depth (reconstructed.forward identity) =
        (liftToDepth reconstructed depth).forward
          (IteratedCarrier.embedInitial depth identity) := by
      symm
      simpa [IteratedCarrier.embedInitial, liftToDepth] using
        (liftToDepth_embedFrom
          reconstructed
          (DepthExtension.zeroTo depth)
          identity)
    _ = (alignment.transportAtDepth depth).forward
          (IteratedCarrier.embedInitial depth identity) := by
      symm
      exact
        reconstruct_forward
          depth
          (alignment.transportAtDepth depth)
          (alignment.transportAtDepth_preservesGenesis depth)
          (IteratedCarrier.embedInitial depth identity)
    _ = IteratedCarrier.embedInitial depth
          (alignment.initial.transport.forward identity) := by
      simpa [IndependentConstitutiveAlignment.transportAtDepth,
        IteratedCarrier.embedInitial, liftToDepth] using
        (liftToDepth_embedFrom
          alignment.initial.transport
          (DepthExtension.zeroTo depth)
          identity)

theorem reconstructInitial_backward
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    {context :
      IndependentRelationalContext Source Target SourceValue TargetValue}
    (alignment : IndependentConstitutiveAlignment context)
    (depth : Nat)
    (identity : Target) :
    (reconstructInitial
      (alignment.transportAtDepth depth)
      (alignment.transportAtDepth_preservesGenesis depth)).backward identity =
      alignment.initial.transport.backward identity :=
  ExactTypeTransport.backward_eq_of_forward_eq
    (reconstructInitial
      (alignment.transportAtDepth depth)
      (alignment.transportAtDepth_preservesGenesis depth))
    alignment.initial.transport
    (alignment.reconstructInitial_forward depth)
    identity

theorem transportAtDepth_forward_unique_of_targetPatternRigidity
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    {context :
      IndependentRelationalContext Source Target SourceValue TargetValue}
    (targetRigid : RelationalPatternRigid context.targetRelation)
    (first second : IndependentConstitutiveAlignment context)
    (depth : Nat)
    (identity : IteratedCarrier Source depth) :
    (first.transportAtDepth depth).forward identity =
      (second.transportAtDepth depth).forward identity :=
  IntrinsicConstitutiveAlignment.liftToDepth_forward_congr
    first.initial.transport
    second.initial.transport
    (first.initial.forward_unique_of_targetPatternRigidity
      targetRigid second.initial)
    depth
    identity

theorem transportAtDepth_backward_unique_of_targetPatternRigidity
    {Source : Type uSource}
    {Target : Type uTarget}
    {SourceValue : Type uSourceValue}
    {TargetValue : Type uTargetValue}
    {context :
      IndependentRelationalContext Source Target SourceValue TargetValue}
    (targetRigid : RelationalPatternRigid context.targetRelation)
    (first second : IndependentConstitutiveAlignment context)
    (depth : Nat)
    (identity : IteratedCarrier Target depth) :
    (first.transportAtDepth depth).backward identity =
      (second.transportAtDepth depth).backward identity :=
  ExactTypeTransport.backward_eq_of_forward_eq
    (first.transportAtDepth depth)
    (second.transportAtDepth depth)
    (first.transportAtDepth_forward_unique_of_targetPatternRigidity
      targetRigid second depth)
    identity

end IndependentConstitutiveAlignment

end GenesisReconstruction
end Alignment

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.GenesisReconstruction.IndependentRelationalContext
#print axioms Alignment.GenesisReconstruction.PreservesRelationalPattern
#print axioms Alignment.GenesisReconstruction.IndependentCompatibleExactAlignment
#print axioms Alignment.GenesisReconstruction.IntrinsicRelationalContext.toIndependent
#print axioms Alignment.GenesisReconstruction.IntrinsicCompatibleExactAlignment.toIndependent
#print axioms Alignment.GenesisReconstruction.RelationalPatternRigid
#print axioms Alignment.GenesisReconstruction.IndependentCompatibleExactAlignment.targetDifference
#print axioms Alignment.GenesisReconstruction.IndependentCompatibleExactAlignment.targetDifference_preservesPattern
#print axioms Alignment.GenesisReconstruction.IndependentCompatibleExactAlignment.forward_unique_of_targetPatternRigidity
#print axioms Alignment.GenesisReconstruction.IndependentCompatibleExactAlignment.backward_unique_of_targetPatternRigidity
#print axioms Alignment.GenesisReconstruction.IndependentConstitutiveAlignment
#print axioms Alignment.GenesisReconstruction.IndependentConstitutiveAlignment.transportAtDepth
#print axioms Alignment.GenesisReconstruction.IndependentConstitutiveAlignment.transportAtDepth_preservesGenesis
#print axioms Alignment.GenesisReconstruction.IndependentConstitutiveAlignment.reconstructInitial_forward
#print axioms Alignment.GenesisReconstruction.IndependentConstitutiveAlignment.reconstructInitial_backward
#print axioms Alignment.GenesisReconstruction.IndependentConstitutiveAlignment.transportAtDepth_forward_unique_of_targetPatternRigidity
#print axioms Alignment.GenesisReconstruction.IndependentConstitutiveAlignment.transportAtDepth_backward_unique_of_targetPatternRigidity
/- AXIOM_AUDIT_END -/
