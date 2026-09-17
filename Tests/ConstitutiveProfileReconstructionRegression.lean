import Alignment.ConstitutiveProfileReconstruction

namespace Alignment.Tests.ConstitutiveProfileReconstructionRegression

open GenesisReconstruction

/-- A carrier intentionally distinct from `Bool`. -/
inductive TaggedBit
  | zero
  | one

/-- Source and target profiles expose the same structural bit through one probe. -/
def boolProfile : Bool → Unit → Bool :=
  fun identity _ => identity

def taggedProfile : TaggedBit → Unit → Bool
  | .zero, _ => false
  | .one, _ => true

/-- Both profiles separate their local identities. -/
theorem boolProfile_separates :
    ProfileSeparates boolProfile := by
  intro first second agreement
  exact agreement ()

theorem taggedProfile_separates :
    ProfileSeparates taggedProfile := by
  intro first second agreement
  cases first <;> cases second
  · rfl
  · have impossible := agreement ()
    cases impossible
  · have impossible := agreement ()
    cases impossible
  · rfl

/-- Positive structural resolvers between two different carrier types. -/
def toTagged : Bool → TaggedBit
  | false => .zero
  | true => .one

def toBool : TaggedBit → Bool
  | .zero => false
  | .one => true

theorem toTagged_preservesProfile :
    PreservesProfile boolProfile taggedProfile toTagged := by
  intro identity probe
  cases identity <;> cases probe <;> rfl

theorem toBool_preservesProfile :
    PreservesProfile taggedProfile boolProfile toBool := by
  intro identity probe
  cases identity <;> cases probe <;> rfl

/-- The resolver does not store inverse laws. They are derived by the library. -/
def taggedResolver :
    BidirectionalProfileResolver Bool TaggedBit Unit Bool :=
  { sourceProfile := boolProfile
    targetProfile := taggedProfile
    forward := toTagged
    backward := toBool
    sourceSeparates := boolProfile_separates
    targetSeparates := taggedProfile_separates
    forwardPreserves := toTagged_preservesProfile
    backwardPreserves := toBool_preservesProfile }

theorem taggedResolver_roundTrip_false :
    taggedResolver.backward (taggedResolver.forward false) = false :=
  taggedResolver.forwardBackward false

theorem taggedResolver_roundTrip_one :
    taggedResolver.forward (taggedResolver.backward TaggedBit.one) =
      TaggedBit.one :=
  taggedResolver.backwardForward TaggedBit.one

/-- The reconstructed exact alignment extends canonically through arbitrary natural-depth genesis. -/
theorem taggedResolver_depth_three_preservesGenesis :
    PreservesGenesis (taggedResolver.finiteTransport 3) :=
  taggedResolver.finiteTransport_preservesGenesis 3

/-- The generated fresh identity at depth two is aligned independently of carrier type. -/
theorem taggedResolver_depth_three_fresh_two :
    (taggedResolver.finiteTransport 3).forward
        (@IteratedCarrier.freshAtStep Bool 2) =
      @IteratedCarrier.freshAtStep TaggedBit 2 := by
  rfl

/-- A non-separating profile cannot force resolver round-trips. -/
def constantProfile : Bool → Unit → Bool :=
  fun _ _ => false

def collapse : Bool → Bool :=
  fun _ => false

theorem collapse_preserves_constantProfile :
    PreservesProfile constantProfile constantProfile collapse := by
  intro identity probe
  cases identity <;> cases probe <;> rfl

theorem collapse_roundTrip_fails :
    collapse (collapse true) ≠ true := by
  intro equality
  change false = true at equality
  cases equality

end Alignment.Tests.ConstitutiveProfileReconstructionRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms Alignment.Tests.ConstitutiveProfileReconstructionRegression.taggedResolver
#print axioms Alignment.Tests.ConstitutiveProfileReconstructionRegression.taggedResolver_roundTrip_false
#print axioms Alignment.Tests.ConstitutiveProfileReconstructionRegression.taggedResolver_roundTrip_one
#print axioms Alignment.Tests.ConstitutiveProfileReconstructionRegression.taggedResolver_depth_three_preservesGenesis
#print axioms Alignment.Tests.ConstitutiveProfileReconstructionRegression.taggedResolver_depth_three_fresh_two
#print axioms Alignment.Tests.ConstitutiveProfileReconstructionRegression.collapse_preserves_constantProfile
#print axioms Alignment.Tests.ConstitutiveProfileReconstructionRegression.collapse_roundTrip_fails
/- AXIOM_AUDIT_END -/
