import ConstitutiveSearch.ClosureSearchJointGrowthPolynomial
import ConstitutiveSearch.ClosureSearchWidthControlled

/-!
# Growing constitutive width and joint closure complexity

The joint candidate/fuel criterion can be connected directly to the
constitutive maxFrontierWidth coordinate.

A WidthControlledClosureSchedule already certifies that its explicit candidate
list is no wider than the announced constitutive frontier width.  When

  bitWidth(maxFrontierWidth) * fuel
    <= degree * log2(inputBits),

the actual executable closure counters are input-polynomially bounded.

A stronger profile-only corollary replaces fuel by maxFrontierWidth itself,
using the schedule's existing fuel <= width certificate.

The module also instantiates the schedule-specific theorem on a concrete family
whose width, candidate count, and fuel are all unbounded while the executable
closure counters remain input-polynomial relative to the concrete input size.
-/

namespace ConstitutiveSearch

/-- Monotonicity of Nat.log2, reconstructed from the standard power bounds. -/
theorem natLog2_mono
    {small large : Nat}
    (smallLe : small ≤ large) :
    Nat.log2 small ≤
      Nat.log2 large := by
  cases small with
  | zero =>
      exact Nat.zero_le _
  | succ small =>
      have smallPositive :
          0 < small + 1 :=
        Nat.zero_lt_succ small
      have largePositive :
          0 < large :=
        Nat.lt_of_lt_of_le
          smallPositive
          smallLe
      apply
        (Nat.le_log2
          (Nat.ne_of_gt largePositive)).2
      exact
        Nat.le_trans
          (Nat.log2_self_le
            (Nat.ne_of_gt smallPositive))
          smallLe

/-- Candidate binary width is monotone in candidate count. -/
theorem closureCandidateBitWidth_mono
    {small large : Nat}
    (smallLe : small ≤ large) :
    closureCandidateBitWidth small ≤
      closureCandidateBitWidth large := by
  unfold closureCandidateBitWidth
  exact
    Nat.add_le_add_right
      (natLog2_mono
        (closureGeometricBase_mono
          smallLe))
      1

namespace WidthControlledClosureSchedule

/--
A schedule-specific growing-width criterion.

Candidate growth is controlled by maxFrontierWidth through the schedule
certificate. Fuel may grow too, as long as the product of fuel and the binary
width of maxFrontierWidth remains logarithmic in the concrete input size.
-/
theorem inputPolynomialCounters_of_jointWidthGrowth
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type}
    {profile : Nat → ConstitutiveComplexityProfile}
    (primitive :
      (n : Nat) →
        RelationSearch (Generator n))
    (schedule :
      WidthControlledClosureSchedule
        State
        profile)
    (degree : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < (profile n).inputBits)
    (widthFuelLe :
      ∀ n : Nat,
        closureCandidateBitWidth
              (profile n).maxFrontierWidth *
            schedule.fuel n ≤
          degree *
            Nat.log2
              (profile n).inputBits) :
    InputPolynomialCounters
      primitive
      schedule := by
  have jointLe :
      ∀ n : Nat,
        closureCandidateBitWidth
              ((schedule.candidates n).length) *
            schedule.fuel n ≤
          degree *
            Nat.log2
              (profile n).inputBits := by
    intro n
    have bitWidthLe :
        closureCandidateBitWidth
            ((schedule.candidates n).length) ≤
          closureCandidateBitWidth
            (profile n).maxFrontierWidth :=
      closureCandidateBitWidth_mono
        (schedule.candidateLeWidth n)
    have productLe :
        closureCandidateBitWidth
              ((schedule.candidates n).length) *
            schedule.fuel n ≤
          closureCandidateBitWidth
              (profile n).maxFrontierWidth *
            schedule.fuel n :=
      Nat.mul_le_mul_right
        (schedule.fuel n)
        bitWidthLe
    exact
      Nat.le_trans
        productLe
        (widthFuelLe n)
  exact
    { primitiveQueries :=
        searchTransportClosure_jointGrowth_primitiveQueries
          primitive
          schedule.candidates
          schedule.fuel
          (fun n =>
            (profile n).inputBits)
          degree
          inputPositive
          jointLe
          schedule.source
          schedule.target
      compositionCandidates :=
        searchTransportClosure_jointGrowth_compositionCandidates
          primitive
          schedule.candidates
          schedule.fuel
          (fun n =>
            (profile n).inputBits)
          degree
          inputPositive
          jointLe
          schedule.source
          schedule.target }

/--
Stronger profile-only criterion: if width bit-size times width itself is
logarithmically controlled, every width-controlled schedule over that profile
has polynomial closure counters.
-/
theorem inputPolynomialCounters_of_profileWidthGrowth
    {State : Nat → Type}
    {Generator :
      (n : Nat) →
        State n → State n → Type}
    {profile : Nat → ConstitutiveComplexityProfile}
    (primitive :
      (n : Nat) →
        RelationSearch (Generator n))
    (schedule :
      WidthControlledClosureSchedule
        State
        profile)
    (degree : Nat)
    (inputPositive :
      ∀ n : Nat,
        0 < (profile n).inputBits)
    (widthGrowthLe :
      ∀ n : Nat,
        closureCandidateBitWidth
              (profile n).maxFrontierWidth *
            (profile n).maxFrontierWidth ≤
          degree *
            Nat.log2
              (profile n).inputBits) :
    InputPolynomialCounters
      primitive
      schedule := by
  apply
    schedule.inputPolynomialCounters_of_jointWidthGrowth
      primitive
      degree
      inputPositive
  intro n
  exact
    Nat.le_trans
      (Nat.mul_le_mul_left
        (closureCandidateBitWidth
          (profile n).maxFrontierWidth)
        (schedule.fuelLeWidth n))
      (widthGrowthLe n)

end WidthControlledClosureSchedule

/-! ## Explicit growing-width executable witness -/

abbrev JointGrowingWidthState
    (_n : Nat) : Type :=
  Nat

abbrev JointGrowingWidthGenerator
    (n : Nat)
    (_source _target :
      JointGrowingWidthState n) : Type :=
  Unit

def jointGrowingWidthPrimitive
    (n : Nat) :
    RelationSearch
      (JointGrowingWidthGenerator n) :=
  { find := fun _source _target =>
      none }

/--
Constitutive profile carrying the concrete jointly-growing input and width.
Other coordinates are zero because this witness isolates closure control-flow.
-/
def jointGrowingWidthProfile
    (n : Nat) :
    ConstitutiveComplexityProfile :=
  { inputBits :=
      jointGrowingInputBits n
    depth := 0
    maxFrontierWidth :=
      jointGrowingCandidateCount n
    events :=
      ComplexityCounts.zero
    representationCharge := 0 }

/-- Linear fuel remains below the exponentially growing witness width. -/
theorem jointGrowingFuel_le_width
    (n : Nat) :
    jointGrowingFuel n ≤
      (jointGrowingWidthProfile n).maxFrontierWidth := by
  unfold
    jointGrowingWidthProfile
    jointGrowingFuel
    jointGrowingCandidateCount
  have powerLt :
      n < 2 ^ n :=
    Nat.lt_two_pow_self
  exact
    Nat.le_sub_one_of_lt
      powerLt

/--
The explicit candidate list fills exactly the announced constitutive width,
while fuel grows linearly.
-/
def jointGrowingWidthSchedule :
    WidthControlledClosureSchedule
      JointGrowingWidthState
      jointGrowingWidthProfile :=
  { candidates := fun n =>
      List.replicate
        (jointGrowingCandidateCount n)
        0
    fuel :=
      jointGrowingFuel
    source := fun _ => 0
    target := fun _ => 1
    candidateLeWidth := by
      intro n
      change
        (List.replicate
          (jointGrowingCandidateCount n)
          0).length ≤
        jointGrowingCandidateCount n
      simp
    fuelLeWidth :=
      jointGrowingFuel_le_width }

/--
The schedule-specific width/fuel criterion is exactly the previously certified
joint witness inequality.
-/
theorem jointGrowingWidthSchedule_jointLe
    (n : Nat) :
    closureCandidateBitWidth
          (jointGrowingWidthProfile n).maxFrontierWidth *
        jointGrowingWidthSchedule.fuel n ≤
      1 *
        Nat.log2
          (jointGrowingWidthProfile n).inputBits := by
  simpa only [
    jointGrowingWidthProfile,
    jointGrowingWidthSchedule
  ] using
    jointGrowing_jointLe n

/--
Actual executable closure counters are input-polynomial even though the
constitutive width and fuel are both unbounded.
-/
theorem jointGrowingWidthSchedule_countersPolynomial :
    WidthControlledClosureSchedule.InputPolynomialCounters
      jointGrowingWidthPrimitive
      jointGrowingWidthSchedule :=
  jointGrowingWidthSchedule.inputPolynomialCounters_of_jointWidthGrowth
    jointGrowingWidthPrimitive
    1
    (fun n =>
      jointGrowing_inputPositive n)
    jointGrowingWidthSchedule_jointLe

/-- The constitutive width coordinate of the witness is unbounded. -/
theorem jointGrowingWidthProfile_width_unbounded :
    ∀ cap : Nat,
      ∃ n : Nat,
        cap <
          (jointGrowingWidthProfile n).maxFrontierWidth := by
  simpa only [
    jointGrowingWidthProfile
  ] using
    jointGrowingCandidateCount_unbounded

/-- The schedule fuel is unbounded too. -/
theorem jointGrowingWidthSchedule_fuel_unbounded :
    ∀ cap : Nat,
      ∃ n : Nat,
        cap <
          jointGrowingWidthSchedule.fuel n := by
  simpa only [
    jointGrowingWidthSchedule
  ] using
    jointGrowingFuel_unbounded

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.natLog2_mono
#print axioms ConstitutiveSearch.closureCandidateBitWidth_mono
#print axioms ConstitutiveSearch.WidthControlledClosureSchedule.inputPolynomialCounters_of_jointWidthGrowth
#print axioms ConstitutiveSearch.WidthControlledClosureSchedule.inputPolynomialCounters_of_profileWidthGrowth
#print axioms ConstitutiveSearch.JointGrowingWidthState
#print axioms ConstitutiveSearch.JointGrowingWidthGenerator
#print axioms ConstitutiveSearch.jointGrowingWidthPrimitive
#print axioms ConstitutiveSearch.jointGrowingWidthProfile
#print axioms ConstitutiveSearch.jointGrowingFuel_le_width
#print axioms ConstitutiveSearch.jointGrowingWidthSchedule
#print axioms ConstitutiveSearch.jointGrowingWidthSchedule_jointLe
#print axioms ConstitutiveSearch.jointGrowingWidthSchedule_countersPolynomial
#print axioms ConstitutiveSearch.jointGrowingWidthProfile_width_unbounded
#print axioms ConstitutiveSearch.jointGrowingWidthSchedule_fuel_unbounded
/- AXIOM_AUDIT_END -/
