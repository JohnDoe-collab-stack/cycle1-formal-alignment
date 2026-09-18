import ConstitutiveSearch.ClosureSearchFixedFuelPolynomial
import ConstitutiveSearch.ConstitutiveComplexityProfile

/-!
# Width-controlled closure-search regimes

The bounded-fuel theory already proves polynomial control-flow when candidate
growth is input-polynomial and fuel is uniformly bounded by a fixed constant.

This module ties those hypotheses to one constitutive quantity already carried
by every complexity profile: maximal frontier width.

A width-controlled closure schedule is explicit data whose candidate-list
length and fuel never exceed the announced constitutive maxFrontierWidth.
Whenever that width itself has one uniform finite cap across the family, both
actual executable closure counters inherit input-polynomial bounds.

This is a sufficient regime.  It does not claim that every useful closure
schedule must be width-controlled, nor that polynomially growing width suffices
for the current closure engine.
-/

namespace ConstitutiveSearch

/--
One family of closure-search invocations controlled pointwise by the
constitutive width coordinate of an announced profile family.
-/
structure WidthControlledClosureSchedule
    (State : Type)
    (profile : Nat → ConstitutiveComplexityProfile) where
  candidates : Nat → List State
  fuel : Nat → Nat
  source : Nat → State
  target : Nat → State
  candidateLeWidth :
    ∀ n : Nat,
      (candidates n).length ≤
        (profile n).maxFrontierWidth
  fuelLeWidth :
    ∀ n : Nat,
      fuel n ≤
        (profile n).maxFrontierWidth

/-- A uniform finite width cap for one constitutive profile family. -/
structure UniformProfileWidthBound
    (profile : Nat → ConstitutiveComplexityProfile)
    (widthCap : Nat) : Prop where
  widthLe :
    ∀ n : Nat,
      (profile n).maxFrontierWidth ≤
        widthCap

namespace WidthControlledClosureSchedule

/--
A width-controlled candidate family is input-polynomial whenever the profile
width has one uniform cap: the constant polynomial widthCap is an envelope.
-/
theorem candidateLength_inputPolynomiallyBounded
    {State : Type}
    {profile : Nat → ConstitutiveComplexityProfile}
    (schedule :
      WidthControlledClosureSchedule
        State
        profile)
    (widthCap : Nat)
    (bounded :
      UniformProfileWidthBound
        profile
        widthCap) :
    InputPolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
      (fun n =>
        (schedule.candidates n).length) :=
  ⟨CostPolynomial.constant widthCap,
    fun n => by
      change
        (schedule.candidates n).length ≤
          widthCap
      exact
        Nat.le_trans
          (schedule.candidateLeWidth n)
          (bounded.widthLe n)⟩

/-- The same uniform width cap bounds the schedule fuel. -/
theorem fuel_uniformlyBounded
    {State : Type}
    {profile : Nat → ConstitutiveComplexityProfile}
    (schedule :
      WidthControlledClosureSchedule
        State
        profile)
    (widthCap : Nat)
    (bounded :
      UniformProfileWidthBound
        profile
        widthCap) :
    ∀ n : Nat,
      schedule.fuel n ≤ widthCap :=
  fun n =>
    Nat.le_trans
      (schedule.fuelLeWidth n)
      (bounded.widthLe n)

/--
Actual primitive-query counts are input-polynomial for every width-controlled
schedule over a uniformly bounded-width profile family.
-/
theorem primitiveQueries_inputPolynomiallyBounded
    {State : Type}
    {Generator : State → State → Type}
    {profile : Nat → ConstitutiveComplexityProfile}
    (primitive : RelationSearch Generator)
    (schedule :
      WidthControlledClosureSchedule
        State
        profile)
    (widthCap : Nat)
    (bounded :
      UniformProfileWidthBound
        profile
        widthCap) :
    InputPolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
      (fun n =>
        (searchTransportClosureBounded
          primitive
          (schedule.candidates n)
          (schedule.fuel n)
          (schedule.source n)
          (schedule.target n)).stats.primitiveQueries) :=
  searchTransportClosureBoundedFuel_primitiveQueries_of_candidateInputPolynomial
    primitive
    schedule.candidates
    schedule.fuel
    widthCap
    (schedule.candidateLength_inputPolynomiallyBounded
      widthCap
      bounded)
    (schedule.fuel_uniformlyBounded
      widthCap
      bounded)
    schedule.source
    schedule.target

/--
Actual composition-candidate counts satisfy the same input-polynomial regime.
-/
theorem compositionCandidates_inputPolynomiallyBounded
    {State : Type}
    {Generator : State → State → Type}
    {profile : Nat → ConstitutiveComplexityProfile}
    (primitive : RelationSearch Generator)
    (schedule :
      WidthControlledClosureSchedule
        State
        profile)
    (widthCap : Nat)
    (bounded :
      UniformProfileWidthBound
        profile
        widthCap) :
    InputPolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
      (fun n =>
        (searchTransportClosureBounded
          primitive
          (schedule.candidates n)
          (schedule.fuel n)
          (schedule.source n)
          (schedule.target n)).stats.compositionCandidates) :=
  searchTransportClosureBoundedFuel_compositionCandidates_of_candidateInputPolynomial
    primitive
    schedule.candidates
    schedule.fuel
    widthCap
    (schedule.candidateLength_inputPolynomiallyBounded
      widthCap
      bounded)
    (schedule.fuel_uniformlyBounded
      widthCap
      bounded)
    schedule.source
    schedule.target

/-- Packaged polynomial control-flow evidence for one width-controlled schedule. -/
structure InputPolynomialCounters
    {State : Type}
    {Generator : State → State → Type}
    {profile : Nat → ConstitutiveComplexityProfile}
    (primitive : RelationSearch Generator)
    (schedule :
      WidthControlledClosureSchedule
        State
        profile) : Prop where
  primitiveQueries :
    InputPolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
      (fun n =>
        (searchTransportClosureBounded
          primitive
          (schedule.candidates n)
          (schedule.fuel n)
          (schedule.source n)
          (schedule.target n)).stats.primitiveQueries)
  compositionCandidates :
    InputPolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
      (fun n =>
        (searchTransportClosureBounded
          primitive
          (schedule.candidates n)
          (schedule.fuel n)
          (schedule.source n)
          (schedule.target n)).stats.compositionCandidates)

/--
Uniformly bounded constitutive width is therefore a sufficient internal
certificate for polynomial closure control-flow whenever the schedule stays
inside that width.
-/
theorem inputPolynomialCounters_of_uniformWidth
    {State : Type}
    {Generator : State → State → Type}
    {profile : Nat → ConstitutiveComplexityProfile}
    (primitive : RelationSearch Generator)
    (schedule :
      WidthControlledClosureSchedule
        State
        profile)
    (widthCap : Nat)
    (bounded :
      UniformProfileWidthBound
        profile
        widthCap) :
    InputPolynomialCounters
      primitive
      schedule :=
  { primitiveQueries :=
      schedule.primitiveQueries_inputPolynomiallyBounded
        primitive
        widthCap
        bounded
    compositionCandidates :=
      schedule.compositionCandidates_inputPolynomiallyBounded
        primitive
        widthCap
        bounded }

end WidthControlledClosureSchedule

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.WidthControlledClosureSchedule
#print axioms ConstitutiveSearch.UniformProfileWidthBound
#print axioms ConstitutiveSearch.WidthControlledClosureSchedule.candidateLength_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.WidthControlledClosureSchedule.fuel_uniformlyBounded
#print axioms ConstitutiveSearch.WidthControlledClosureSchedule.primitiveQueries_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.WidthControlledClosureSchedule.compositionCandidates_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.WidthControlledClosureSchedule.InputPolynomialCounters
#print axioms ConstitutiveSearch.WidthControlledClosureSchedule.inputPolynomialCounters_of_uniformWidth
/- AXIOM_AUDIT_END -/
