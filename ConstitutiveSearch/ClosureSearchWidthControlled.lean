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
The state type may depend on the family index, which is required by concrete
families such as SAT contexts generated from F(n).

Whenever width itself has one uniform finite cap across the family, both actual
executable closure counters inherit input-polynomial bounds.

This is a sufficient regime.  It does not claim that every useful closure
schedule must be width-controlled, nor that polynomially growing width suffices
for the current closure engine.
-/

namespace ConstitutiveSearch

universe uState uGenerator

/--
One family of closure-search invocations controlled pointwise by the
constitutive width coordinate of an announced profile family.
-/
structure WidthControlledClosureSchedule
    (State : Nat → Type uState)
    (profile : Nat → ConstitutiveComplexityProfile) where
  candidates :
    (n : Nat) →
      List (State n)
  fuel : Nat → Nat
  source :
    (n : Nat) →
      State n
  target :
    (n : Nat) →
      State n
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
    {State : Nat → Type uState}
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
    {State : Nat → Type uState}
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
    {State : Nat → Type uState}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    {profile : Nat → ConstitutiveComplexityProfile}
    (primitive :
      (n : Nat) →
        RelationSearch (Generator n))
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
          (primitive n)
          (schedule.candidates n)
          (schedule.fuel n)
          (schedule.source n)
          (schedule.target n)).stats.primitiveQueries) := by
  rcases
      closurePrimitiveBoundedFuel_of_candidateInputPolynomial
        widthCap
        (schedule.candidateLength_inputPolynomiallyBounded
          widthCap
          bounded)
        (schedule.fuel_uniformlyBounded
          widthCap
          bounded) with
    ⟨envelope, budgetLe⟩
  refine
    ⟨envelope, ?_⟩
  intro n
  exact
    Nat.le_trans
      (searchTransportClosureBounded_primitiveQueries_le
        (primitive n)
        (schedule.candidates n)
        (schedule.fuel n)
        (schedule.source n)
        (schedule.target n))
      (budgetLe n)

/--
Actual composition-candidate counts satisfy the same input-polynomial regime.
-/
theorem compositionCandidates_inputPolynomiallyBounded
    {State : Nat → Type uState}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    {profile : Nat → ConstitutiveComplexityProfile}
    (primitive :
      (n : Nat) →
        RelationSearch (Generator n))
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
          (primitive n)
          (schedule.candidates n)
          (schedule.fuel n)
          (schedule.source n)
          (schedule.target n)).stats.compositionCandidates) := by
  rcases
      closureCompositionBoundedFuel_of_candidateInputPolynomial
        widthCap
        (schedule.candidateLength_inputPolynomiallyBounded
          widthCap
          bounded)
        (schedule.fuel_uniformlyBounded
          widthCap
          bounded) with
    ⟨envelope, budgetLe⟩
  refine
    ⟨envelope, ?_⟩
  intro n
  exact
    Nat.le_trans
      (searchTransportClosureBounded_compositionCandidates_le
        (primitive n)
        (schedule.candidates n)
        (schedule.fuel n)
        (schedule.source n)
        (schedule.target n))
      (budgetLe n)

/-- Packaged polynomial control-flow evidence for one width-controlled schedule. -/
structure InputPolynomialCounters
    {State : Nat → Type uState}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    {profile : Nat → ConstitutiveComplexityProfile}
    (primitive :
      (n : Nat) →
        RelationSearch (Generator n))
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
          (primitive n)
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
          (primitive n)
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
    {State : Nat → Type uState}
    {Generator :
      (n : Nat) →
        State n → State n → Type uGenerator}
    {profile : Nat → ConstitutiveComplexityProfile}
    (primitive :
      (n : Nat) →
        RelationSearch (Generator n))
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
