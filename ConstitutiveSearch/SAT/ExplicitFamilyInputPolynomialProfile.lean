import ConstitutiveSearch.SAT.ExplicitFamilyCostPolynomials

/-!
# Input-indexed polynomial profile theorem for the explicit SAT family

This module closes the multidimensional constitutive profile under explicit
polynomial envelopes evaluated at the concrete binary input size.

The local F(n) phase and the added two-flip composition phase are certified
separately.  The total profile then inherits polynomial boundedness from the
generic profile-composition theorem.

This is a theorem about the declared constitutive profile and binary
representation model.  It is not a wall-clock machine-time theorem.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Folded natural maximum stays below a common bound. -/
theorem foldlNatMax_le
    (bound : Nat) :
    ∀ (values : List Nat) (initial : Nat),
      initial ≤ bound →
      (∀ value : Nat,
        value ∈ values →
          value ≤ bound) →
      values.foldl Nat.max initial ≤ bound
  | [], initial, initialLe, _ =>
      initialLe
  | head :: tail, initial, initialLe, allLe =>
      foldlNatMax_le
        bound
        tail
        (Nat.max initial head)
        (Constructive.nat_max_le
          initial
          head
          bound
          initialLe
          (allLe
            head
            List.mem_cons_self))
        (fun value member =>
          allLe
            value
            (List.mem_cons_of_mem
              head
              member))

/-- The scalar max-width coordinate of the local F(n) profile is at most two. -/
theorem explicitFamilyConstitutiveProfile_width_le_two
    (count : Nat) :
    (explicitFamilyConstitutiveProfile count).maxFrontierWidth ≤
      2 := by
  change
    (explicitFamilyResourceTrajectory count).trajectory.widthTrace.foldl
        Nat.max
        0 ≤
      2
  exact
    foldlNatMax_le
      2
      (explicitFamilyResourceTrajectory count).trajectory.widthTrace
      0
      (Nat.zero_le 2)
      (fun width member =>
        explicitFamilyConstitutiveProfile_widthTrace_le_two
          count
          width
          member)

/-- Every local-profile coordinate is polynomially bounded in concrete inputBits. -/
theorem explicitFamilyConstitutiveProfile_inputPolynomiallyBounded :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      explicitFamilyConstitutiveProfile :=
  { depth :=
      ⟨CostPolynomial.input,
        fun count =>
          explicitFamilyIndex_le_inputBitSize count⟩
    width :=
      ⟨CostPolynomial.constant 2,
        fun count =>
          explicitFamilyConstitutiveProfile_width_le_two count⟩
    syntaxUnits :=
      ⟨costScaleInput 4,
        fun count => by
          change
            4 * count ≤
              4 * explicitFamilyInputBitSize count
          exact
            Nat.mul_le_mul_left
              4
              (explicitFamilyIndex_le_inputBitSize
                count)⟩
    frontierSlots :=
      ⟨costScaleInputPlus 3 1,
        fun count => by
          change
            3 * count + 1 ≤
              3 * explicitFamilyInputBitSize count + 1
          exact
            Nat.add_le_add_right
              (Nat.mul_le_mul_left
                3
                (explicitFamilyIndex_le_inputBitSize
                  count))
              1⟩
    provenance :=
      ⟨CostPolynomial.input,
        fun count =>
          explicitFamilyIndex_le_inputBitSize count⟩
    certificates :=
      ⟨CostPolynomial.input,
        fun count =>
          explicitFamilyIndex_le_inputBitSize count⟩
    relationFind :=
      ⟨costScaleInput 2,
        fun count => by
          change
            2 * count ≤
              2 * explicitFamilyInputBitSize count
          exact
            Nat.mul_le_mul_left
              2
              (explicitFamilyIndex_le_inputBitSize
                count)⟩
    closurePrimitive :=
      ⟨CostPolynomial.constant 0,
        fun _ =>
          Nat.le_refl 0⟩
    closureCandidates :=
      ⟨CostPolynomial.constant 0,
        fun _ =>
          Nat.le_refl 0⟩
    terminal :=
      ⟨CostPolynomial.constant 1,
        fun _ =>
          Nat.le_refl 1⟩
    representationCharge :=
      ⟨explicitFamilyRepresentationCostPolynomial,
        fun count => by
          change
            explicitFamilyRepresentationChargedCost count ≤
              explicitFamilyRepresentationCostPolynomial.eval
                (explicitFamilyInputBitSize count)
          rw [
            explicitFamilyRepresentationCostPolynomial_eval
          ]
          simpa only [
            explicitFamilyInputIndexedPolynomialBudget
          ] using
            explicitFamilyRepresentationChargedCost_le_inputIndexedPolynomial
              count⟩ }

/-- Every composition-phase coordinate is polynomially bounded in inputBits. -/
theorem composedClosureConstitutivePhaseProfile_inputPolynomiallyBounded :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      composedClosureConstitutivePhaseProfile :=
  { depth :=
      ⟨CostPolynomial.constant 2,
        fun _ =>
          Nat.le_refl 2⟩
    width :=
      ⟨CostPolynomial.constant 2,
        fun _ =>
          Nat.le_refl 2⟩
    syntaxUnits :=
      ⟨CostPolynomial.constant 0,
        fun _ =>
          Nat.le_refl 0⟩
    frontierSlots :=
      ⟨CostPolynomial.constant 2,
        fun _ =>
          Nat.le_refl 2⟩
    provenance :=
      ⟨CostPolynomial.constant 0,
        fun _ =>
          Nat.le_refl 0⟩
    certificates :=
      ⟨CostPolynomial.constant 2,
        fun _ =>
          Nat.le_refl 2⟩
    relationFind :=
      ⟨CostPolynomial.constant 0,
        fun _ =>
          Nat.le_refl 0⟩
    closurePrimitive :=
      ⟨CostPolynomial.constant 3,
        fun _ =>
          Nat.le_refl 3⟩
    closureCandidates :=
      ⟨CostPolynomial.constant 1,
        fun _ =>
          Nat.le_refl 1⟩
    terminal :=
      ⟨CostPolynomial.constant 0,
        fun _ =>
          Nat.le_refl 0⟩
    representationCharge :=
      ⟨composedClosurePhaseRepresentationCostPolynomial,
        fun count => by
          change
            composedClosurePhaseRepresentationChargedCost count ≤
              composedClosurePhaseRepresentationCostPolynomial.eval
                (explicitFamilyInputBitSize count)
          rw [
            composedClosurePhaseRepresentationCostPolynomial_eval
          ]
          simpa only [
            composedClosurePhaseInputIndexedPolynomialBudget
          ] using
            composedClosurePhaseRepresentationChargedCost_le_inputIndexedPolynomial
              count⟩ }

/--
The complete local-plus-composition constitutive profile is polynomially
bounded in its own concrete binary input-size coordinate.
-/
theorem explicitFamilyWithCompositionProfile_inputPolynomiallyBounded :
    ConstitutiveProfileFamilyInputPolynomiallyBounded
      explicitFamilyWithCompositionProfile := by
  let composedBounded :
      ConstitutiveProfileFamilyInputPolynomiallyBounded
        (fun count =>
          ConstitutiveComplexityProfile.compose
            (explicitFamilyConstitutiveProfile count)
            (composedClosureConstitutivePhaseProfile count)) :=
    ConstitutiveProfileFamilyInputPolynomiallyBounded.compose
      explicitFamilyConstitutiveProfile_inputPolynomiallyBounded
      composedClosureConstitutivePhaseProfile_inputPolynomiallyBounded
  exact
    { depth := by
        rcases composedBounded.depth with ⟨envelope, bound⟩
        refine ⟨envelope, ?_⟩
        intro count
        change
          (explicitFamilyWithCompositionProfile count).depth ≤
            envelope.eval
              (explicitFamilyWithCompositionProfile count).inputBits
        rw [explicitFamilyWithCompositionProfile_eq_compose]
        exact bound count
      width := by
        rcases composedBounded.width with ⟨envelope, bound⟩
        refine ⟨envelope, ?_⟩
        intro count
        change
          (explicitFamilyWithCompositionProfile count).maxFrontierWidth ≤
            envelope.eval
              (explicitFamilyWithCompositionProfile count).inputBits
        rw [explicitFamilyWithCompositionProfile_eq_compose]
        exact bound count
      syntaxUnits := by
        rcases composedBounded.syntaxUnits with ⟨envelope, bound⟩
        refine ⟨envelope, ?_⟩
        intro count
        change
          (explicitFamilyWithCompositionProfile count).events.syntaxUnits ≤
            envelope.eval
              (explicitFamilyWithCompositionProfile count).inputBits
        rw [explicitFamilyWithCompositionProfile_eq_compose]
        exact bound count
      frontierSlots := by
        rcases composedBounded.frontierSlots with ⟨envelope, bound⟩
        refine ⟨envelope, ?_⟩
        intro count
        change
          (explicitFamilyWithCompositionProfile count).events.frontierSlots ≤
            envelope.eval
              (explicitFamilyWithCompositionProfile count).inputBits
        rw [explicitFamilyWithCompositionProfile_eq_compose]
        exact bound count
      provenance := by
        rcases composedBounded.provenance with ⟨envelope, bound⟩
        refine ⟨envelope, ?_⟩
        intro count
        change
          (explicitFamilyWithCompositionProfile count).events.provenanceUnits ≤
            envelope.eval
              (explicitFamilyWithCompositionProfile count).inputBits
        rw [explicitFamilyWithCompositionProfile_eq_compose]
        exact bound count
      certificates := by
        rcases composedBounded.certificates with ⟨envelope, bound⟩
        refine ⟨envelope, ?_⟩
        intro count
        change
          (explicitFamilyWithCompositionProfile count).events.certificateAtoms ≤
            envelope.eval
              (explicitFamilyWithCompositionProfile count).inputBits
        rw [explicitFamilyWithCompositionProfile_eq_compose]
        exact bound count
      relationFind := by
        rcases composedBounded.relationFind with ⟨envelope, bound⟩
        refine ⟨envelope, ?_⟩
        intro count
        change
          (explicitFamilyWithCompositionProfile count).events.relationFindCalls ≤
            envelope.eval
              (explicitFamilyWithCompositionProfile count).inputBits
        rw [explicitFamilyWithCompositionProfile_eq_compose]
        exact bound count
      closurePrimitive := by
        rcases composedBounded.closurePrimitive with ⟨envelope, bound⟩
        refine ⟨envelope, ?_⟩
        intro count
        change
          (explicitFamilyWithCompositionProfile count).events.closurePrimitiveQueries ≤
            envelope.eval
              (explicitFamilyWithCompositionProfile count).inputBits
        rw [explicitFamilyWithCompositionProfile_eq_compose]
        exact bound count
      closureCandidates := by
        rcases composedBounded.closureCandidates with ⟨envelope, bound⟩
        refine ⟨envelope, ?_⟩
        intro count
        change
          (explicitFamilyWithCompositionProfile count).events.closureCompositionCandidates ≤
            envelope.eval
              (explicitFamilyWithCompositionProfile count).inputBits
        rw [explicitFamilyWithCompositionProfile_eq_compose]
        exact bound count
      terminal := by
        rcases composedBounded.terminal with ⟨envelope, bound⟩
        refine ⟨envelope, ?_⟩
        intro count
        change
          (explicitFamilyWithCompositionProfile count).events.terminalChecks ≤
            envelope.eval
              (explicitFamilyWithCompositionProfile count).inputBits
        rw [explicitFamilyWithCompositionProfile_eq_compose]
        exact bound count
      representationCharge := by
        rcases composedBounded.representationCharge with ⟨envelope, bound⟩
        refine ⟨envelope, ?_⟩
        intro count
        change
          (explicitFamilyWithCompositionProfile count).representationCharge ≤
            envelope.eval
              (explicitFamilyWithCompositionProfile count).inputBits
        rw [explicitFamilyWithCompositionProfile_eq_compose]
        exact bound count }

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.foldlNatMax_le
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutiveProfile_width_le_two
#print axioms ConstitutiveSearch.SAT.explicitFamilyConstitutiveProfile_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.composedClosureConstitutivePhaseProfile_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.SAT.explicitFamilyWithCompositionProfile_inputPolynomiallyBounded
/- AXIOM_AUDIT_END -/
