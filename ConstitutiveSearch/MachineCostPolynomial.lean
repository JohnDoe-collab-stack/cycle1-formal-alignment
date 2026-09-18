import ConstitutiveSearch.ConstitutiveComplexityInputPolynomial
import ConstitutiveSearch.MachineCostInterface

/-!
# Polynomial machine calibration for constitutive complexity

MachineCostInterface keeps representation charge and machine cost distinct.
This module adds the asymptotic closure theorem needed for that separation.

If:
* event-count coordinates are polynomially bounded in a concrete input-size
  function;
* representation-level atomic costs are polynomially bounded in the same input
  size;
* machine atomic costs are pointwise below one fixed affine calibration of the
  representation costs;

then the aggregate calibrated machine budget, and hence the bridged machine
cost, are polynomially bounded in that input size.

The bridge remains an explicit hypothesis.
-/

namespace ConstitutiveSearch

namespace InputPolynomiallyBounded

/-- Pointwise addition under one fixed input-size function. -/
theorem add_same
    {inputBits left right : Nat → Nat}
    (leftBounded :
      InputPolynomiallyBounded inputBits left)
    (rightBounded :
      InputPolynomiallyBounded inputBits right) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        left n + right n) := by
  rcases leftBounded with
    ⟨leftEnvelope, leftLe⟩
  rcases rightBounded with
    ⟨rightEnvelope, rightLe⟩
  exact
    ⟨CostPolynomial.add
        leftEnvelope
        rightEnvelope,
      fun n =>
        Nat.add_le_add
          (leftLe n)
          (rightLe n)⟩

/-- Pointwise multiplication under one fixed input-size function. -/
theorem mul_same
    {inputBits left right : Nat → Nat}
    (leftBounded :
      InputPolynomiallyBounded inputBits left)
    (rightBounded :
      InputPolynomiallyBounded inputBits right) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        left n * right n) := by
  rcases leftBounded with
    ⟨leftEnvelope, leftLe⟩
  rcases rightBounded with
    ⟨rightEnvelope, rightLe⟩
  exact
    ⟨CostPolynomial.mul
        leftEnvelope
        rightEnvelope,
      fun n =>
        PolynomiallyBounded.natMulLeMul
          (leftLe n)
          (rightLe n)⟩

/-- Domination by an input-polynomial cost transfers polynomial boundedness. -/
theorem of_le
    {inputBits lower upper : Nat → Nat}
    (upperBounded :
      InputPolynomiallyBounded inputBits upper)
    (lowerLe :
      ∀ n : Nat,
        lower n ≤ upper n) :
    InputPolynomiallyBounded
      inputBits
      lower := by
  rcases upperBounded with
    ⟨envelope, upperLe⟩
  exact
    ⟨envelope,
      fun n =>
        Nat.le_trans
          (lowerLe n)
          (upperLe n)⟩

end InputPolynomiallyBounded

/-- Polynomial event-count coordinates under one concrete input-size function. -/
structure ComplexityCountsFamilyInputPolynomiallyBounded
    (inputBits : Nat → Nat)
    (counts : Nat → ComplexityCounts) : Prop where
  syntaxUnits :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (counts n).syntaxUnits)
  frontierSlots :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (counts n).frontierSlots)
  provenanceUnits :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (counts n).provenanceUnits)
  certificateAtoms :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (counts n).certificateAtoms)
  relationFindCalls :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (counts n).relationFindCalls)
  closurePrimitiveQueries :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (counts n).closurePrimitiveQueries)
  closureCompositionCandidates :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (counts n).closureCompositionCandidates)
  terminalChecks :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (counts n).terminalChecks)

/-- Polynomial atomic representation costs under one concrete input-size function. -/
structure AtomicCostsFamilyInputPolynomiallyBounded
    (inputBits : Nat → Nat)
    (costs : Nat → AtomicCosts) : Prop where
  syntaxUnit :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (costs n).syntaxUnit)
  frontierSlot :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (costs n).frontierSlot)
  provenanceUnit :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (costs n).provenanceUnit)
  certificateAtom :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (costs n).certificateAtom)
  relationFindCall :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (costs n).relationFindCall)
  closurePrimitiveQuery :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (costs n).closurePrimitiveQuery)
  closureCompositionCandidate :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (costs n).closureCompositionCandidate)
  terminalCheck :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        (costs n).terminalCheck)

namespace ComplexityCountsFamilyInputPolynomiallyBounded

/-- Extract polynomial event counts from a polynomial constitutive profile family. -/
theorem ofProfile
    {profile : Nat → ConstitutiveComplexityProfile}
    (bounded :
      ConstitutiveProfileFamilyInputPolynomiallyBounded
        profile) :
    ComplexityCountsFamilyInputPolynomiallyBounded
      (fun n =>
        (profile n).inputBits)
      (fun n =>
        (profile n).events) :=
  { syntaxUnits := bounded.syntaxUnits
    frontierSlots := bounded.frontierSlots
    provenanceUnits := bounded.provenance
    certificateAtoms := bounded.certificates
    relationFindCalls := bounded.relationFind
    closurePrimitiveQueries := bounded.closurePrimitive
    closureCompositionCandidates := bounded.closureCandidates
    terminalChecks := bounded.terminal }

end ComplexityCountsFamilyInputPolynomiallyBounded

namespace AtomicCostsFamilyInputPolynomiallyBounded

/-- Fixed affine calibration preserves polynomial atomic-cost envelopes. -/
theorem affine
    {inputBits : Nat → Nat}
    {representation : Nat → AtomicCosts}
    (bounded :
      AtomicCostsFamilyInputPolynomiallyBounded
        inputBits
        representation)
    (factor overhead : Nat) :
    AtomicCostsFamilyInputPolynomiallyBounded
      inputBits
      (fun n =>
        affineAtomicEnvelope
          (representation n)
          factor
          overhead) :=
  { syntaxUnit :=
      InputPolynomiallyBounded.add_same
        (InputPolynomiallyBounded.mul_same
          (InputPolynomiallyBounded.constant
            inputBits
            factor)
          bounded.syntaxUnit)
        (InputPolynomiallyBounded.constant
          inputBits
          overhead)
    frontierSlot :=
      InputPolynomiallyBounded.add_same
        (InputPolynomiallyBounded.mul_same
          (InputPolynomiallyBounded.constant
            inputBits
            factor)
          bounded.frontierSlot)
        (InputPolynomiallyBounded.constant
          inputBits
          overhead)
    provenanceUnit :=
      InputPolynomiallyBounded.add_same
        (InputPolynomiallyBounded.mul_same
          (InputPolynomiallyBounded.constant
            inputBits
            factor)
          bounded.provenanceUnit)
        (InputPolynomiallyBounded.constant
          inputBits
          overhead)
    certificateAtom :=
      InputPolynomiallyBounded.add_same
        (InputPolynomiallyBounded.mul_same
          (InputPolynomiallyBounded.constant
            inputBits
            factor)
          bounded.certificateAtom)
        (InputPolynomiallyBounded.constant
          inputBits
          overhead)
    relationFindCall :=
      InputPolynomiallyBounded.add_same
        (InputPolynomiallyBounded.mul_same
          (InputPolynomiallyBounded.constant
            inputBits
            factor)
          bounded.relationFindCall)
        (InputPolynomiallyBounded.constant
          inputBits
          overhead)
    closurePrimitiveQuery :=
      InputPolynomiallyBounded.add_same
        (InputPolynomiallyBounded.mul_same
          (InputPolynomiallyBounded.constant
            inputBits
            factor)
          bounded.closurePrimitiveQuery)
        (InputPolynomiallyBounded.constant
          inputBits
          overhead)
    closureCompositionCandidate :=
      InputPolynomiallyBounded.add_same
        (InputPolynomiallyBounded.mul_same
          (InputPolynomiallyBounded.constant
            inputBits
            factor)
          bounded.closureCompositionCandidate)
        (InputPolynomiallyBounded.constant
          inputBits
          overhead)
    terminalCheck :=
      InputPolynomiallyBounded.add_same
        (InputPolynomiallyBounded.mul_same
          (InputPolynomiallyBounded.constant
            inputBits
            factor)
          bounded.terminalCheck)
        (InputPolynomiallyBounded.constant
          inputBits
          overhead) }

end AtomicCostsFamilyInputPolynomiallyBounded

/-- Aggregate charged cost of polynomial counts and polynomial atomic costs is polynomial. -/
theorem chargedCost_inputPolynomiallyBounded
    {inputBits : Nat → Nat}
    {counts : Nat → ComplexityCounts}
    {costs : Nat → AtomicCosts}
    (countsBounded :
      ComplexityCountsFamilyInputPolynomiallyBounded
        inputBits
        counts)
    (costsBounded :
      AtomicCostsFamilyInputPolynomiallyBounded
        inputBits
        costs) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        chargedCost
          (counts n)
          (costs n)) := by
  have syntaxCost :=
    InputPolynomiallyBounded.mul_same
      countsBounded.syntaxUnits
      costsBounded.syntaxUnit
  have frontierCost :=
    InputPolynomiallyBounded.mul_same
      countsBounded.frontierSlots
      costsBounded.frontierSlot
  have provenanceCost :=
    InputPolynomiallyBounded.mul_same
      countsBounded.provenanceUnits
      costsBounded.provenanceUnit
  have certificateCost :=
    InputPolynomiallyBounded.mul_same
      countsBounded.certificateAtoms
      costsBounded.certificateAtom
  have relationCost :=
    InputPolynomiallyBounded.mul_same
      countsBounded.relationFindCalls
      costsBounded.relationFindCall
  have closurePrimitiveCost :=
    InputPolynomiallyBounded.mul_same
      countsBounded.closurePrimitiveQueries
      costsBounded.closurePrimitiveQuery
  have closureCandidateCost :=
    InputPolynomiallyBounded.mul_same
      countsBounded.closureCompositionCandidates
      costsBounded.closureCompositionCandidate
  have terminalCost :=
    InputPolynomiallyBounded.mul_same
      countsBounded.terminalChecks
      costsBounded.terminalCheck
  simpa only [chargedCost] using
    InputPolynomiallyBounded.add_same
      syntaxCost
      (InputPolynomiallyBounded.add_same
        frontierCost
        (InputPolynomiallyBounded.add_same
          provenanceCost
          (InputPolynomiallyBounded.add_same
            certificateCost
            (InputPolynomiallyBounded.add_same
              relationCost
              (InputPolynomiallyBounded.add_same
                closurePrimitiveCost
                (InputPolynomiallyBounded.add_same
                  closureCandidateCost
                  terminalCost))))))

/-- A fixed affine representation calibration has polynomial aggregate budget. -/
theorem representationCalibratedMachineBudget_inputPolynomiallyBounded
    {inputBits : Nat → Nat}
    {counts : Nat → ComplexityCounts}
    {representation : Nat → AtomicCosts}
    (countsBounded :
      ComplexityCountsFamilyInputPolynomiallyBounded
        inputBits
        counts)
    (representationBounded :
      AtomicCostsFamilyInputPolynomiallyBounded
        inputBits
        representation)
    (factor overhead : Nat) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        representationCalibratedMachineBudget
          (counts n)
          (representation n)
          factor
          overhead) := by
  change
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        chargedCost
          (counts n)
          (affineAtomicEnvelope
            (representation n)
            factor
            overhead))
  exact
    chargedCost_inputPolynomiallyBounded
      countsBounded
      (AtomicCostsFamilyInputPolynomiallyBounded.affine
        representationBounded
        factor
        overhead)

/--
Under an explicit pointwise representation-to-machine bridge with fixed
calibration constants, aggregate machine cost is polynomially bounded.
-/
theorem machineChargedCost_inputPolynomiallyBounded
    {inputBits : Nat → Nat}
    {counts : Nat → ComplexityCounts}
    {representation : Nat → AtomicCosts}
    {machine : Nat → MachineCostModel}
    (countsBounded :
      ComplexityCountsFamilyInputPolynomiallyBounded
        inputBits
        counts)
    (representationBounded :
      AtomicCostsFamilyInputPolynomiallyBounded
        inputBits
        representation)
    (factor overhead : Nat)
    (bridges :
      ∀ n : Nat,
        RepresentationMachineBridge
          (representation n)
          (machine n)
          factor
          overhead) :
    InputPolynomiallyBounded
      inputBits
      (fun n =>
        machineChargedCost
          (counts n)
          (machine n)) := by
  apply
    InputPolynomiallyBounded.of_le
      (representationCalibratedMachineBudget_inputPolynomiallyBounded
        countsBounded
        representationBounded
        factor
        overhead)
  intro n
  exact
    machineChargedCost_le_calibrated
      (counts n)
      (representation n)
      (machine n)
      factor
      overhead
      (bridges n)

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.InputPolynomiallyBounded.add_same
#print axioms ConstitutiveSearch.InputPolynomiallyBounded.mul_same
#print axioms ConstitutiveSearch.InputPolynomiallyBounded.of_le
#print axioms ConstitutiveSearch.ComplexityCountsFamilyInputPolynomiallyBounded
#print axioms ConstitutiveSearch.AtomicCostsFamilyInputPolynomiallyBounded
#print axioms ConstitutiveSearch.ComplexityCountsFamilyInputPolynomiallyBounded.ofProfile
#print axioms ConstitutiveSearch.AtomicCostsFamilyInputPolynomiallyBounded.affine
#print axioms ConstitutiveSearch.chargedCost_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.representationCalibratedMachineBudget_inputPolynomiallyBounded
#print axioms ConstitutiveSearch.machineChargedCost_inputPolynomiallyBounded
/- AXIOM_AUDIT_END -/
