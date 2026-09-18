import ConstitutiveSearch.SAT.ParametricComposedComplexity

/-!
# Binary representation charges for the SAT composition phase

The composition benchmark adds two fresh decisions above the certified endpoint
of F(n).  This module bounds the binary representation of every state in the
composition square and assigns concrete representation charges to the event
profile already certified in ParametricComposedComplexity.

One closure primitive query invokes the announced primitive engine, which may
perform at most two structural flip comparisons.  Its atomic representation
charge is therefore conservatively set to twice the uniform single-flip
equality envelope.
-/

namespace ConstitutiveSearch
namespace SAT

namespace StructuralGeneratedFrom

/-- Generated residual syntax never exceeds the binary size of its root CNF. -/
theorem formula_binarySize_le_root
    {rootFormula : Cnf}
    {context : StructuralBranchContext}
    (generated :
      StructuralGeneratedFrom rootFormula context) :
    Cnf.binarySize context.formula ≤
      Cnf.binarySize rootFormula := by
  induction generated with
  | root =>
      exact Nat.le_refl _
  | @child parent parentGenerated var value fresh inductionHypothesis =>
      change
        Cnf.binarySize
            (branchResidual parent.formula var value) ≤
          Cnf.binarySize rootFormula
      exact
        Nat.le_trans
          (Cnf.branchResidual_binarySize_le
            parent.formula
            var
            value)
          inductionHypothesis

end StructuralGeneratedFrom

namespace StructuralDecisionsVarsBoundedBy

/-- Raising the variable ceiling preserves a bounded-history witness. -/
theorem mono
    {lower upper : Var}
    (lowerLeUpper : lower ≤ upper) :
    ∀ {decisions : List StructuralBranchDecision},
      StructuralDecisionsVarsBoundedBy lower decisions →
        StructuralDecisionsVarsBoundedBy upper decisions := by
  intro decisions bounded
  induction decisions with
  | nil =>
      exact True.intro
  | cons decision rest inductionHypothesis =>
      rcases bounded with
        ⟨headBounded, tailBounded⟩
      exact
        ⟨Nat.le_trans
            headBounded
            lowerLeUpper,
          inductionHypothesis
            tailBounded⟩

end StructuralDecisionsVarsBoundedBy

/-- Uniform history budget for any state in the two-bit composition square. -/
def composedHistoryBinaryBudget
    (count : Nat) : Nat :=
  StructuralDecisionHistory.binaryBudget
    (count + 2)
    (count + 2)

/-- Uniform encoded state envelope for the composition square. -/
def composedStateBinaryBudget
    (count : Nat) : Nat :=
  explicitFamilyBinaryBudget count +
    composedHistoryBinaryBudget count

/-- Uniform equality charge for one structural flip comparison on square states. -/
def composedSingleFlipEqualityBinaryBudget
    (count : Nat) : Nat :=
  uniformGeneratedFlipEqualityCharge
    (explicitFamilyBinaryBudget count)
    (composedHistoryBinaryBudget count)

/--
One announced primitive query may try both fresh flip generators, hence at most
two structural flip equality surfaces.
-/
def composedPrimitiveQueryBinaryBudget
    (count : Nat) : Nat :=
  composedSingleFlipEqualityBinaryBudget count +
    composedSingleFlipEqualityBinaryBudget count

/-- Tagged certificate-atom envelope for variables bounded by n+2. -/
def composedCertificateAtomBinaryBudget
    (count : Nat) : Nat :=
  (count + 2) + 2

/-- Every square-state history has exactly n+2 decisions. -/
theorem composedState_decisions_length
    (count : Nat)
    (firstValue secondValue : Bool) :
    (composedState
      count
      firstValue
      secondValue).context.decisions.length =
      count + 2 := by
  rw [
    composedState_decisions
      count
      firstValue
      secondValue
  ]
  change
    Nat.succ
        (Nat.succ
          (composedFamilyParent count).context.decisions.length) =
      count + 2
  have parentLength :
      (composedFamilyParent count).context.decisions.length =
        count := by
    unfold composedFamilyParent
    exact
      explicitFamilyEndpoint_decisions_length count
  rw [parentLength]
  rfl

/-- Every square-state decision variable is bounded by n+2. -/
theorem composedState_decisions_bounded
    (count : Nat)
    (firstValue secondValue : Bool) :
    StructuralDecisionsVarsBoundedBy
      (count + 2)
      (composedState
        count
        firstValue
        secondValue).context.decisions := by
  rw [
    composedState_decisions
      count
      firstValue
      secondValue
  ]
  change
    composedSecondVar count ≤ count + 2 ∧
      (composedFirstVar count ≤ count + 2 ∧
        StructuralDecisionsVarsBoundedBy
          (count + 2)
          (composedFamilyParent count).context.decisions)
  constructor
  · unfold composedSecondVar
    exact Nat.le_refl _
  · constructor
    · unfold composedFirstVar
      exact Nat.le_succ (count + 1)
    · have endpointBounded :
          StructuralDecisionsVarsBoundedBy
            count
            (composedFamilyParent count).context.decisions := by
        unfold composedFamilyParent
        exact
          explicitFamilyEndpoint_decisions_bounded count
      have countLe :
          count ≤ count + 2 := by
        exact
          Nat.le_trans
            (Nat.le_succ count)
            (Nat.le_succ (count + 1))
      exact
        StructuralDecisionsVarsBoundedBy.mono
          countLe
          endpointBounded

/-- Every square-state history fits the uniform n+2 history budget. -/
theorem composedState_historyBinarySize_le_budget
    (count : Nat)
    (firstValue secondValue : Bool) :
    StructuralDecisionHistory.binarySize
        (composedState
          count
          firstValue
          secondValue).context.decisions ≤
      composedHistoryBinaryBudget count := by
  calc
    StructuralDecisionHistory.binarySize
        (composedState
          count
          firstValue
          secondValue).context.decisions
        ≤
      StructuralDecisionHistory.binaryBudget
        (count + 2)
        (composedState
          count
          firstValue
          secondValue).context.decisions.length :=
      StructuralDecisionHistory.binarySize_le_budget
        (composedState_decisions_bounded
          count
          firstValue
          secondValue)
    _ =
      composedHistoryBinaryBudget count := by
        unfold composedHistoryBinaryBudget
        rw [
          composedState_decisions_length
            count
            firstValue
            secondValue
        ]

/-- Every square-state residual formula fits the original F(n) formula budget. -/
theorem composedState_formulaBinarySize_le_budget
    (count : Nat)
    (firstValue secondValue : Bool) :
    Cnf.binarySize
        (composedState
          count
          firstValue
          secondValue).context.formula ≤
      explicitFamilyBinaryBudget count := by
  exact
    Nat.le_trans
      (StructuralGeneratedFrom.formula_binarySize_le_root
        (composedState
          count
          firstValue
          secondValue).generated)
      (explicitFamily_binarySize_le_budget count)

/-- Any structural flip comparison between square states fits one common budget. -/
theorem composedState_flipEqualityCharge_le_budget
    (count : Nat)
    (var : Var)
    (sourceFirst sourceSecond targetFirst targetSecond : Bool) :
    generatedFlipEqualityCharge
        var
        (composedState
          count
          sourceFirst
          sourceSecond)
        (composedState
          count
          targetFirst
          targetSecond) ≤
      composedSingleFlipEqualityBinaryBudget count := by
  unfold composedSingleFlipEqualityBinaryBudget
  apply
    generatedFlipEqualityCharge_le
      var
      (composedState
        count
        sourceFirst
        sourceSecond)
      (composedState
        count
        targetFirst
        targetSecond)
      (explicitFamilyBinaryBudget count)
      (composedHistoryBinaryBudget count)
  · exact
      composedState_formulaBinarySize_le_budget
        count
        sourceFirst
        sourceSecond
  · exact
      composedState_formulaBinarySize_le_budget
        count
        targetFirst
        targetSecond
  · exact
      composedState_historyBinarySize_le_budget
        count
        sourceFirst
        sourceSecond
  · exact
      composedState_historyBinarySize_le_budget
        count
        targetFirst
        targetSecond

namespace GeneratedStructuralFlipWitness

/-- Representation charge of one primitive flip witness tag plus its variable. -/
def binarySize
    {rootFormula : Cnf}
    {source target :
      GeneratedStructuralBranchContext rootFormula}
    (witness :
      GeneratedStructuralFlipWitness source target) :
    Nat :=
  Nat.succ
    (BinaryRepresentation.natBitSize
      witness.var)

/-- A variable ceiling gives a coarse binary charge for one packaged witness. -/
theorem binarySize_le_of_var_le
    {rootFormula : Cnf}
    {source target :
      GeneratedStructuralBranchContext rootFormula}
    {witness :
      GeneratedStructuralFlipWitness source target}
    {maximum : Var}
    (bounded :
      witness.var ≤ maximum) :
    witness.binarySize ≤ maximum + 2 := by
  have bitLe :
      BinaryRepresentation.natBitSize witness.var ≤
        maximum + 1 :=
    Nat.le_trans
      (BinaryRepresentation.natBitSize_le_succ
        witness.var)
      (Nat.add_le_add_right
        bounded
        1)
  change
    Nat.succ
        (BinaryRepresentation.natBitSize witness.var) ≤
      Nat.succ (maximum + 1)
  exact
    Nat.succ_le_succ bitLe

end GeneratedStructuralFlipWitness

/-- The first primitive witness fits the common n+2 certificate envelope. -/
theorem composedSourceMiddleWitness_binarySize_le_budget
    (count : Nat) :
    (composedSourceMiddleWitness count).binarySize ≤
      composedCertificateAtomBinaryBudget count := by
  unfold composedCertificateAtomBinaryBudget
  apply
    GeneratedStructuralFlipWitness.binarySize_le_of_var_le
  change
    composedFirstVar count ≤ count + 2
  unfold composedFirstVar
  exact Nat.le_succ (count + 1)

/-- The second primitive witness fits the common n+2 certificate envelope. -/
theorem composedMiddleTargetWitness_binarySize_le_budget
    (count : Nat) :
    (composedMiddleTargetWitness count).binarySize ≤
      composedCertificateAtomBinaryBudget count := by
  unfold composedCertificateAtomBinaryBudget
  apply
    GeneratedStructuralFlipWitness.binarySize_le_of_var_le
  change
    composedSecondVar count ≤ count + 2
  unfold composedSecondVar
  exact Nat.le_refl _

/-- Concrete representation charges assigned to the added composition phase. -/
def composedClosurePhaseRepresentationAtomicCosts
    (count : Nat) : AtomicCosts :=
  { syntaxUnit := 1
    frontierSlot :=
      composedStateBinaryBudget count
    provenanceUnit :=
      StructuralDecisionHistory.binaryBudget
        (count + 2)
        1
    certificateAtom :=
      composedCertificateAtomBinaryBudget count
    relationFindCall :=
      composedSingleFlipEqualityBinaryBudget count
    closurePrimitiveQuery :=
      composedPrimitiveQueryBinaryBudget count
    closureCompositionCandidate :=
      composedStateBinaryBudget count
    terminalCheck :=
      composedHistoryBinaryBudget count }

/-- Aggregate binary representation charge of the added composition phase. -/
def composedClosurePhaseRepresentationChargedCost
    (count : Nat) : Nat :=
  composedClosurePhaseChargedCost
    count
    (composedClosurePhaseRepresentationAtomicCosts count)

/-- Closed binary representation budget for the composition phase. -/
def composedClosurePhaseRepresentationBudget
    (count : Nat) : Nat :=
  2 * composedStateBinaryBudget count +
    (2 * composedCertificateAtomBinaryBudget count +
      (3 * composedPrimitiveQueryBinaryBudget count +
        composedStateBinaryBudget count))

/-- The charged composition-phase cost equals its explicit representation budget. -/
theorem composedClosurePhaseRepresentationChargedCost_eq_budget
    (count : Nat) :
    composedClosurePhaseRepresentationChargedCost count =
      composedClosurePhaseRepresentationBudget count := by
  unfold composedClosurePhaseRepresentationChargedCost
  rw [
    composedClosurePhaseChargedCost_eq_budget
      count
      (composedClosurePhaseRepresentationAtomicCosts count)
  ]
  rfl

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.StructuralGeneratedFrom.formula_binarySize_le_root
#print axioms ConstitutiveSearch.SAT.StructuralDecisionsVarsBoundedBy.mono
#print axioms ConstitutiveSearch.SAT.composedHistoryBinaryBudget
#print axioms ConstitutiveSearch.SAT.composedStateBinaryBudget
#print axioms ConstitutiveSearch.SAT.composedSingleFlipEqualityBinaryBudget
#print axioms ConstitutiveSearch.SAT.composedPrimitiveQueryBinaryBudget
#print axioms ConstitutiveSearch.SAT.composedCertificateAtomBinaryBudget
#print axioms ConstitutiveSearch.SAT.composedState_decisions_length
#print axioms ConstitutiveSearch.SAT.composedState_decisions_bounded
#print axioms ConstitutiveSearch.SAT.composedState_historyBinarySize_le_budget
#print axioms ConstitutiveSearch.SAT.composedState_formulaBinarySize_le_budget
#print axioms ConstitutiveSearch.SAT.composedState_flipEqualityCharge_le_budget
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralFlipWitness.binarySize
#print axioms ConstitutiveSearch.SAT.GeneratedStructuralFlipWitness.binarySize_le_of_var_le
#print axioms ConstitutiveSearch.SAT.composedSourceMiddleWitness_binarySize_le_budget
#print axioms ConstitutiveSearch.SAT.composedMiddleTargetWitness_binarySize_le_budget
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseRepresentationAtomicCosts
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseRepresentationChargedCost
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseRepresentationBudget
#print axioms ConstitutiveSearch.SAT.composedClosurePhaseRepresentationChargedCost_eq_budget
/- AXIOM_AUDIT_END -/
