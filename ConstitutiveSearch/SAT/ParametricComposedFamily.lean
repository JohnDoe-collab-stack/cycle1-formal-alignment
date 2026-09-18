import ConstitutiveSearch.SAT.ExplicitFamilyInputComplexity

/-!
# Parametric SAT family requiring composed structural flips

This module prepares a genuinely SAT-indexed composition benchmark.

For every n, start from the certified endpoint of F(n).  Its formula and
constituted history contain only variables at most n.  Two fresh variables
n+1 and n+2 are then appended structurally.  Four generated states encode the
four Boolean choices on those two fresh variables.

Because the two variables are absent from the inherited formula, a global flip
at n+1 changes only the first new decision and a flip at n+2 changes only the
second.  Hence:

  source --flip(n+1)--> middle --flip(n+2)--> target

while no single announced primitive flip at n+1 or n+2 maps source directly to
target.

This module stops at the primitive search boundary.  The bounded closure search
is connected in the next layer.
-/

namespace ConstitutiveSearch
namespace SAT

namespace Literal

/-- A variable bounded by maximum avoids every strictly larger query. -/
theorem avoidsVar_of_varBounded_lt
    {maximum query : Var}
    {literal : Literal}
    (bounded :
      VarBoundedBy maximum literal)
    (maximumLtQuery :
      maximum < query) :
    AvoidsVar query literal := by
  cases literal with
  | positive var =>
      change var ≤ maximum at bounded
      change var ≠ query
      exact
        Nat.ne_of_lt
          (Nat.lt_of_le_of_lt
            bounded
            maximumLtQuery)
  | negative var =>
      change var ≤ maximum at bounded
      change var ≠ query
      exact
        Nat.ne_of_lt
          (Nat.lt_of_le_of_lt
            bounded
            maximumLtQuery)

end Literal

namespace Clause

/-- A bounded clause avoids every variable strictly above its bound. -/
theorem avoidsVar_of_varsBounded_lt
    {maximum query : Var}
    {clause : Clause}
    (bounded :
      VarsBoundedBy maximum clause)
    (maximumLtQuery :
      maximum < query) :
    AvoidsVar query clause := by
  induction clause with
  | nil =>
      exact True.intro
  | cons literal rest inductionHypothesis =>
      rcases bounded with
        ⟨literalBounded, restBounded⟩
      exact
        ⟨Literal.avoidsVar_of_varBounded_lt
            literalBounded
            maximumLtQuery,
          inductionHypothesis
            restBounded⟩

end Clause

namespace Cnf

/-- Weak residual formation preserves an upper bound on all variable indices. -/
theorem branchResidual_varsBoundedBy
    {maximum : Var}
    (formula : Cnf)
    (var : Var)
    (value : Bool)
    (bounded :
      VarsBoundedBy maximum formula) :
    VarsBoundedBy
      maximum
      (branchResidual formula var value) := by
  induction formula with
  | nil =>
      exact True.intro
  | cons clause rest inductionHypothesis =>
      rcases bounded with
        ⟨clauseBounded, restBounded⟩
      cases hit :
          Clause.containsLiteral
            (Literal.forValue var value)
            clause with
      | false =>
          rw [
            branchResidual_cons_miss
              clause
              rest
              var
              value
              hit
          ]
          exact
            ⟨clauseBounded,
              inductionHypothesis
                restBounded⟩
      | true =>
          rw [
            branchResidual_cons_hit
              clause
              rest
              var
              value
              hit
          ]
          exact
            inductionHypothesis
              restBounded

/-- A bounded CNF avoids every variable strictly above its bound. -/
theorem avoidsVar_of_varsBounded_lt
    {maximum query : Var}
    {formula : Cnf}
    (bounded :
      VarsBoundedBy maximum formula)
    (maximumLtQuery :
      maximum < query) :
    AvoidsVar query formula := by
  induction formula with
  | nil =>
      exact True.intro
  | cons clause rest inductionHypothesis =>
      rcases bounded with
        ⟨clauseBounded, restBounded⟩
      exact
        ⟨Clause.avoidsVar_of_varsBounded_lt
            clauseBounded
            maximumLtQuery,
          inductionHypothesis
            restBounded⟩

end Cnf

namespace StructuralGeneratedFrom

/-- Generated residual formulas preserve every root variable-index bound. -/
theorem formula_varsBoundedBy
    {rootFormula : Cnf}
    {context : StructuralBranchContext}
    {maximum : Var}
    (generated :
      StructuralGeneratedFrom
        rootFormula
        context)
    (rootBounded :
      Cnf.VarsBoundedBy
        maximum
        rootFormula) :
    Cnf.VarsBoundedBy
      maximum
      context.formula := by
  induction generated with
  | root =>
      exact rootBounded
  | @child parent parentGenerated var value fresh inductionHypothesis =>
      change
        Cnf.VarsBoundedBy
          maximum
          (branchResidual
            parent.formula
            var
            value)
      exact
        Cnf.branchResidual_varsBoundedBy
          parent.formula
          var
          value
          inductionHypothesis

end StructuralGeneratedFrom

/-- A bounded decision history avoids every strictly larger variable. -/
theorem structuralDecisionsAvoid_of_varsBounded_lt
    {maximum query : Var} :
    ∀ {decisions : List StructuralBranchDecision},
      StructuralDecisionsVarsBoundedBy
          maximum
          decisions →
        maximum < query →
        StructuralDecisionsAvoid
          query
          decisions
  | [], _bounded, _maximumLtQuery =>
      True.intro
  | decision :: rest, bounded, maximumLtQuery => by
      rcases bounded with
        ⟨decisionBounded, restBounded⟩
      constructor
      · exact
          Nat.ne_of_lt
            (Nat.lt_of_le_of_lt
              decisionBounded
              maximumLtQuery)
      · exact
          structuralDecisionsAvoid_of_varsBounded_lt
            restBounded
            maximumLtQuery

/-- Flipping an avoided variable leaves the complete decision history unchanged. -/
theorem flipStructuralDecisionsAt_eq_self_of_avoids
    {var : Var} :
    ∀ {decisions : List StructuralBranchDecision},
      StructuralDecisionsAvoid var decisions →
        flipStructuralDecisionsAt
            var
            decisions =
          decisions
  | [], _avoids =>
      rfl
  | decision :: rest, avoids => by
      rcases avoids with
        ⟨decisionDifferent, restAvoids⟩
      rw [flipStructuralDecisionsAt]
      rw [
        StructuralBranchDecision.flipAt,
        if_neg decisionDifferent
      ]
      rw [
        flipStructuralDecisionsAt_eq_self_of_avoids
          restAvoids
      ]

/-- Parent state inherited from the certified endpoint of F(n). -/
def composedFamilyParent
    (count : Nat) :
    GeneratedStructuralBranchContext
      (explicitStackedSymmetricFamily count) :=
  (explicitFamilyResourceTrajectory count).finish

/-- First fresh composition variable. -/
def composedFirstVar
    (count : Nat) : Var :=
  count + 1

/-- Second fresh composition variable. -/
def composedSecondVar
    (count : Nat) : Var :=
  count + 2

/-- Every residual variable of the inherited parent is at most n. -/
theorem composedFamilyParent_formula_bounded
    (count : Nat) :
    Cnf.VarsBoundedBy
      count
      (composedFamilyParent count).context.formula :=
  StructuralGeneratedFrom.formula_varsBoundedBy
    (composedFamilyParent count).generated
    (explicitStackedSymmetricFamily_varsBoundedBy
      count)

/-- The inherited parent formula avoids n+1. -/
theorem composedFamilyParent_formula_avoids_first
    (count : Nat) :
    Cnf.AvoidsVar
      (composedFirstVar count)
      (composedFamilyParent count).context.formula :=
  Cnf.avoidsVar_of_varsBounded_lt
    (composedFamilyParent_formula_bounded count)
    (Nat.lt_succ_self count)

/-- The inherited parent formula avoids n+2. -/
theorem composedFamilyParent_formula_avoids_second
    (count : Nat) :
    Cnf.AvoidsVar
      (composedSecondVar count)
      (composedFamilyParent count).context.formula := by
  apply
    Cnf.avoidsVar_of_varsBounded_lt
      (composedFamilyParent_formula_bounded count)
  exact
    Nat.lt_trans
      (Nat.lt_succ_self count)
      (Nat.lt_succ_self (count + 1))

/-- The inherited history avoids n+1. -/
theorem composedFamilyParent_decisions_avoid_first
    (count : Nat) :
    StructuralDecisionsAvoid
      (composedFirstVar count)
      (composedFamilyParent count).context.decisions :=
  structuralDecisionsAvoid_of_varsBounded_lt
    (explicitFamilyEndpoint_decisions_bounded count)
    (Nat.lt_succ_self count)

/-- The inherited history avoids n+2. -/
theorem composedFamilyParent_decisions_avoid_second
    (count : Nat) :
    StructuralDecisionsAvoid
      (composedSecondVar count)
      (composedFamilyParent count).context.decisions := by
  apply
    structuralDecisionsAvoid_of_varsBounded_lt
      (explicitFamilyEndpoint_decisions_bounded count)
  exact
    Nat.lt_trans
      (Nat.lt_succ_self count)
      (Nat.lt_succ_self (count + 1))

/-- First generated child, parameterized by its new Boolean decision. -/
def composedFirstChild
    (count : Nat)
    (firstValue : Bool) :
    GeneratedStructuralBranchContext
      (explicitStackedSymmetricFamily count) :=
  GeneratedStructuralBranchContext.child
    (composedFamilyParent count)
    (composedFirstVar count)
    firstValue
    (composedFamilyParent_decisions_avoid_first
      count)

/-- The second composition variable is fresh after either first decision. -/
theorem composedSecondFresh
    (count : Nat)
    (firstValue : Bool) :
    StructuralDecisionsAvoid
      (composedSecondVar count)
      (composedFirstChild count firstValue).context.decisions := by
  change
    composedFirstVar count ≠
        composedSecondVar count ∧
      StructuralDecisionsAvoid
        (composedSecondVar count)
        (composedFamilyParent count).context.decisions
  constructor
  · exact
      Nat.ne_of_lt
        (Nat.lt_succ_self
          (count + 1))
  · exact
      composedFamilyParent_decisions_avoid_second
        count

/-- Two-decision generated state above the inherited F(n) endpoint. -/
def composedState
    (count : Nat)
    (firstValue secondValue : Bool) :
    GeneratedStructuralBranchContext
      (explicitStackedSymmetricFamily count) :=
  GeneratedStructuralBranchContext.child
    (composedFirstChild count firstValue)
    (composedSecondVar count)
    secondValue
    (composedSecondFresh
      count
      firstValue)

/-- Every state in the composition square has the same residual formula. -/
theorem composedState_formula
    (count : Nat)
    (firstValue secondValue : Bool) :
    (composedState
      count
      firstValue
      secondValue).context.formula =
      (composedFamilyParent count).context.formula := by
  change
    branchResidual
        (branchResidual
          (composedFamilyParent count).context.formula
          (composedFirstVar count)
          firstValue)
        (composedSecondVar count)
        secondValue =
      (composedFamilyParent count).context.formula
  rw [
    Cnf.branchResidual_eq_self
      (composedFamilyParent_formula_avoids_first
        count)
      firstValue
  ]
  rw [
    Cnf.branchResidual_eq_self
      (composedFamilyParent_formula_avoids_second
        count)
      secondValue
  ]

/-- Exact decision history of one state in the composition square. -/
theorem composedState_decisions
    (count : Nat)
    (firstValue secondValue : Bool) :
    (composedState
      count
      firstValue
      secondValue).context.decisions =
      { var := composedSecondVar count,
        value := secondValue } ::
      { var := composedFirstVar count,
        value := firstValue } ::
      (composedFamilyParent count).context.decisions := by
  rfl

/-- Flipping n+1 toggles exactly the first new decision. -/
theorem composedState_decisions_flip_first
    (count : Nat)
    (firstValue secondValue : Bool) :
    (composedState
      count
      (!firstValue)
      secondValue).context.decisions =
      flipStructuralDecisionsAt
        (composedFirstVar count)
        (composedState
          count
          firstValue
          secondValue).context.decisions := by
  rw [
    composedState_decisions,
    composedState_decisions
  ]
  rw [flipStructuralDecisionsAt]
  rw [
    StructuralBranchDecision.flipAt,
    if_neg
      (Nat.ne_of_gt
        (Nat.lt_succ_self
          (count + 1)))
  ]
  rw [flipStructuralDecisionsAt]
  rw [
    StructuralBranchDecision.flipAt,
    if_pos rfl
  ]
  rw [
    flipStructuralDecisionsAt_eq_self_of_avoids
      (composedFamilyParent_decisions_avoid_first
        count)
  ]

/-- Flipping n+2 toggles exactly the second new decision. -/
theorem composedState_decisions_flip_second
    (count : Nat)
    (firstValue secondValue : Bool) :
    (composedState
      count
      firstValue
      (!secondValue)).context.decisions =
      flipStructuralDecisionsAt
        (composedSecondVar count)
        (composedState
          count
          firstValue
          secondValue).context.decisions := by
  rw [
    composedState_decisions,
    composedState_decisions
  ]
  rw [flipStructuralDecisionsAt]
  rw [
    StructuralBranchDecision.flipAt,
    if_pos rfl
  ]
  rw [flipStructuralDecisionsAt]
  rw [
    StructuralBranchDecision.flipAt,
    if_neg
      (Nat.ne_of_lt
        (Nat.lt_succ_self
          (count + 1)))
  ]
  rw [
    flipStructuralDecisionsAt_eq_self_of_avoids
      (composedFamilyParent_decisions_avoid_second
        count)
  ]

/-- Every generated state formula avoids n+1. -/
theorem composedState_formula_avoids_first
    (count : Nat)
    (firstValue secondValue : Bool) :
    Cnf.AvoidsVar
      (composedFirstVar count)
      (composedState
        count
        firstValue
        secondValue).context.formula := by
  rw [
    composedState_formula
      count
      firstValue
      secondValue
  ]
  exact
    composedFamilyParent_formula_avoids_first
      count

/-- Every generated state formula avoids n+2. -/
theorem composedState_formula_avoids_second
    (count : Nat)
    (firstValue secondValue : Bool) :
    Cnf.AvoidsVar
      (composedSecondVar count)
      (composedState
        count
        firstValue
        secondValue).context.formula := by
  rw [
    composedState_formula
      count
      firstValue
      secondValue
  ]
  exact
    composedFamilyParent_formula_avoids_second
      count

/-- Primitive flip relation changing only the first new decision. -/
def composedFlipFirstRelation
    (count : Nat)
    (firstValue secondValue : Bool) :
    GeneratedStructuralFlipAtRelation
      (composedFirstVar count)
      (composedState
        count
        firstValue
        secondValue)
      (composedState
        count
        (!firstValue)
        secondValue) :=
  { formulaExact := by
      calc
        (composedState
          count
          (!firstValue)
          secondValue).context.formula
            =
          (composedFamilyParent count).context.formula :=
            composedState_formula
              count
              (!firstValue)
              secondValue
        _ =
          (composedState
            count
            firstValue
            secondValue).context.formula :=
            (composedState_formula
              count
              firstValue
              secondValue).symm
        _ =
          Cnf.flipAt
            (composedFirstVar count)
            (composedState
              count
              firstValue
              secondValue).context.formula :=
            (Cnf.flipAt_eq_self
              (composedState_formula_avoids_first
                count
                firstValue
                secondValue)).symm
    decisionsExact :=
      composedState_decisions_flip_first
        count
        firstValue
        secondValue }

/-- Primitive flip relation changing only the second new decision. -/
def composedFlipSecondRelation
    (count : Nat)
    (firstValue secondValue : Bool) :
    GeneratedStructuralFlipAtRelation
      (composedSecondVar count)
      (composedState
        count
        firstValue
        secondValue)
      (composedState
        count
        firstValue
        (!secondValue)) :=
  { formulaExact := by
      calc
        (composedState
          count
          firstValue
          (!secondValue)).context.formula
            =
          (composedFamilyParent count).context.formula :=
            composedState_formula
              count
              firstValue
              (!secondValue)
        _ =
          (composedState
            count
            firstValue
            secondValue).context.formula :=
            (composedState_formula
              count
              firstValue
              secondValue).symm
        _ =
          Cnf.flipAt
            (composedSecondVar count)
            (composedState
              count
              firstValue
              secondValue).context.formula :=
            (Cnf.flipAt_eq_self
              (composedState_formula_avoids_second
                count
                firstValue
                secondValue)).symm
    decisionsExact :=
      composedState_decisions_flip_second
        count
        firstValue
        secondValue }

/-- Source, middle, target and alternate states of the composition square. -/
def composedSource
    (count : Nat) :=
  composedState count false false

def composedMiddle
    (count : Nat) :=
  composedState count true false

def composedTarget
    (count : Nat) :=
  composedState count true true

def composedAlternate
    (count : Nat) :=
  composedState count false true

/-- Certified source -> middle primitive relation. -/
def composedSourceMiddleRelation
    (count : Nat) :
    GeneratedStructuralFlipAtRelation
      (composedFirstVar count)
      (composedSource count)
      (composedMiddle count) :=
  composedFlipFirstRelation
    count
    false
    false

/-- Certified source -> alternate primitive relation. -/
def composedSourceAlternateRelation
    (count : Nat) :
    GeneratedStructuralFlipAtRelation
      (composedSecondVar count)
      (composedSource count)
      (composedAlternate count) :=
  composedFlipSecondRelation
    count
    false
    false

/-- Certified middle -> target primitive relation. -/
def composedMiddleTargetRelation
    (count : Nat) :
    GeneratedStructuralFlipAtRelation
      (composedSecondVar count)
      (composedMiddle count)
      (composedTarget count) :=
  composedFlipSecondRelation
    count
    true
    false

/-- Search finds every explicitly supplied exact global flip relation. -/
theorem generatedStructuralFlipAtSearch_found_of_relation
    {rootFormula : Cnf}
    {var : Var}
    {source target :
      GeneratedStructuralBranchContext rootFormula}
    (relation :
      GeneratedStructuralFlipAtRelation
        var
        source
        target) :
    (generatedStructuralFlipAtSearch
      rootFormula
      var).find source target ≠
      none := by
  unfold generatedStructuralFlipAtSearch
  rw [dif_pos relation.formulaExact]
  rw [dif_pos relation.decisionsExact]
  intro impossible
  cases impossible

/-- A known history mismatch forces exact global flip search to return none. -/
theorem generatedStructuralFlipAtSearch_none_of_decisions_ne
    {rootFormula : Cnf}
    {var : Var}
    {source target :
      GeneratedStructuralBranchContext rootFormula}
    (different :
      target.context.decisions ≠
        flipStructuralDecisionsAt
          var
          source.context.decisions) :
    (generatedStructuralFlipAtSearch
      rootFormula
      var).find source target =
      none := by
  unfold generatedStructuralFlipAtSearch
  by_cases formulaExact :
      target.context.formula =
        Cnf.flipAt
          var
          source.context.formula
  · rw [dif_pos formulaExact]
    rw [dif_neg different]
  · rw [dif_neg formulaExact]

/--
Executable primitive search over exactly the two announced fresh flip
generators.  No satisfiability query occurs.
-/
def composedPrimitiveSearch
    (count : Nat) :
    RelationSearch
      (GeneratedStructuralFlipWitness
        (rootFormula :=
          explicitStackedSymmetricFamily count)) :=
  { find := fun source target =>
      match
        (generatedStructuralFlipAtSearch
          (explicitStackedSymmetricFamily count)
          (composedFirstVar count)).find
            source
            target with
      | some relation =>
          some
            { var := composedFirstVar count
              relation := relation }
      | none =>
          match
            (generatedStructuralFlipAtSearch
              (explicitStackedSymmetricFamily count)
              (composedSecondVar count)).find
                source
                target with
          | some relation =>
              some
                { var := composedSecondVar count
                  relation := relation }
          | none =>
              none }

/-- Source and target cannot be related by the first primitive flip. -/
theorem composedSourceTarget_not_first
    (count : Nat) :
    (composedTarget count).context.decisions ≠
      flipStructuralDecisionsAt
        (composedFirstVar count)
        (composedSource count).context.decisions := by
  intro exactHistory
  have targetMiddle :
      (composedTarget count).context.decisions =
        (composedMiddle count).context.decisions :=
    Eq.trans
      exactHistory
      (composedSourceMiddleRelation
        count).decisionsExact.symm
  change
    ({ var := composedSecondVar count, value := true } ::
      { var := composedFirstVar count, value := true } ::
      (composedFamilyParent count).context.decisions) =
    ({ var := composedSecondVar count, value := false } ::
      { var := composedFirstVar count, value := true } ::
      (composedFamilyParent count).context.decisions) at targetMiddle
  injection targetMiddle with headEqual tailEqual
  have valueEqual :
      true = false :=
    congrArg
      StructuralBranchDecision.value
      headEqual
  cases valueEqual

/-- Source and target cannot be related by the second primitive flip. -/
theorem composedSourceTarget_not_second
    (count : Nat) :
    (composedTarget count).context.decisions ≠
      flipStructuralDecisionsAt
        (composedSecondVar count)
        (composedSource count).context.decisions := by
  intro exactHistory
  have targetAlternate :
      (composedTarget count).context.decisions =
        (composedAlternate count).context.decisions :=
    Eq.trans
      exactHistory
      (composedSourceAlternateRelation
        count).decisionsExact.symm
  change
    ({ var := composedSecondVar count, value := true } ::
      { var := composedFirstVar count, value := true } ::
      (composedFamilyParent count).context.decisions) =
    ({ var := composedSecondVar count, value := true } ::
      { var := composedFirstVar count, value := false } ::
      (composedFamilyParent count).context.decisions) at targetAlternate
  injection targetAlternate with headEqual tailEqual
  injection tailEqual with firstEqual restEqual
  have valueEqual :
      true = false :=
    congrArg
      StructuralBranchDecision.value
      firstEqual
  cases valueEqual

/-- No announced primitive relation directly connects source to target. -/
theorem composedPrimitiveSearch_source_target_none
    (count : Nat) :
    (composedPrimitiveSearch count).find
        (composedSource count)
        (composedTarget count) =
      none := by
  unfold composedPrimitiveSearch
  rw [
    generatedStructuralFlipAtSearch_none_of_decisions_ne
      (composedSourceTarget_not_first count)
  ]
  rw [
    generatedStructuralFlipAtSearch_none_of_decisions_ne
      (composedSourceTarget_not_second count)
  ]

/-- The announced primitive search does find source -> middle. -/
theorem composedPrimitiveSearch_source_middle_present
    (count : Nat) :
    (composedPrimitiveSearch count).find
        (composedSource count)
        (composedMiddle count) ≠
      none := by
  unfold composedPrimitiveSearch
  have found :=
    generatedStructuralFlipAtSearch_found_of_relation
      (composedSourceMiddleRelation count)
  cases result :
      (generatedStructuralFlipAtSearch
        (explicitStackedSymmetricFamily count)
        (composedFirstVar count)).find
          (composedSource count)
          (composedMiddle count) with
  | none =>
      exact False.elim (found result)
  | some relation =>
      intro impossible
      cases impossible

/-- The announced primitive search does find middle -> target. -/
theorem composedPrimitiveSearch_middle_target_present
    (count : Nat) :
    (composedPrimitiveSearch count).find
        (composedMiddle count)
        (composedTarget count) ≠
      none := by
  unfold composedPrimitiveSearch
  cases firstResult :
      (generatedStructuralFlipAtSearch
        (explicitStackedSymmetricFamily count)
        (composedFirstVar count)).find
          (composedMiddle count)
          (composedTarget count) with
  | some relation =>
      intro impossible
      cases impossible
  | none =>
      have found :=
        generatedStructuralFlipAtSearch_found_of_relation
          (composedMiddleTargetRelation count)
      cases secondResult :
          (generatedStructuralFlipAtSearch
            (explicitStackedSymmetricFamily count)
            (composedSecondVar count)).find
              (composedMiddle count)
              (composedTarget count) with
      | none =>
          exact False.elim (found secondResult)
      | some relation =>
          intro impossible
          cases impossible

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.Cnf.branchResidual_varsBoundedBy
#print axioms ConstitutiveSearch.SAT.StructuralGeneratedFrom.formula_varsBoundedBy
#print axioms ConstitutiveSearch.SAT.structuralDecisionsAvoid_of_varsBounded_lt
#print axioms ConstitutiveSearch.SAT.flipStructuralDecisionsAt_eq_self_of_avoids
#print axioms ConstitutiveSearch.SAT.composedFamilyParent
#print axioms ConstitutiveSearch.SAT.composedState
#print axioms ConstitutiveSearch.SAT.composedState_formula
#print axioms ConstitutiveSearch.SAT.composedState_decisions_flip_first
#print axioms ConstitutiveSearch.SAT.composedState_decisions_flip_second
#print axioms ConstitutiveSearch.SAT.composedFlipFirstRelation
#print axioms ConstitutiveSearch.SAT.composedFlipSecondRelation
#print axioms ConstitutiveSearch.SAT.composedPrimitiveSearch
#print axioms ConstitutiveSearch.SAT.composedPrimitiveSearch_source_target_none
#print axioms ConstitutiveSearch.SAT.composedPrimitiveSearch_source_middle_present
#print axioms ConstitutiveSearch.SAT.composedPrimitiveSearch_middle_target_present
/- AXIOM_AUDIT_END -/
