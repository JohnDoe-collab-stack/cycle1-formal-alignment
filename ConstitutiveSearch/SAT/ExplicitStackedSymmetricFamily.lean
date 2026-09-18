import ConstitutiveSearch.SAT.ParametricSymmetricTrajectory

/-!
# Explicit stacked symmetric SAT family

This module closes the gap between an arbitrary certified flip-symmetric
trajectory and a concrete CNF family indexed by a natural number.

For `n`, the formula contains `n` symmetric two-clause blocks over the
decision variables `0, ..., n-1` and uses `n` itself as a common anchor.
The announced strategy decides variables in descending order.  Because the
current residual is the weak branch residual, each true decision retains the
negative sibling clause.  Those retained clauses form an explicit prefix.

The constructor below tracks that prefix, proves each next variable fresh,
proves each current residual flip-symmetric, and builds a
`FlipSymmetricTrajectory` of length exactly `n`.
-/

namespace ConstitutiveSearch
namespace SAT

namespace Cnf

/-- Avoidance is preserved by CNF append. -/
theorem avoidsVar_append
    {var : Var}
    {left right : Cnf}
    (leftAvoids : AvoidsVar var left)
    (rightAvoids : AvoidsVar var right) :
    AvoidsVar var (left ++ right) := by
  induction left with
  | nil =>
      exact rightAvoids
  | cons clause rest inductionHypothesis =>
      rcases leftAvoids with
        ⟨clauseAvoids, restAvoids⟩
      exact
        ⟨clauseAvoids,
          inductionHypothesis restAvoids⟩

/-- Weak branch residual distributes over CNF append. -/
theorem branchResidual_append
    (left right : Cnf)
    (var : Var)
    (value : Bool) :
    branchResidual (left ++ right) var value =
      branchResidual left var value ++
        branchResidual right var value := by
  induction left with
  | nil =>
      rfl
  | cons clause rest inductionHypothesis =>
      cases hit :
          Clause.containsLiteral
            (Literal.forValue var value)
            clause with
      | false =>
          rw [
            branchResidual_cons_miss
              clause
              (rest ++ right)
              var
              value
              hit,
            branchResidual_cons_miss
              clause
              rest
              var
              value
              hit,
            inductionHypothesis
          ]
      | true =>
          rw [
            branchResidual_cons_hit
              clause
              (rest ++ right)
              var
              value
              hit,
            branchResidual_cons_hit
              clause
              rest
              var
              value
              hit,
            inductionHypothesis
          ]

/-- Polarity flip distributes over CNF append. -/
theorem flipAt_append
    (var : Var)
    (left right : Cnf) :
    flipAt var (left ++ right) =
      flipAt var left ++ flipAt var right := by
  induction left with
  | nil =>
      rfl
  | cons clause rest inductionHypothesis =>
      dsimp [flipAt]
      rw [inductionHypothesis]

end Cnf

namespace FlipSymmetricAt

/--
A prefix that avoids the selected variable can be placed in front of a
flip-symmetric body without destroying the symmetry.
-/
theorem prepend_avoiding
    {prefix body : Cnf}
    {var : Var}
    (prefixAvoids : Cnf.AvoidsVar var prefix)
    (bodySymmetric : FlipSymmetricAt body var) :
    FlipSymmetricAt (prefix ++ body) var := by
  unfold FlipSymmetricAt at bodySymmetric ⊢
  rw [
    Cnf.branchResidual_append,
    Cnf.branchResidual_append,
    Cnf.branchResidual_eq_self
      prefixAvoids
      true,
    Cnf.branchResidual_eq_self
      prefixAvoids
      false,
    Cnf.flipAt_append,
    Cnf.flipAt_eq_self prefixAvoids,
    bodySymmetric
  ]

end FlipSymmetricAt

/-- Exact true residual of one symmetric block over an avoiding background. -/
theorem symmetricBlockFamily_trueResidual
    {var anchor : Var}
    {background : Cnf}
    (anchorDifferent : anchor ≠ var)
    (backgroundAvoids : Cnf.AvoidsVar var background) :
    branchResidual
        (symmetricBlockFamily var anchor background)
        var
        true =
      symmetricNegativeClause var anchor ::
        background := by
  have positiveHit :
      Clause.containsLiteral
        (Literal.forValue var true)
        (symmetricPositiveClause var anchor) =
          true := by
    unfold symmetricPositiveClause
    dsimp [Literal.forValue]
    rw [Clause.containsLiteral, if_pos rfl]
  have negativeMiss :
      Clause.containsLiteral
        (Literal.forValue var true)
        (symmetricNegativeClause var anchor) =
          false := by
    unfold symmetricNegativeClause
    dsimp [Literal.forValue]
    have firstDifferent :
        Literal.negative var ≠ Literal.positive var := by
      intro impossible
      cases impossible
    have secondDifferent :
        Literal.positive anchor ≠
          Literal.positive var := by
      intro impossible
      exact
        anchorDifferent
          (Literal.positive.inj impossible)
    rw [Clause.containsLiteral, if_neg firstDifferent]
    rw [Clause.containsLiteral, if_neg secondDifferent]
    rfl
  unfold symmetricBlockFamily
  rw [
    branchResidual_cons_hit
      (symmetricPositiveClause var anchor)
      (symmetricNegativeClause var anchor ::
        background)
      var
      true
      positiveHit,
    branchResidual_cons_miss
      (symmetricNegativeClause var anchor)
      background
      var
      true
      negativeMiss,
    Cnf.branchResidual_eq_self
      backgroundAvoids
      true
  ]

/--
Stack `count` symmetric blocks.  Block variables are
`count-1, ..., 0`; `anchor` is shared by every block.
-/
def stackedSymmetricBlocks :
    Nat → Var → Cnf
  | 0, _anchor =>
      []
  | count + 1, anchor =>
      symmetricBlockFamily
        count
        anchor
        (stackedSymmetricBlocks count anchor)

/-- Closed family: the common anchor is exactly the block count. -/
def explicitStackedSymmetricFamily
    (count : Nat) : Cnf :=
  stackedSymmetricBlocks count count

/-- The explicit family has exactly two clauses per level. -/
theorem stackedSymmetricBlocks_length
    (count : Nat)
    (anchor : Var) :
    (stackedSymmetricBlocks count anchor).length =
      2 * count := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      dsimp [
        stackedSymmetricBlocks,
        symmetricBlockFamily
      ]
      rw [inductionHypothesis]
      rw [Nat.mul_succ]
      exact Nat.add_comm 2 (2 * count)

/--
All variables in a stack of size `count` avoid every query at least
`count`, provided the common anchor is not that query.
-/
theorem stackedSymmetricBlocks_avoids_of_le
    {count query anchor : Nat}
    (countLeQuery : count ≤ query)
    (queryDifferentAnchor : query ≠ anchor) :
    Cnf.AvoidsVar
      query
      (stackedSymmetricBlocks count anchor) := by
  induction count with
  | zero =>
      exact True.intro
  | succ count inductionHypothesis =>
      have countLtQuery : count < query :=
        Nat.lt_of_lt_of_le
          (Nat.lt_succ_self count)
          countLeQuery
      have countDifferentQuery : count ≠ query :=
        Nat.ne_of_lt countLtQuery
      have anchorDifferentQuery : anchor ≠ query :=
        queryDifferentAnchor.symm
      have tailAvoids :
          Cnf.AvoidsVar
            query
            (stackedSymmetricBlocks count anchor) :=
        inductionHypothesis
          (Nat.le_trans
            (Nat.le_succ count)
            countLeQuery)
      change
        Clause.AvoidsVar
            query
            (symmetricPositiveClause count anchor) ∧
          Clause.AvoidsVar
            query
            (symmetricNegativeClause count anchor) ∧
          Cnf.AvoidsVar
            query
            (stackedSymmetricBlocks count anchor)
      constructor
      · exact
          ⟨countDifferentQuery,
            ⟨anchorDifferentQuery, True.intro⟩⟩
      · exact
          ⟨⟨countDifferentQuery,
              ⟨anchorDifferentQuery, True.intro⟩⟩,
            tailAvoids⟩

/--
A prefix is safe for the remaining `count` levels when it avoids every
decision variable strictly below `count`.
-/
def PrefixAvoidsBelow
    (count : Nat)
    (prefix : Cnf) : Prop :=
  ∀ query : Var,
    query < count →
      Cnf.AvoidsVar query prefix

/--
A decision history is safe for the remaining `count` levels when all those
future decision variables are fresh.
-/
def DecisionsAvoidBelow
    (count : Nat)
    (decisions : List StructuralBranchDecision) : Prop :=
  ∀ query : Var,
    query < count →
      StructuralDecisionsAvoid query decisions

namespace PrefixAvoidsBelow

theorem nil
    (count : Nat) :
    PrefixAvoidsBelow count [] := by
  intro _query _queryLt
  exact True.intro

/--
After deciding `count`, append its retained negative clause.  The resulting
prefix is safe for every smaller future variable.
-/
theorem append_negative
    {count anchor : Nat}
    {prefix : Cnf}
    (safe :
      PrefixAvoidsBelow (count + 1) prefix)
    (countLtAnchor : count < anchor) :
    PrefixAvoidsBelow
      count
      (prefix ++
        [symmetricNegativeClause count anchor]) := by
  intro query queryLtCount
  have queryLtSucc :
      query < count + 1 :=
    Nat.lt_trans
      queryLtCount
      (Nat.lt_succ_self count)
  have prefixAvoids :=
    safe query queryLtSucc
  have countDifferentQuery : count ≠ query :=
    (Nat.ne_of_lt queryLtCount).symm
  have queryLtAnchor :
      query < anchor :=
    Nat.lt_trans queryLtCount countLtAnchor
  have anchorDifferentQuery : anchor ≠ query :=
    (Nat.ne_of_lt queryLtAnchor).symm
  have clauseAvoids :
      Clause.AvoidsVar
        query
        (symmetricNegativeClause count anchor) := by
    exact
      ⟨countDifferentQuery,
        ⟨anchorDifferentQuery, True.intro⟩⟩
  exact
    Cnf.avoidsVar_append
      prefixAvoids
      ⟨clauseAvoids, True.intro⟩

end PrefixAvoidsBelow

namespace DecisionsAvoidBelow

theorem nil
    (count : Nat) :
    DecisionsAvoidBelow count [] := by
  intro _query _queryLt
  exact True.intro

/--
After deciding `count`, the extended history remains fresh for all smaller
future decision variables.
-/
theorem cons_current
    {count : Nat}
    {decisions : List StructuralBranchDecision}
    (safe :
      DecisionsAvoidBelow
        (count + 1)
        decisions) :
    DecisionsAvoidBelow
      count
      ({ var := count, value := true } ::
        decisions) := by
  intro query queryLtCount
  constructor
  · exact
      (Nat.ne_of_lt queryLtCount).symm
  · exact
      safe
        query
        (Nat.lt_trans
          queryLtCount
          (Nat.lt_succ_self count))

end DecisionsAvoidBelow

/-- Result of constructing an explicit stacked trajectory from one state. -/
structure StackedTrajectoryResult
    {rootFormula : Cnf}
    (start : GeneratedStructuralBranchContext rootFormula)
    (length : Nat) where
  finish : GeneratedStructuralBranchContext rootFormula
  trajectory :
    FlipSymmetricTrajectory start finish length

/--
Construct the complete flip-symmetric path through an explicit stack.

The current formula is tracked as `prefix ++ stackedSymmetricBlocks count
anchor`.  The weak residual retains one negative clause after every true
decision, and that clause is appended to `prefix`.
-/
def buildStackedTrajectory
    {rootFormula : Cnf}
    (anchor : Var) :
    (count : Nat) →
      (state : GeneratedStructuralBranchContext rootFormula) →
      (prefix : Cnf) →
      state.context.formula =
        prefix ++ stackedSymmetricBlocks count anchor →
      PrefixAvoidsBelow count prefix →
      DecisionsAvoidBelow count state.context.decisions →
      count ≤ anchor →
      StackedTrajectoryResult state count
  | 0, state, _prefix, _formulaExact, _prefixSafe,
      _decisionsSafe, _countLeAnchor =>
      { finish := state
        trajectory := .done state }
  | count + 1, state, prefix, formulaExact, prefixSafe,
      decisionsSafe, countSuccLeAnchor =>
      let currentVar : Var := count
      have currentLtAnchor : currentVar < anchor :=
        Nat.lt_of_lt_of_le
          (Nat.lt_succ_self count)
          countSuccLeAnchor
      have anchorDifferentCurrent :
          anchor ≠ currentVar :=
        (Nat.ne_of_lt currentLtAnchor).symm
      have fresh :
          StructuralDecisionsAvoid
            currentVar
            state.context.decisions :=
        decisionsSafe
          currentVar
          (Nat.lt_succ_self count)
      have tailAvoidsCurrent :
          Cnf.AvoidsVar
            currentVar
            (stackedSymmetricBlocks count anchor) :=
        stackedSymmetricBlocks_avoids_of_le
          (Nat.le_refl currentVar)
          (Nat.ne_of_lt currentLtAnchor)
      have blockSymmetric :
          FlipSymmetricAt
            (symmetricBlockFamily
              currentVar
              anchor
              (stackedSymmetricBlocks count anchor))
            currentVar :=
        symmetricBlockFamily_flipSymmetric
          anchorDifferentCurrent
          tailAvoidsCurrent
      have prefixAvoidsCurrent :
          Cnf.AvoidsVar currentVar prefix :=
        prefixSafe
          currentVar
          (Nat.lt_succ_self count)
      have explicitSymmetric :
          FlipSymmetricAt
            (prefix ++
              stackedSymmetricBlocks (count + 1) anchor)
            currentVar := by
        change
          FlipSymmetricAt
            (prefix ++
              symmetricBlockFamily
                currentVar
                anchor
                (stackedSymmetricBlocks count anchor))
            currentVar
        exact
          FlipSymmetricAt.prepend_avoiding
            prefixAvoidsCurrent
            blockSymmetric
      have stateSymmetric :
          FlipSymmetricAt
            state.context.formula
            currentVar := by
        rw [formulaExact]
        exact explicitSymmetric
      let child :=
        GeneratedStructuralBranchContext.child
          state
          currentVar
          true
          fresh
      let nextPrefix : Cnf :=
        prefix ++
          [symmetricNegativeClause currentVar anchor]
      have childFormulaExact :
          child.context.formula =
            nextPrefix ++
              stackedSymmetricBlocks count anchor := by
        change
          branchResidual
              state.context.formula
              currentVar
              true =
            nextPrefix ++
              stackedSymmetricBlocks count anchor
        rw [formulaExact]
        rw [Cnf.branchResidual_append]
        rw [
          Cnf.branchResidual_eq_self
            prefixAvoidsCurrent
            true
        ]
        change
          prefix ++
              branchResidual
                (symmetricBlockFamily
                  currentVar
                  anchor
                  (stackedSymmetricBlocks count anchor))
                currentVar
                true =
            nextPrefix ++
              stackedSymmetricBlocks count anchor
        rw [
          symmetricBlockFamily_trueResidual
            anchorDifferentCurrent
            tailAvoidsCurrent
        ]
        unfold nextPrefix
        rw [List.append_assoc]
        rfl
      have nextPrefixSafe :
          PrefixAvoidsBelow count nextPrefix := by
        unfold nextPrefix
        exact
          PrefixAvoidsBelow.append_negative
            prefixSafe
            currentLtAnchor
      have nextDecisionsSafe :
          DecisionsAvoidBelow
            count
            child.context.decisions := by
        change
          DecisionsAvoidBelow
            count
            ({ var := currentVar, value := true } ::
              state.context.decisions)
        exact
          DecisionsAvoidBelow.cons_current
            decisionsSafe
      have countLeAnchor : count ≤ anchor :=
        Nat.le_trans
          (Nat.le_succ count)
          countSuccLeAnchor
      let tail :=
        buildStackedTrajectory
          anchor
          count
          child
          nextPrefix
          childFormulaExact
          nextPrefixSafe
          nextDecisionsSafe
          countLeAnchor
      { finish := tail.finish
        trajectory :=
          .step
            currentVar
            fresh
            stateSymmetric
            tail.trajectory }

/-- Canonical root of the closed family. -/
abbrev explicitStackedRoot
    (count : Nat) :
    GeneratedStructuralBranchContext
      (explicitStackedSymmetricFamily count) :=
  GeneratedStructuralBranchContext.root
    (explicitStackedSymmetricFamily count)

/-- Construct the trajectory directly from the closed CNF `F(count)`. -/
def explicitStackedTrajectory
    (count : Nat) :
    StackedTrajectoryResult
      (explicitStackedRoot count)
      count :=
  buildStackedTrajectory
    count
    count
    (explicitStackedRoot count)
    []
    rfl
    (PrefixAvoidsBelow.nil count)
    (DecisionsAvoidBelow.nil count)
    (Nat.le_refl count)

/-- The explicit closed family has a trajectory of exactly the requested length. -/
theorem explicitStackedTrajectory_length
    (count : Nat) :
    (explicitStackedTrajectory count).trajectory.widthTrace.length =
      2 * count + 1 := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      change
        (1 :: 2 ::
          (explicitStackedTrajectory count).trajectory.widthTrace).length =
            2 * (count + 1) + 1
      rw [inductionHypothesis]
      simp only [List.length_cons]
      rw [Nat.mul_succ]
      omega

/-- Uniform width bound for the concrete CNF family `F(n)`. -/
theorem explicitStackedTrajectory_width_le_two
    (count : Nat)
    (width : Nat)
    (member :
      width ∈
        (explicitStackedTrajectory count).trajectory.widthTrace) :
    width ≤ 2 :=
  (explicitStackedTrajectory count).trajectory.width_le_two
    width
    member

/-- End-to-end viability is preserved for the concrete family. -/
theorem explicitStackedTrajectory_viable_iff
    (count : Nat) :
    FrontierViable
        (generatedStructuralBranchSystem
          (explicitStackedSymmetricFamily count))
        [explicitStackedRoot count] ↔
      FrontierViable
        (generatedStructuralBranchSystem
          (explicitStackedSymmetricFamily count))
        [(explicitStackedTrajectory count).finish] :=
  (explicitStackedTrajectory count).trajectory.viable_iff

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.Cnf.avoidsVar_append
#print axioms ConstitutiveSearch.SAT.Cnf.branchResidual_append
#print axioms ConstitutiveSearch.SAT.Cnf.flipAt_append
#print axioms ConstitutiveSearch.SAT.FlipSymmetricAt.prepend_avoiding
#print axioms ConstitutiveSearch.SAT.symmetricBlockFamily_trueResidual
#print axioms ConstitutiveSearch.SAT.stackedSymmetricBlocks
#print axioms ConstitutiveSearch.SAT.explicitStackedSymmetricFamily
#print axioms ConstitutiveSearch.SAT.stackedSymmetricBlocks_length
#print axioms ConstitutiveSearch.SAT.stackedSymmetricBlocks_avoids_of_le
#print axioms ConstitutiveSearch.SAT.PrefixAvoidsBelow
#print axioms ConstitutiveSearch.SAT.DecisionsAvoidBelow
#print axioms ConstitutiveSearch.SAT.StackedTrajectoryResult
#print axioms ConstitutiveSearch.SAT.buildStackedTrajectory
#print axioms ConstitutiveSearch.SAT.explicitStackedTrajectory
#print axioms ConstitutiveSearch.SAT.explicitStackedTrajectory_length
#print axioms ConstitutiveSearch.SAT.explicitStackedTrajectory_width_le_two
#print axioms ConstitutiveSearch.SAT.explicitStackedTrajectory_viable_iff
/- AXIOM_AUDIT_END -/
