import ConstitutiveSearch.ConstitutiveProjectionNonFactorization
import ConstitutiveSearch.ConstructivePrelude
import ConstitutiveSearch.SAT.GrowingDiscoveryBenchmark

/-!
# Operational inadequacy of the provenance-erasing projection

This module integrates the objects that were separate after the second audit.
For every input index it constructs two generated computations over the exact
same root CNF.  Their public, input-aware extensional snapshots coincide, but
one and the same executable continuation succeeds on one computation and fails
on the other because their constituted histories differ.

The hidden mismatch is placed after an input-sized common history prefix.  It
is therefore not a relabelling spectator: both constituted depth and the work
performed by the recursive history comparison grow with the input.

The successful continuation does not manufacture its target state.  It finds a
transport code and evaluates that code on an actual source continuation.  The
observable terminal bit is read from the continuation returned by this
evaluation.

The conclusion is deliberately exact.  It proves failure of factorization and
failure of contextual adequacy for an input-aware extensional projection.  It
does not assert either equality or inequality of classical complexity classes.
The counters below are exact for the explicitly instrumented extraction,
transformation, comparison, code, and readout phases.  They are not a machine
time model, a lower bound, or a claim that every Lean evaluator reduction has
been charged.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Reassociate one successor without arithmetic automation. -/
theorem add_one_left_of_tail
    (first tail : Nat) :
    (first + 1) + tail = first + (tail + 1) := by
  calc
    (first + 1) + tail = first + (1 + tail) :=
      Nat.add_assoc first 1 tail
    _ = first + (tail + 1) :=
      congrArg (Nat.add first) (Nat.add_comm 1 tail)

/-- The two smaller offsets used below are strictly below offset four. -/
theorem add_two_lt_add_four (value : Nat) :
    value + 2 < value + 4 :=
  Nat.add_lt_add_left (by decide : 2 < 4) value

theorem add_three_lt_add_four (value : Nat) :
    value + 3 < value + 4 :=
  Nat.add_lt_add_left (by decide : 3 < 4) value

theorem take_append_head
    {alpha : Type}
    (initial : List alpha)
    (head : alpha)
    (tail : List alpha) :
    (initial ++ head :: tail).take (initial.length + 1) =
      initial ++ [head] := by
  induction initial with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      change
        first ::
            (rest ++ head :: tail).take (rest.length + 1) =
          first :: (rest ++ [head])
      exact congrArg (List.cons first) inductionHypothesis

/-! ## Generated paths with explicit provenance -/

/-- A decision history assigning `false` to every listed variable. -/
def falseDecisionHistory : List Var -> List StructuralBranchDecision
  | [] => []
  | var :: rest =>
      { var := var, value := false } :: falseDecisionHistory rest

theorem falseDecisionHistory_length :
    forall variables : List Var,
      (falseDecisionHistory variables).length = variables.length
  | [] => rfl
  | _variable :: rest => by
      change (falseDecisionHistory rest).length + 1 = rest.length + 1
      rw [falseDecisionHistory_length]

/-- Constructive, recursion-shaped distinctness used by the path generator. -/
def PathVariablesDistinct : List Var -> Prop
  | [] => True
  | candidate :: rest =>
      candidate ∉ rest ∧ PathVariablesDistinct rest

/-- Absence from a variable list gives freshness for its false decision history. -/
theorem structuralDecisionsAvoid_falseDecisionHistory
    (selected : Var) :
    forall variables : List Var,
      selected ∉ variables ->
        StructuralDecisionsAvoid
          selected
          (falseDecisionHistory variables)
  | [], _notMember =>
      True.intro
  | var :: rest, notMember => by
      constructor
      · intro same
        apply notMember
        cases same
        exact List.Mem.head rest
      · apply
          structuralDecisionsAvoid_falseDecisionHistory
            selected
            rest
        intro member
        exact notMember (List.Mem.tail var member)

/--
Result of actually generating a path from a list of fresh, pairwise-distinct
variables.  The retained equations expose the data produced by the recursion.
-/
structure GeneratedFalsePath
    (rootFormula : Cnf)
    (variables : List Var) where
  state : GeneratedStructuralBranchContext rootFormula
  decisionsExact :
    state.context.decisions = falseDecisionHistory variables
  formulaExact : state.context.formula = rootFormula
  depthExact : state.depth = variables.length

/--
Generate the path by structural recursion.  Every child is built from the
state returned by the preceding recursive call; no terminal state is supplied.
-/
def generateFalsePath
    (rootFormula : Cnf) :
    (variables : List Var) ->
      PathVariablesDistinct variables ->
      (forall candidate,
        candidate ∈ variables ->
          Cnf.AvoidsVar candidate rootFormula) ->
      GeneratedFalsePath rootFormula variables
  | [], _distinct, _avoids =>
      { state := GeneratedStructuralBranchContext.root rootFormula
        decisionsExact := rfl
        formulaExact := rfl
        depthExact := rfl }
  | candidate :: rest, distinct, avoids => by
      have headNotMember : candidate ∉ rest := distinct.1
      have tailDistinct : PathVariablesDistinct rest := distinct.2
      have tailAvoids :
          forall tailVariable,
            tailVariable ∈ rest ->
              Cnf.AvoidsVar tailVariable rootFormula := by
        intro tailVariable member
        exact avoids tailVariable (List.Mem.tail candidate member)
      let tail :=
        generateFalsePath
          rootFormula
          rest
          tailDistinct
          tailAvoids
      have fresh :
            StructuralDecisionsAvoid
            candidate
            tail.state.context.decisions := by
        rw [tail.decisionsExact]
        exact
          structuralDecisionsAvoid_falseDecisionHistory
            candidate
            rest
            headNotMember
      let produced :=
        GeneratedStructuralBranchContext.child
          tail.state
          candidate
          false
          fresh
      refine
        { state := produced
          decisionsExact := ?_
          formulaExact := ?_
          depthExact := ?_ }
      · change
          { var := candidate, value := false } ::
              tail.state.context.decisions =
            { var := candidate, value := false } ::
              falseDecisionHistory rest
        rw [tail.decisionsExact]
      · change
          branchResidual
              tail.state.context.formula
              candidate
              false =
            rootFormula
        rw [tail.formulaExact]
        exact
          Cnf.branchResidual_eq_self
            (avoids candidate (List.Mem.head rest))
            false
      · change tail.state.depth + 1 = rest.length + 1
        rw [tail.depthExact]

/-! ## One growing, same-input family -/

/--
`count` consecutive variables followed by one oldest marker.  The recursion is
also used to prove freshness without importing extensional list lemmas.
-/
def pathVariablesFrom : Nat -> Nat -> Var -> List Var
  | _start, 0, marker => [marker]
  | start, count + 1, marker =>
      start :: pathVariablesFrom (start + 1) count marker

theorem pathVariablesFrom_length
    (start count marker : Nat) :
    (pathVariablesFrom start count marker).length = count + 1 := by
  induction count generalizing start with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        (pathVariablesFrom (start + 1) count marker).length + 1 =
          (count + 1) + 1
      rw [inductionHypothesis]

theorem pathVariablesFrom_member_lower
    (start count marker candidate : Nat)
    (member : candidate ∈ pathVariablesFrom start count marker)
    (markerAbove : start + count <= marker) :
    start <= candidate := by
  induction count generalizing start with
  | zero =>
      change candidate ∈ [marker] at member
      cases member with
      | head => exact markerAbove
      | tail _ impossible => cases impossible
  | succ count inductionHypothesis =>
      change candidate ∈ start :: pathVariablesFrom (start + 1) count marker at member
      cases member with
      | head => exact Nat.le_refl _
      | tail _ tailMember =>
          exact
            Nat.le_trans
              (Nat.le_succ start)
              (inductionHypothesis
                (start + 1)
                tailMember
                (by
                  rw [add_one_left_of_tail]
                  exact markerAbove))

theorem pathVariablesFrom_distinct
    (start count marker : Nat)
    (markerAbove : start + count <= marker) :
    PathVariablesDistinct (pathVariablesFrom start count marker) := by
  induction count generalizing start with
  | zero =>
      constructor
      · intro impossible
        cases impossible
      · exact True.intro
  | succ count inductionHypothesis =>
      constructor
      · intro member
        have lower : start + 1 <= start :=
          pathVariablesFrom_member_lower
            (start + 1)
            count
            marker
            start
            member
            (by
              rw [add_one_left_of_tail]
              exact markerAbove)
        exact False.elim ((Nat.not_succ_le_self start) lower)
      · exact
          inductionHypothesis
            (start + 1)
            (by
              rw [add_one_left_of_tail]
              exact markerAbove)

/-- Oldest marker of the reconstructible/source organization. -/
def operationalSourceMarker (input : Nat) : Var :=
  (input + 4) + input

/-- Distinct oldest marker of the provenance-mismatched organization. -/
def operationalTargetMarker (input : Nat) : Var :=
  operationalSourceMarker input + 1

/-- Variables used to generate the common source parent. -/
def operationalSourcePathVariables (input : Nat) : List Var :=
  pathVariablesFrom
    (input + 4)
    input
    (operationalSourceMarker input)

/--
The target organization agrees through the complete input-sized prefix and
differs only at the oldest retained marker.
-/
def operationalMismatchedPathVariables (input : Nat) : List Var :=
  pathVariablesFrom
    (input + 4)
    input
    (operationalTargetMarker input)

theorem operationalSourcePathVariables_nodup
    (input : Nat) :
    PathVariablesDistinct (operationalSourcePathVariables input) := by
  unfold operationalSourcePathVariables operationalSourceMarker
  exact pathVariablesFrom_distinct _ _ _ (Nat.le_refl _)

theorem operationalMismatchedPathVariables_nodup
    (input : Nat) :
    PathVariablesDistinct (operationalMismatchedPathVariables input) := by
  unfold
    operationalMismatchedPathVariables
    operationalTargetMarker
    operationalSourceMarker
  exact
    pathVariablesFrom_distinct
      _
      _
      _
      (Nat.le_succ ((input + 4) + input))

/-- Every padding variable is above all variables occurring in the input CNF. -/
theorem distinctGrowingDiscoveryFormula_avoids_above
    (input candidate : Nat)
    (above : input + 4 <= candidate) :
    Cnf.AvoidsVar
      candidate
      (distinctGrowingDiscoveryFormula input) := by
  unfold distinctGrowingDiscoveryFormula
  refine ⟨?_, ?_, ?_, True.intro⟩
  · exact
      distinctDecoyClause_avoids_above
        (input + 1)
        candidate
        (Nat.le_trans
          (Nat.add_le_add_left (by decide : 1 <= 4) input)
          above)
  · have splitLt : growingDiscoverySplitVar input < candidate := by
      unfold growingDiscoverySplitVar
      exact Nat.lt_of_lt_of_le (add_two_lt_add_four input) above
    have anchorLt : growingDiscoveryAnchorVar input < candidate := by
      unfold growingDiscoveryAnchorVar
      exact Nat.lt_of_lt_of_le (add_three_lt_add_four input) above
    exact ⟨Nat.ne_of_lt splitLt, Nat.ne_of_lt anchorLt, True.intro⟩
  · have splitLt : growingDiscoverySplitVar input < candidate := by
      unfold growingDiscoverySplitVar
      exact Nat.lt_of_lt_of_le (add_two_lt_add_four input) above
    have anchorLt : growingDiscoveryAnchorVar input < candidate := by
      unfold growingDiscoveryAnchorVar
      exact Nat.lt_of_lt_of_le (add_three_lt_add_four input) above
    exact ⟨Nat.ne_of_lt splitLt, Nat.ne_of_lt anchorLt, True.intro⟩

theorem operationalSourcePathVariables_avoid_formula
    (input : Nat) :
    forall candidate,
      candidate ∈ operationalSourcePathVariables input ->
        Cnf.AvoidsVar
          candidate
          (distinctGrowingDiscoveryFormula input) := by
  intro candidate member
  apply distinctGrowingDiscoveryFormula_avoids_above
  exact
    pathVariablesFrom_member_lower
      (input + 4)
      input
      (operationalSourceMarker input)
      candidate
      member
      (by
        unfold operationalSourceMarker
        exact Nat.le_refl _)

theorem operationalMismatchedPathVariables_avoid_formula
    (input : Nat) :
    forall candidate,
      candidate ∈ operationalMismatchedPathVariables input ->
        Cnf.AvoidsVar
          candidate
          (distinctGrowingDiscoveryFormula input) := by
  intro candidate member
  apply distinctGrowingDiscoveryFormula_avoids_above
  exact
    pathVariablesFrom_member_lower
      (input + 4)
      input
      (operationalTargetMarker input)
      candidate
      member
      (by
        unfold operationalTargetMarker operationalSourceMarker
        exact Nat.le_succ ((input + 4) + input))

/-- Common parent constructed by the recursive path generator. -/
def operationalCommonParentPath
    (input : Nat) :
    GeneratedFalsePath
      (distinctGrowingDiscoveryFormula input)
      (operationalSourcePathVariables input) :=
  generateFalsePath
    (distinctGrowingDiscoveryFormula input)
    (operationalSourcePathVariables input)
    (operationalSourcePathVariables_nodup input)
    (operationalSourcePathVariables_avoid_formula input)

/-- Alternative parent with the mismatch after the complete common prefix. -/
def operationalMismatchedParentPath
    (input : Nat) :
    GeneratedFalsePath
      (distinctGrowingDiscoveryFormula input)
      (operationalMismatchedPathVariables input) :=
  generateFalsePath
    (distinctGrowingDiscoveryFormula input)
    (operationalMismatchedPathVariables input)
    (operationalMismatchedPathVariables_nodup input)
    (operationalMismatchedPathVariables_avoid_formula input)

/-- The useful variable found by endogenous discovery is fresh at both parents. -/
theorem operationalEngineFreshCommon
    (input : Nat) :
    StructuralDecisionsAvoid
      (growingDiscoverySplitVar input)
      (operationalCommonParentPath input).state.context.decisions := by
  rw [(operationalCommonParentPath input).decisionsExact]
  apply structuralDecisionsAvoid_falseDecisionHistory
  intro member
  have lower : input + 4 <= growingDiscoverySplitVar input :=
    pathVariablesFrom_member_lower
      (input + 4)
      input
      (operationalSourceMarker input)
      (growingDiscoverySplitVar input)
      member
      (by
        unfold operationalSourceMarker
        exact Nat.le_refl _)
  unfold growingDiscoverySplitVar at lower
  exact False.elim ((Nat.not_le_of_gt (add_two_lt_add_four input)) lower)

theorem operationalEngineFreshMismatched
    (input : Nat) :
    StructuralDecisionsAvoid
      (growingDiscoverySplitVar input)
      (operationalMismatchedParentPath input).state.context.decisions := by
  rw [(operationalMismatchedParentPath input).decisionsExact]
  apply structuralDecisionsAvoid_falseDecisionHistory
  intro member
  have lower : input + 4 <= growingDiscoverySplitVar input :=
    pathVariablesFrom_member_lower
      (input + 4)
      input
      (operationalTargetMarker input)
      (growingDiscoverySplitVar input)
      member
      (by
        unfold operationalTargetMarker operationalSourceMarker
        exact Nat.le_succ ((input + 4) + input))
  unfold growingDiscoverySplitVar at lower
  exact False.elim ((Nat.not_le_of_gt (add_two_lt_add_four input)) lower)

/-- Shared source state of both organizations. -/
def operationalSource
    (input : Nat) :
    GeneratedStructuralBranchContext
      (distinctGrowingDiscoveryFormula input) :=
  GeneratedStructuralBranchContext.child
    (operationalCommonParentPath input).state
    (growingDiscoverySplitVar input)
    false
    (operationalEngineFreshCommon input)

/-- Reconstructible target produced from the same parent as the source. -/
def operationalPositiveTarget
    (input : Nat) :
    GeneratedStructuralBranchContext
      (distinctGrowingDiscoveryFormula input) :=
  GeneratedStructuralBranchContext.child
    (operationalCommonParentPath input).state
    (growingDiscoverySplitVar input)
    true
    (operationalEngineFreshCommon input)

/-- Target with the same residual syntax but a deeply mismatched provenance. -/
def operationalNegativeTarget
    (input : Nat) :
    GeneratedStructuralBranchContext
      (distinctGrowingDiscoveryFormula input) :=
  GeneratedStructuralBranchContext.child
    (operationalMismatchedParentPath input).state
    (growingDiscoverySplitVar input)
    true
    (operationalEngineFreshMismatched input)

/-- Both generated organizations have genuinely growing constituted depth. -/
theorem operationalSource_depth
    (input : Nat) :
    (operationalSource input).depth = input + 2 := by
  change
    (operationalCommonParentPath input).state.depth + 1 = input + 2
  rw [(operationalCommonParentPath input).depthExact]
  unfold operationalSourcePathVariables
  rw [pathVariablesFrom_length]

theorem operationalPositiveTarget_depth
    (input : Nat) :
    (operationalPositiveTarget input).depth = input + 2 := by
  change
    (operationalCommonParentPath input).state.depth + 1 = input + 2
  rw [(operationalCommonParentPath input).depthExact]
  unfold operationalSourcePathVariables
  rw [pathVariablesFrom_length]

theorem operationalNegativeTarget_depth
    (input : Nat) :
    (operationalNegativeTarget input).depth = input + 2 := by
  change
    (operationalMismatchedParentPath input).state.depth + 1 = input + 2
  rw [(operationalMismatchedParentPath input).depthExact]
  unfold operationalMismatchedPathVariables
  rw [pathVariablesFrom_length]

/-! ## Exact positive and negative relation behavior -/

theorem pathVariablesFrom_marker_ne
    (start count firstMarker secondMarker : Nat)
    (different : firstMarker ≠ secondMarker) :
    pathVariablesFrom start count firstMarker ≠
      pathVariablesFrom start count secondMarker := by
  induction count generalizing start with
  | zero =>
      intro same
      exact different (List.cons.inj same).1
  | succ count inductionHypothesis =>
      intro same
      exact
        inductionHypothesis
          (start + 1)
          (List.cons.inj same).2

theorem falseDecisionHistory_injective :
    forall {first second : List Var},
      falseDecisionHistory first = falseDecisionHistory second ->
        first = second
  | [], [], _same => rfl
  | [], _ :: _, same => by cases same
  | _ :: _, [], same => by cases same
  | first :: firstRest, second :: secondRest, same => by
      have heads : first = second := by
        have decisionHeads := (List.cons.inj same).1
        exact congrArg StructuralBranchDecision.var decisionHeads
      have tails :
          falseDecisionHistory firstRest =
            falseDecisionHistory secondRest :=
        (List.cons.inj same).2
      cases heads
      exact
        congrArg
          (List.cons first)
          (falseDecisionHistory_injective tails)

theorem operationalPathVariables_ne
    (input : Nat) :
    operationalSourcePathVariables input ≠
      operationalMismatchedPathVariables input := by
  unfold
    operationalSourcePathVariables
    operationalMismatchedPathVariables
  apply pathVariablesFrom_marker_ne
  unfold operationalTargetMarker
  exact Constructive.nat_ne_add_one (operationalSourceMarker input)

theorem operationalCommonParent_flipSymmetric
    (input : Nat) :
    FlipSymmetricAt
      (operationalCommonParentPath input).state.context.formula
      (growingDiscoverySplitVar input) := by
  rw [(operationalCommonParentPath input).formulaExact]
  exact distinctGrowingDiscovery_flipSymmetric input

/-- Positive sibling relation at the variable returned by endogenous discovery. -/
def operationalPositiveRelation
    (input : Nat) :
    GeneratedStructuralFlipAtRelation
      (growingDiscoverySplitVar input)
      (operationalSource input)
      (operationalPositiveTarget input) :=
  flipSymmetricSiblingRelation
    (operationalCommonParentPath input).state
    (growingDiscoverySplitVar input)
    (operationalEngineFreshCommon input)
    (operationalCommonParent_flipSymmetric input)

theorem operationalSource_formula
    (input : Nat) :
    (operationalSource input).context.formula =
      branchResidual
        (distinctGrowingDiscoveryFormula input)
        (growingDiscoverySplitVar input)
        false := by
  change
    branchResidual
        (operationalCommonParentPath input).state.context.formula
        (growingDiscoverySplitVar input)
        false =
      branchResidual
        (distinctGrowingDiscoveryFormula input)
        (growingDiscoverySplitVar input)
        false
  rw [(operationalCommonParentPath input).formulaExact]

theorem operationalPositiveTarget_formula
    (input : Nat) :
    (operationalPositiveTarget input).context.formula =
      branchResidual
        (distinctGrowingDiscoveryFormula input)
        (growingDiscoverySplitVar input)
        true := by
  change
    branchResidual
        (operationalCommonParentPath input).state.context.formula
        (growingDiscoverySplitVar input)
        true =
      branchResidual
        (distinctGrowingDiscoveryFormula input)
        (growingDiscoverySplitVar input)
        true
  rw [(operationalCommonParentPath input).formulaExact]

theorem operationalNegativeTarget_formula
    (input : Nat) :
    (operationalNegativeTarget input).context.formula =
      branchResidual
        (distinctGrowingDiscoveryFormula input)
        (growingDiscoverySplitVar input)
        true := by
  change
    branchResidual
        (operationalMismatchedParentPath input).state.context.formula
        (growingDiscoverySplitVar input)
        true =
      branchResidual
        (distinctGrowingDiscoveryFormula input)
        (growingDiscoverySplitVar input)
        true
  rw [(operationalMismatchedParentPath input).formulaExact]

/-- Both organizations are exactly equal after input-aware residual projection. -/
theorem operationalTarget_formulas_same
    (input : Nat) :
    (operationalPositiveTarget input).context.formula =
      (operationalNegativeTarget input).context.formula := by
  rw [operationalPositiveTarget_formula, operationalNegativeTarget_formula]

/-- The negative case passes the formula half of the exact relation test. -/
theorem operationalNegative_formula_matches
    (input : Nat) :
    (operationalNegativeTarget input).context.formula =
      Cnf.flipAt
        (growingDiscoverySplitVar input)
        (operationalSource input).context.formula := by
  rw [operationalNegativeTarget_formula, operationalSource_formula]
  exact distinctGrowingDiscovery_flipSymmetric input

/-- Its rejection is caused only by the deeply retained history marker. -/
theorem operationalNegative_decisions_mismatch
    (input : Nat) :
    (operationalNegativeTarget input).context.decisions ≠
      flipStructuralDecisionsAt
        (growingDiscoverySplitVar input)
        (operationalSource input).context.decisions := by
  intro same
  change
    { var := growingDiscoverySplitVar input, value := true } ::
        (operationalMismatchedParentPath input).state.context.decisions =
      flipStructuralDecisionsAt
        (growingDiscoverySplitVar input)
        ({ var := growingDiscoverySplitVar input, value := false } ::
          (operationalCommonParentPath input).state.context.decisions) at same
  rw [
    (operationalMismatchedParentPath input).decisionsExact,
    (operationalCommonParentPath input).decisionsExact
  ] at same
  dsimp [flipStructuralDecisionsAt, StructuralBranchDecision.flipAt] at same
  rw [if_pos rfl] at same
  have sourceAvoids :
      StructuralDecisionsAvoid
        (growingDiscoverySplitVar input)
        (falseDecisionHistory (operationalSourcePathVariables input)) := by
    rw [← (operationalCommonParentPath input).decisionsExact]
    exact operationalEngineFreshCommon input
  rw [flipStructuralDecisionsAt_eq_self sourceAvoids] at same
  have historiesSame :
      falseDecisionHistory (operationalMismatchedPathVariables input) =
        falseDecisionHistory (operationalSourcePathVariables input) :=
    (List.cons.inj same).2
  have variablesSame := falseDecisionHistory_injective historiesSame
  exact (operationalPathVariables_ne input) variablesSame.symm

/-- The two organizations are constructively different before any projection. -/
theorem operationalTarget_constitutions_different
    (input : Nat) :
    (operationalPositiveTarget input).context.decisions ≠
      (operationalNegativeTarget input).context.decisions := by
  intro same
  apply operationalNegative_decisions_mismatch input
  calc
    (operationalNegativeTarget input).context.decisions =
        (operationalPositiveTarget input).context.decisions :=
      same.symm
    _ =
        flipStructuralDecisionsAt
          (growingDiscoverySplitVar input)
          (operationalSource input).context.decisions :=
      (operationalPositiveRelation input).decisionsExact

/-- The ungated engine succeeds on the generated sibling organization. -/
theorem operationalPositive_found
    (input : Nat) :
    (generatedStructuralFlipAtSearch
      (distinctGrowingDiscoveryFormula input)
      (growingDiscoverySplitVar input)).find
        (operationalSource input)
        (operationalPositiveTarget input) ≠ none := by
  dsimp [generatedStructuralFlipAtSearch]
  rw [
    dif_pos (operationalPositiveRelation input).formulaExact,
    dif_pos (operationalPositiveRelation input).decisionsExact
  ]
  intro impossible
  cases impossible

/-- The exact same engine rejects the same-input provenance mismatch. -/
theorem operationalNegative_missing
    (input : Nat) :
    (generatedStructuralFlipAtSearch
      (distinctGrowingDiscoveryFormula input)
      (growingDiscoverySplitVar input)).find
        (operationalSource input)
        (operationalNegativeTarget input) = none := by
  dsimp [generatedStructuralFlipAtSearch]
  rw [
    dif_pos (operationalNegative_formula_matches input),
    dif_neg (operationalNegative_decisions_mismatch input)
  ]

/-! ## Fully instrumented structural equality and flip runs -/

/-- Executed comparison of two unary natural labels. -/
structure NatComparisonRun where
  equal : Bool
  constructorVisits : Nat
  deriving DecidableEq, Repr

def runNatComparison : Nat -> Nat -> NatComparisonRun
  | 0, 0 => { equal := true, constructorVisits := 1 }
  | 0, _ + 1 => { equal := false, constructorVisits := 1 }
  | _ + 1, 0 => { equal := false, constructorVisits := 1 }
  | left + 1, right + 1 =>
      let tail := runNatComparison left right
      { equal := tail.equal
        constructorVisits := tail.constructorVisits + 1 }

theorem runNatComparison_true_implies_equal :
    forall left right : Nat,
      (runNatComparison left right).equal = true -> left = right
  | 0, 0, _ => rfl
  | 0, _ + 1, impossible => False.elim (Bool.noConfusion impossible)
  | _ + 1, 0, impossible => False.elim (Bool.noConfusion impossible)
  | left + 1, right + 1, equal =>
      congrArg Nat.succ
        (runNatComparison_true_implies_equal left right equal)

theorem runNatComparison_equal_implies_true :
    forall value : Nat,
      (runNatComparison value value).equal = true
  | 0 => rfl
  | value + 1 => runNatComparison_equal_implies_true value

theorem runNatComparison_false_of_ne
    (left right : Nat)
    (different : left ≠ right) :
    (runNatComparison left right).equal = false := by
  cases exactResult : (runNatComparison left right).equal with
  | false => rfl
  | true =>
      exact
        False.elim
          (different
            (runNatComparison_true_implies_equal
              left right exactResult))

/-- Instrumented result of flipping one literal. -/
structure LiteralFlipRun where
  output : Literal
  literalVisits : Nat
  variableConstructorVisits : Nat
  deriving DecidableEq

def runLiteralFlip
    (selected : Var) : Literal -> LiteralFlipRun
  | .positive label =>
      let comparison := runNatComparison label selected
      { output := Literal.flipAt selected (.positive label)
        literalVisits := 1
        variableConstructorVisits := comparison.constructorVisits }
  | .negative label =>
      let comparison := runNatComparison label selected
      { output := Literal.flipAt selected (.negative label)
        literalVisits := 1
        variableConstructorVisits := comparison.constructorVisits }

theorem runLiteralFlip_output
    (selected : Var) :
    forall literal : Literal,
      (runLiteralFlip selected literal).output =
        Literal.flipAt selected literal
  | .positive _label => rfl
  | .negative _label => rfl

theorem runLiteralFlip_literalVisits
    (selected : Var) :
    forall literal : Literal,
      (runLiteralFlip selected literal).literalVisits = 1
  | .positive label => by
      rfl
  | .negative label => by
      rfl

/-- Instrumented clause transformation. -/
structure ClauseFlipRun where
  output : Clause
  literalVisits : Nat
  variableConstructorVisits : Nat
  deriving DecidableEq

def runClauseFlip (selected : Var) : Clause -> ClauseFlipRun
  | [] =>
      { output := []
        literalVisits := 0
        variableConstructorVisits := 0 }
  | literal :: rest =>
      let head := runLiteralFlip selected literal
      let tail := runClauseFlip selected rest
      { output := head.output :: tail.output
        literalVisits := head.literalVisits + tail.literalVisits
        variableConstructorVisits :=
          head.variableConstructorVisits + tail.variableConstructorVisits }

theorem runClauseFlip_output
    (selected : Var) :
    forall clause : Clause,
      (runClauseFlip selected clause).output = Clause.flipAt selected clause
  | [] => rfl
  | literal :: rest => by
      change
        (runLiteralFlip selected literal).output ::
            (runClauseFlip selected rest).output =
          Literal.flipAt selected literal :: Clause.flipAt selected rest
      rw [runLiteralFlip_output, runClauseFlip_output]

theorem runClauseFlip_literalVisits
    (selected : Var) :
    forall clause : Clause,
      (runClauseFlip selected clause).literalVisits = clause.length
  | [] => rfl
  | literal :: rest => by
      change
        (runLiteralFlip selected literal).literalVisits +
            (runClauseFlip selected rest).literalVisits =
          rest.length + 1
      rw [
        runLiteralFlip_literalVisits,
        runClauseFlip_literalVisits
      ]
      exact Nat.add_comm 1 rest.length

/-- Instrumented CNF transformation. -/
structure CnfFlipRun where
  output : Cnf
  clauseVisits : Nat
  literalVisits : Nat
  variableConstructorVisits : Nat
  deriving DecidableEq

def runCnfFlip (selected : Var) : Cnf -> CnfFlipRun
  | [] =>
      { output := []
        clauseVisits := 0
        literalVisits := 0
        variableConstructorVisits := 0 }
  | clause :: rest =>
      let head := runClauseFlip selected clause
      let tail := runCnfFlip selected rest
      { output := head.output :: tail.output
        clauseVisits := tail.clauseVisits + 1
        literalVisits := head.literalVisits + tail.literalVisits
        variableConstructorVisits :=
          head.variableConstructorVisits + tail.variableConstructorVisits }

theorem runCnfFlip_output
    (selected : Var) :
    forall formula : Cnf,
      (runCnfFlip selected formula).output = Cnf.flipAt selected formula
  | [] => rfl
  | clause :: rest => by
      change
        (runClauseFlip selected clause).output ::
            (runCnfFlip selected rest).output =
          Clause.flipAt selected clause :: Cnf.flipAt selected rest
      rw [runClauseFlip_output, runCnfFlip_output]

/-- CNF transformation charges every visited clause. -/
theorem runCnfFlip_clauseVisits
    (selected : Var) :
    forall formula : Cnf,
      (runCnfFlip selected formula).clauseVisits = formula.length
  | [] => rfl
  | _clause :: rest => by
      change
        (runCnfFlip selected rest).clauseVisits + 1 =
          rest.length + 1
      rw [runCnfFlip_clauseVisits]

/-- CNF transformation charges every literal, not merely one query event. -/
theorem runCnfFlip_literalVisits
    (selected : Var) :
    forall formula : Cnf,
      (runCnfFlip selected formula).literalVisits = Cnf.literalCount formula
  | [] => rfl
  | clause :: rest => by
      change
        (runClauseFlip selected clause).literalVisits +
            (runCnfFlip selected rest).literalVisits =
          clause.length + Cnf.literalCount rest
      rw [runClauseFlip_literalVisits, runCnfFlip_literalVisits]

/-- Executed equality of two literals, including unary-label work. -/
structure LiteralComparisonRun where
  equal : Bool
  literalVisits : Nat
  variableConstructorVisits : Nat
  deriving DecidableEq, Repr

def runLiteralComparison : Literal -> Literal -> LiteralComparisonRun
  | .positive left, .positive right =>
      let comparison := runNatComparison left right
      { equal := comparison.equal
        literalVisits := 1
        variableConstructorVisits := comparison.constructorVisits }
  | .negative left, .negative right =>
      let comparison := runNatComparison left right
      { equal := comparison.equal
        literalVisits := 1
        variableConstructorVisits := comparison.constructorVisits }
  | .positive _, .negative _ =>
      { equal := false, literalVisits := 1, variableConstructorVisits := 0 }
  | .negative _, .positive _ =>
      { equal := false, literalVisits := 1, variableConstructorVisits := 0 }

theorem runLiteralComparison_true_implies_equal :
    forall left right : Literal,
      (runLiteralComparison left right).equal = true -> left = right
  | .positive left, .positive right, equal =>
      congrArg Literal.positive
        (runNatComparison_true_implies_equal left right equal)
  | .negative left, .negative right, equal =>
      congrArg Literal.negative
        (runNatComparison_true_implies_equal left right equal)
  | .positive _, .negative _, impossible =>
      False.elim (Bool.noConfusion impossible)
  | .negative _, .positive _, impossible =>
      False.elim (Bool.noConfusion impossible)

theorem runLiteralComparison_equal_implies_true
    (literal : Literal) :
    (runLiteralComparison literal literal).equal = true := by
  cases literal <;> exact runNatComparison_equal_implies_true _

/-- Executed equality of two clauses. -/
structure ClauseComparisonRun where
  equal : Bool
  literalVisits : Nat
  variableConstructorVisits : Nat
  deriving DecidableEq, Repr

def runClauseComparison : Clause -> Clause -> ClauseComparisonRun
  | [], [] =>
      { equal := true, literalVisits := 0, variableConstructorVisits := 0 }
  | [], _ :: _ =>
      { equal := false, literalVisits := 0, variableConstructorVisits := 0 }
  | _ :: _, [] =>
      { equal := false, literalVisits := 0, variableConstructorVisits := 0 }
  | left :: leftRest, right :: rightRest =>
      let head := runLiteralComparison left right
      match head.equal with
      | false =>
          { equal := false
            literalVisits := head.literalVisits
            variableConstructorVisits := head.variableConstructorVisits }
      | true =>
          let tail := runClauseComparison leftRest rightRest
          { equal := tail.equal
            literalVisits := head.literalVisits + tail.literalVisits
            variableConstructorVisits :=
              head.variableConstructorVisits + tail.variableConstructorVisits }

theorem runClauseComparison_true_implies_equal :
    forall left right : Clause,
      (runClauseComparison left right).equal = true -> left = right
  | [], [], _ => rfl
  | [], _ :: _, impossible => False.elim (Bool.noConfusion impossible)
  | _ :: _, [], impossible => False.elim (Bool.noConfusion impossible)
  | left :: leftRest, right :: rightRest, equal => by
      change
        (runClauseComparison (left :: leftRest) (right :: rightRest)).equal = true
          at equal
      cases headExact : (runLiteralComparison left right).equal with
      | false =>
          simp only [runClauseComparison, headExact] at equal
          cases equal
      | true =>
          simp only [runClauseComparison, headExact] at equal
          have headSame :=
            runLiteralComparison_true_implies_equal left right headExact
          have tailSame :=
            runClauseComparison_true_implies_equal leftRest rightRest equal
          cases headSame
          exact congrArg (List.cons left) tailSame

theorem runClauseComparison_equal_implies_true :
    forall clause : Clause,
      (runClauseComparison clause clause).equal = true
  | [] => rfl
  | literal :: rest => by
      simp only [runClauseComparison, runLiteralComparison_equal_implies_true]
      exact runClauseComparison_equal_implies_true rest

/-- Equal-clause comparison charges the complete clause. -/
theorem runClauseComparison_equal_literalVisits :
    forall clause : Clause,
      (runClauseComparison clause clause).literalVisits = clause.length
  | [] => rfl
  | literal :: rest => by
      simp only [
        runClauseComparison,
        runLiteralComparison_equal_implies_true
      ]
      change
        (runLiteralComparison literal literal).literalVisits +
            (runClauseComparison rest rest).literalVisits =
          rest.length + 1
      have headVisit :
          (runLiteralComparison literal literal).literalVisits = 1 := by
        cases literal <;> rfl
      rw [headVisit, runClauseComparison_equal_literalVisits]
      exact Nat.add_comm 1 rest.length

/-- Executed equality of two CNFs. -/
structure CnfComparisonRun where
  equal : Bool
  clauseVisits : Nat
  literalVisits : Nat
  variableConstructorVisits : Nat
  deriving DecidableEq, Repr

def runCnfComparison : Cnf -> Cnf -> CnfComparisonRun
  | [], [] =>
      { equal := true
        clauseVisits := 0
        literalVisits := 0
        variableConstructorVisits := 0 }
  | [], _ :: _ =>
      { equal := false
        clauseVisits := 0
        literalVisits := 0
        variableConstructorVisits := 0 }
  | _ :: _, [] =>
      { equal := false
        clauseVisits := 0
        literalVisits := 0
        variableConstructorVisits := 0 }
  | left :: leftRest, right :: rightRest =>
      let head := runClauseComparison left right
      match head.equal with
      | false =>
          { equal := false
            clauseVisits := 1
            literalVisits := head.literalVisits
            variableConstructorVisits := head.variableConstructorVisits }
      | true =>
          let tail := runCnfComparison leftRest rightRest
          { equal := tail.equal
            clauseVisits := tail.clauseVisits + 1
            literalVisits := head.literalVisits + tail.literalVisits
            variableConstructorVisits :=
              head.variableConstructorVisits + tail.variableConstructorVisits }

theorem runCnfComparison_true_implies_equal :
    forall left right : Cnf,
      (runCnfComparison left right).equal = true -> left = right
  | [], [], _ => rfl
  | [], _ :: _, impossible => False.elim (Bool.noConfusion impossible)
  | _ :: _, [], impossible => False.elim (Bool.noConfusion impossible)
  | left :: leftRest, right :: rightRest, equal => by
      change
        (runCnfComparison (left :: leftRest) (right :: rightRest)).equal = true
          at equal
      cases headExact : (runClauseComparison left right).equal with
      | false =>
          simp only [runCnfComparison, headExact] at equal
          cases equal
      | true =>
          simp only [runCnfComparison, headExact] at equal
          have headSame :=
            runClauseComparison_true_implies_equal left right headExact
          have tailSame :=
            runCnfComparison_true_implies_equal leftRest rightRest equal
          cases headSame
          exact congrArg (List.cons left) tailSame

theorem runCnfComparison_false_of_ne
    (left right : Cnf)
    (different : left ≠ right) :
    (runCnfComparison left right).equal = false := by
  cases exactResult : (runCnfComparison left right).equal with
  | false => rfl
  | true =>
      exact
        False.elim
          (different
            (runCnfComparison_true_implies_equal
              left right exactResult))

theorem runCnfComparison_equal_implies_true :
    forall formula : Cnf,
      (runCnfComparison formula formula).equal = true
  | [] => rfl
  | clause :: rest => by
      simp only [runCnfComparison, runClauseComparison_equal_implies_true]
      exact runCnfComparison_equal_implies_true rest

theorem runCnfComparison_equal_clauseVisits :
    forall formula : Cnf,
      (runCnfComparison formula formula).clauseVisits = formula.length
  | [] => rfl
  | clause :: rest => by
      simp only [
        runCnfComparison,
        runClauseComparison_equal_implies_true
      ]
      change
        (runCnfComparison rest rest).clauseVisits + 1 =
          rest.length + 1
      rw [runCnfComparison_equal_clauseVisits]

/-- Equal-CNF comparison charges the complete literal traversal. -/
theorem runCnfComparison_equal_literalVisits :
    forall formula : Cnf,
      (runCnfComparison formula formula).literalVisits =
        Cnf.literalCount formula
  | [] => rfl
  | clause :: rest => by
      simp only [
        runCnfComparison,
        runClauseComparison_equal_implies_true
      ]
      change
        (runClauseComparison clause clause).literalVisits +
            (runCnfComparison rest rest).literalVisits =
          clause.length + Cnf.literalCount rest
      rw [
        runClauseComparison_equal_literalVisits,
        runCnfComparison_equal_literalVisits
      ]

/-! ## Instrumented history transformation and comparison -/

structure DecisionFlipRun where
  output : StructuralBranchDecision
  variableConstructorVisits : Nat
  deriving DecidableEq

def runDecisionFlip
    (selected : Var)
    (decision : StructuralBranchDecision) : DecisionFlipRun :=
  let comparison := runNatComparison decision.var selected
  { output := StructuralBranchDecision.flipAt selected decision
    variableConstructorVisits := comparison.constructorVisits }

theorem runDecisionFlip_output
    (selected : Var)
    (decision : StructuralBranchDecision) :
    (runDecisionFlip selected decision).output =
      StructuralBranchDecision.flipAt selected decision :=
  rfl

structure DecisionHistoryFlipRun where
  output : List StructuralBranchDecision
  decisionVisits : Nat
  variableConstructorVisits : Nat
  deriving DecidableEq

def runDecisionHistoryFlip
    (selected : Var) :
    List StructuralBranchDecision -> DecisionHistoryFlipRun
  | [] =>
      { output := []
        decisionVisits := 0
        variableConstructorVisits := 0 }
  | decision :: rest =>
      let head := runDecisionFlip selected decision
      let tail := runDecisionHistoryFlip selected rest
      { output := head.output :: tail.output
        decisionVisits := tail.decisionVisits + 1
        variableConstructorVisits :=
          head.variableConstructorVisits + tail.variableConstructorVisits }

theorem runDecisionHistoryFlip_output
    (selected : Var) :
    forall decisions : List StructuralBranchDecision,
      (runDecisionHistoryFlip selected decisions).output =
        flipStructuralDecisionsAt selected decisions
  | [] => rfl
  | decision :: rest => by
      change
        (runDecisionFlip selected decision).output ::
            (runDecisionHistoryFlip selected rest).output =
          StructuralBranchDecision.flipAt selected decision ::
            flipStructuralDecisionsAt selected rest
      rw [runDecisionFlip_output, runDecisionHistoryFlip_output]

/-- The transformer charges exactly one visit per input decision. -/
theorem runDecisionHistoryFlip_decisionVisits
    (selected : Var) :
    forall decisions : List StructuralBranchDecision,
      (runDecisionHistoryFlip selected decisions).decisionVisits =
        decisions.length
  | [] => rfl
  | _decision :: rest => by
      change
        (runDecisionHistoryFlip selected rest).decisionVisits + 1 =
          rest.length + 1
      rw [runDecisionHistoryFlip_decisionVisits]

structure DecisionComparisonRun where
  equal : Bool
  variableConstructorVisits : Nat
  deriving DecidableEq, Repr

def compareBool : Bool -> Bool -> Bool
  | false, false => true
  | true, true => true
  | false, true => false
  | true, false => false

theorem compareBool_true_implies_equal :
    forall left right : Bool,
      compareBool left right = true -> left = right
  | false, false, _ => rfl
  | true, true, _ => rfl
  | false, true, impossible => False.elim (Bool.noConfusion impossible)
  | true, false, impossible => False.elim (Bool.noConfusion impossible)

theorem compareBool_equal_implies_true
    (value : Bool) :
    compareBool value value = true := by
  cases value <;> rfl

def runDecisionComparison
    (left right : StructuralBranchDecision) : DecisionComparisonRun :=
  let variableRun := runNatComparison left.var right.var
  match variableRun.equal with
  | false =>
      { equal := false
        variableConstructorVisits := variableRun.constructorVisits }
  | true =>
      { equal := compareBool left.value right.value
        variableConstructorVisits := variableRun.constructorVisits }

theorem runDecisionComparison_true_implies_equal
    (left right : StructuralBranchDecision)
    (equal : (runDecisionComparison left right).equal = true) :
    left = right := by
  unfold runDecisionComparison at equal
  cases variableExact : (runNatComparison left.var right.var).equal with
  | false =>
      simp only [variableExact] at equal
      cases equal
  | true =>
      simp only [variableExact] at equal
      have varsSame : left.var = right.var :=
        runNatComparison_true_implies_equal _ _ variableExact
      have valuesSame : left.value = right.value :=
        compareBool_true_implies_equal _ _ equal
      cases left
      cases right
      cases varsSame
      cases valuesSame
      rfl

theorem runDecisionComparison_equal_implies_true
    (decision : StructuralBranchDecision) :
    (runDecisionComparison decision decision).equal = true := by
  simp only [runDecisionComparison, runNatComparison_equal_implies_true]
  exact compareBool_equal_implies_true decision.value

theorem runDecisionComparison_false_of_var_ne
    (left right : StructuralBranchDecision)
    (different : left.var ≠ right.var) :
    (runDecisionComparison left right).equal = false := by
  have comparisonFalse :
      (runNatComparison left.var right.var).equal = false :=
    runNatComparison_false_of_ne left.var right.var different
  unfold runDecisionComparison
  simp only
  split
  · rfl
  · rename_i comparisonTrue
    rw [comparisonTrue] at comparisonFalse
    cases comparisonFalse

structure DecisionHistoryComparisonRun where
  equal : Bool
  decisionVisits : Nat
  variableConstructorVisits : Nat
  deriving DecidableEq, Repr

def runDecisionHistoryComparison :
    List StructuralBranchDecision ->
      List StructuralBranchDecision ->
        DecisionHistoryComparisonRun
  | [], [] =>
      { equal := true
        decisionVisits := 0
        variableConstructorVisits := 0 }
  | [], _ :: _ =>
      { equal := false
        decisionVisits := 0
        variableConstructorVisits := 0 }
  | _ :: _, [] =>
      { equal := false
        decisionVisits := 0
        variableConstructorVisits := 0 }
  | left :: leftRest, right :: rightRest =>
      let head := runDecisionComparison left right
      match head.equal with
      | false =>
          { equal := false
            decisionVisits := 1
            variableConstructorVisits := head.variableConstructorVisits }
      | true =>
          let tail := runDecisionHistoryComparison leftRest rightRest
          { equal := tail.equal
            decisionVisits := tail.decisionVisits + 1
            variableConstructorVisits :=
              head.variableConstructorVisits + tail.variableConstructorVisits }

theorem runDecisionHistoryComparison_true_implies_equal :
    forall left right : List StructuralBranchDecision,
      (runDecisionHistoryComparison left right).equal = true -> left = right
  | [], [], _ => rfl
  | [], _ :: _, impossible => False.elim (Bool.noConfusion impossible)
  | _ :: _, [], impossible => False.elim (Bool.noConfusion impossible)
  | left :: leftRest, right :: rightRest, equal => by
      change
        (runDecisionHistoryComparison
          (left :: leftRest)
          (right :: rightRest)).equal = true at equal
      cases headExact : (runDecisionComparison left right).equal with
      | false =>
          simp only [runDecisionHistoryComparison, headExact] at equal
          cases equal
      | true =>
          simp only [runDecisionHistoryComparison, headExact] at equal
          have headSame :=
            runDecisionComparison_true_implies_equal left right headExact
          have tailSame :=
            runDecisionHistoryComparison_true_implies_equal
              leftRest rightRest equal
          cases headSame
          exact congrArg (List.cons left) tailSame

theorem runDecisionHistoryComparison_equal_implies_true :
    forall decisions : List StructuralBranchDecision,
      (runDecisionHistoryComparison decisions decisions).equal = true
  | [] => rfl
  | decision :: rest => by
      simp only [
        runDecisionHistoryComparison,
        runDecisionComparison_equal_implies_true
      ]
      exact runDecisionHistoryComparison_equal_implies_true rest

/-- Equal histories are still traversed completely and charged completely. -/
theorem runDecisionHistoryComparison_equal_decisionVisits :
    forall decisions : List StructuralBranchDecision,
      (runDecisionHistoryComparison decisions decisions).decisionVisits =
        decisions.length
  | [] => rfl
  | decision :: rest => by
      simp only [
        runDecisionHistoryComparison,
        runDecisionComparison_equal_implies_true
      ]
      change
        (runDecisionHistoryComparison rest rest).decisionVisits + 1 =
          rest.length + 1
      rw [runDecisionHistoryComparison_equal_decisionVisits]

/-- A final unequal marker is reached only after traversing the whole prefix. -/
theorem runDecisionHistoryComparison_pathVariablesFrom_decisionVisits
    (start count firstMarker secondMarker : Nat)
    (different : firstMarker ≠ secondMarker) :
    (runDecisionHistoryComparison
      (falseDecisionHistory
        (pathVariablesFrom start count firstMarker))
      (falseDecisionHistory
        (pathVariablesFrom start count secondMarker))).decisionVisits =
      count + 1 := by
  induction count generalizing start with
  | zero =>
      have markerFalse :
          (runDecisionComparison
            { var := firstMarker, value := false }
            { var := secondMarker, value := false }).equal = false := by
        exact
          runDecisionComparison_false_of_var_ne
            _
            _
            different
      change
        (runDecisionHistoryComparison
          [{ var := firstMarker, value := false }]
          [{ var := secondMarker, value := false }]).decisionVisits = 1
      rw [runDecisionHistoryComparison, markerFalse]
  | succ count inductionHypothesis =>
      have headTrue :
          (runDecisionComparison
            { var := start, value := false }
            { var := start, value := false }).equal = true :=
        runDecisionComparison_equal_implies_true _
      change
        (runDecisionHistoryComparison
          ({ var := start, value := false } ::
            falseDecisionHistory
              (pathVariablesFrom (start + 1) count firstMarker))
          ({ var := start, value := false } ::
            falseDecisionHistory
              (pathVariablesFrom (start + 1) count secondMarker))).decisionVisits =
          (count + 1) + 1
      rw [runDecisionHistoryComparison, headTrue]
      change
        (runDecisionHistoryComparison
          (falseDecisionHistory
            (pathVariablesFrom (start + 1) count firstMarker))
          (falseDecisionHistory
            (pathVariablesFrom (start + 1) count secondMarker))).decisionVisits + 1 =
          (count + 1) + 1
      rw [inductionHypothesis (start + 1)]

theorem runDecisionHistoryComparison_false_of_ne
    (left right : List StructuralBranchDecision)
    (different : left ≠ right) :
    (runDecisionHistoryComparison left right).equal = false := by
  cases exactResult : (runDecisionHistoryComparison left right).equal with
  | false => rfl
  | true =>
      exact
        False.elim
          (different
            (runDecisionHistoryComparison_true_implies_equal
              left right exactResult))

/-! ## Instrumented ungated relation search -/

structure InstrumentedFlipSearchStats where
  formulaTransformClauseVisits : Nat
  formulaTransformLiteralVisits : Nat
  formulaComparisonClauseVisits : Nat
  formulaComparisonLiteralVisits : Nat
  historyTransformDecisionVisits : Nat
  historyComparisonDecisionVisits : Nat
  variableConstructorVisits : Nat
  deriving DecidableEq, Repr

def zeroInstrumentedFlipSearchStats : InstrumentedFlipSearchStats :=
  { formulaTransformClauseVisits := 0
    formulaTransformLiteralVisits := 0
    formulaComparisonClauseVisits := 0
    formulaComparisonLiteralVisits := 0
    historyTransformDecisionVisits := 0
    historyComparisonDecisionVisits := 0
    variableConstructorVisits := 0 }

def InstrumentedFlipSearchStats.add
    (left right : InstrumentedFlipSearchStats) : InstrumentedFlipSearchStats :=
  { formulaTransformClauseVisits :=
      left.formulaTransformClauseVisits + right.formulaTransformClauseVisits
    formulaTransformLiteralVisits :=
      left.formulaTransformLiteralVisits + right.formulaTransformLiteralVisits
    formulaComparisonClauseVisits :=
      left.formulaComparisonClauseVisits + right.formulaComparisonClauseVisits
    formulaComparisonLiteralVisits :=
      left.formulaComparisonLiteralVisits + right.formulaComparisonLiteralVisits
    historyTransformDecisionVisits :=
      left.historyTransformDecisionVisits + right.historyTransformDecisionVisits
    historyComparisonDecisionVisits :=
      left.historyComparisonDecisionVisits + right.historyComparisonDecisionVisits
    variableConstructorVisits :=
      left.variableConstructorVisits + right.variableConstructorVisits }

def InstrumentedFlipSearchStats.total
    (stats : InstrumentedFlipSearchStats) : Nat :=
  stats.formulaTransformClauseVisits +
    stats.formulaTransformLiteralVisits +
    stats.formulaComparisonClauseVisits +
    stats.formulaComparisonLiteralVisits +
    stats.historyTransformDecisionVisits +
    stats.historyComparisonDecisionVisits +
    stats.variableConstructorVisits

structure InstrumentedFlipSearchRun
    {rootFormula : Cnf}
    (selected : Var)
    (source target : GeneratedStructuralBranchContext rootFormula) where
  relation? : Option (GeneratedStructuralFlipAtRelation selected source target)
  stats : InstrumentedFlipSearchStats

def instrumentedFormulaFlip
    {rootFormula : Cnf}
    (selected : Var)
    (source : GeneratedStructuralBranchContext rootFormula) : CnfFlipRun :=
  runCnfFlip selected source.context.formula

def instrumentedFormulaComparison
    {rootFormula : Cnf}
    (selected : Var)
    (source target : GeneratedStructuralBranchContext rootFormula) :
    CnfComparisonRun :=
  runCnfComparison
    target.context.formula
    (instrumentedFormulaFlip selected source).output

def instrumentedHistoryFlip
    {rootFormula : Cnf}
    (selected : Var)
    (source : GeneratedStructuralBranchContext rootFormula) :
    DecisionHistoryFlipRun :=
  runDecisionHistoryFlip selected source.context.decisions

def instrumentedHistoryComparison
    {rootFormula : Cnf}
    (selected : Var)
    (source target : GeneratedStructuralBranchContext rootFormula) :
    DecisionHistoryComparisonRun :=
  runDecisionHistoryComparison
    target.context.decisions
    (instrumentedHistoryFlip selected source).output

def runInstrumentedFlipSearch
    {rootFormula : Cnf}
    (selected : Var)
    (source target : GeneratedStructuralBranchContext rootFormula) :
    InstrumentedFlipSearchRun selected source target :=
  match formulaTrue :
      (instrumentedFormulaComparison selected source target).equal with
  | false =>
      { relation? := none
        stats :=
          { formulaTransformClauseVisits :=
              (instrumentedFormulaFlip selected source).clauseVisits
            formulaTransformLiteralVisits :=
              (instrumentedFormulaFlip selected source).literalVisits
            formulaComparisonClauseVisits :=
              (instrumentedFormulaComparison selected source target).clauseVisits
            formulaComparisonLiteralVisits :=
              (instrumentedFormulaComparison selected source target).literalVisits
            historyTransformDecisionVisits := 0
            historyComparisonDecisionVisits := 0
            variableConstructorVisits :=
              (instrumentedFormulaFlip
                selected source).variableConstructorVisits +
                (instrumentedFormulaComparison
                  selected source target).variableConstructorVisits } }
  | true =>
      let formulaExact :
          target.context.formula =
            Cnf.flipAt selected source.context.formula :=
        Eq.trans
          (runCnfComparison_true_implies_equal
            target.context.formula
            (instrumentedFormulaFlip selected source).output
            formulaTrue)
          (runCnfFlip_output selected source.context.formula)
      match historyTrue :
          (instrumentedHistoryComparison selected source target).equal with
      | false =>
          { relation? := none
            stats :=
              { formulaTransformClauseVisits :=
                  (instrumentedFormulaFlip selected source).clauseVisits
                formulaTransformLiteralVisits :=
                  (instrumentedFormulaFlip selected source).literalVisits
                formulaComparisonClauseVisits :=
                  (instrumentedFormulaComparison selected source target).clauseVisits
                formulaComparisonLiteralVisits :=
                  (instrumentedFormulaComparison selected source target).literalVisits
                historyTransformDecisionVisits :=
                  (instrumentedHistoryFlip selected source).decisionVisits
                historyComparisonDecisionVisits :=
                  (instrumentedHistoryComparison
                    selected source target).decisionVisits
                variableConstructorVisits :=
                  (instrumentedFormulaFlip
                    selected source).variableConstructorVisits +
                    (instrumentedFormulaComparison
                      selected source target).variableConstructorVisits +
                    (instrumentedHistoryFlip
                      selected source).variableConstructorVisits +
                  (instrumentedHistoryComparison
                      selected source target).variableConstructorVisits } }
      | true =>
          let decisionsExact :
              target.context.decisions =
                flipStructuralDecisionsAt selected source.context.decisions :=
            Eq.trans
              (runDecisionHistoryComparison_true_implies_equal
                target.context.decisions
                (instrumentedHistoryFlip selected source).output
                historyTrue)
              (runDecisionHistoryFlip_output
                selected
                source.context.decisions)
          { relation? := some
              { formulaExact := formulaExact
                decisionsExact := decisionsExact }
            stats :=
              { formulaTransformClauseVisits :=
                  (instrumentedFormulaFlip selected source).clauseVisits
                formulaTransformLiteralVisits :=
                  (instrumentedFormulaFlip selected source).literalVisits
                formulaComparisonClauseVisits :=
                  (instrumentedFormulaComparison selected source target).clauseVisits
                formulaComparisonLiteralVisits :=
                  (instrumentedFormulaComparison selected source target).literalVisits
                historyTransformDecisionVisits :=
                  (instrumentedHistoryFlip selected source).decisionVisits
                historyComparisonDecisionVisits :=
                  (instrumentedHistoryComparison
                    selected source target).decisionVisits
                variableConstructorVisits :=
                  (instrumentedFormulaFlip
                    selected source).variableConstructorVisits +
                    (instrumentedFormulaComparison
                      selected source target).variableConstructorVisits +
                    (instrumentedHistoryFlip
                      selected source).variableConstructorVisits +
                    (instrumentedHistoryComparison
                      selected source target).variableConstructorVisits } }

/--
The instrumented finder returns exactly the same proof-relevant relation as
the established executable finder.  This theorem lets discovery consume the
instrumented result itself instead of executing an uncharged shadow finder.
-/
theorem runInstrumentedFlipSearch_relation_exact
    {rootFormula : Cnf}
    (selected : Var)
    (source target : GeneratedStructuralBranchContext rootFormula) :
    (runInstrumentedFlipSearch selected source target).relation? =
      (generatedStructuralFlipAtSearch rootFormula selected).find
        source target := by
  unfold runInstrumentedFlipSearch
  split
  · rename_i formulaFalse
    have formulaDifferent :
        target.context.formula ≠
          Cnf.flipAt selected source.context.formula := by
      intro formulaExact
      have formulaOutputExact :
          target.context.formula =
            (instrumentedFormulaFlip selected source).output :=
        formulaExact.trans
          (runCnfFlip_output
            selected source.context.formula).symm
      have formulaTrue :
          (instrumentedFormulaComparison
            selected source target).equal = true := by
        unfold instrumentedFormulaComparison
        rw [formulaOutputExact]
        exact runCnfComparison_equal_implies_true _
      rw [formulaTrue] at formulaFalse
      cases formulaFalse
    have missing :
        (generatedStructuralFlipAtSearch rootFormula selected).find
          source target = none := by
      dsimp [generatedStructuralFlipAtSearch]
      rw [dif_neg formulaDifferent]
    exact missing.symm
  · rename_i formulaTrue
    have formulaExact :
        target.context.formula =
          Cnf.flipAt selected source.context.formula :=
      (runCnfComparison_true_implies_equal
        target.context.formula
        (instrumentedFormulaFlip selected source).output
        formulaTrue).trans
          (runCnfFlip_output selected source.context.formula)
    split
    · rename_i historyFalse
      have decisionsDifferent :
          target.context.decisions ≠
            flipStructuralDecisionsAt
              selected source.context.decisions := by
        intro decisionsExact
        have historyOutputExact :
            target.context.decisions =
              (instrumentedHistoryFlip selected source).output :=
          decisionsExact.trans
            (runDecisionHistoryFlip_output
              selected source.context.decisions).symm
        have historyTrue :
            (instrumentedHistoryComparison
              selected source target).equal = true := by
          unfold instrumentedHistoryComparison
          rw [historyOutputExact]
          exact runDecisionHistoryComparison_equal_implies_true _
        rw [historyTrue] at historyFalse
        cases historyFalse
      have missing :
          (generatedStructuralFlipAtSearch rootFormula selected).find
            source target = none := by
        dsimp [generatedStructuralFlipAtSearch]
        rw [dif_pos formulaExact, dif_neg decisionsDifferent]
      exact missing.symm
    · rename_i historyTrue
      have decisionsExact :
          target.context.decisions =
            flipStructuralDecisionsAt
              selected source.context.decisions :=
        (runDecisionHistoryComparison_true_implies_equal
          target.context.decisions
          (instrumentedHistoryFlip selected source).output
          historyTrue).trans
            (runDecisionHistoryFlip_output
              selected source.context.decisions)
      let relation :
          GeneratedStructuralFlipAtRelation selected source target :=
        { formulaExact := formulaExact
          decisionsExact := decisionsExact }
      have foundExact :
          (generatedStructuralFlipAtSearch rootFormula selected).find
            source target = some relation := by
        dsimp [generatedStructuralFlipAtSearch]
        rw [
          dif_pos relation.formulaExact,
          dif_pos relation.decisionsExact
        ]
      rw [foundExact]

/-- Every relation test charges the full source CNF transformation it executes. -/
theorem runInstrumentedFlipSearch_formulaTransformLiteralVisits
    {rootFormula : Cnf}
    (selected : Var)
    (source target : GeneratedStructuralBranchContext rootFormula) :
    (runInstrumentedFlipSearch
      selected source target).stats.formulaTransformLiteralVisits =
        Cnf.literalCount source.context.formula := by
  unfold runInstrumentedFlipSearch
  split
  · exact runCnfFlip_literalVisits selected source.context.formula
  · split <;>
      exact runCnfFlip_literalVisits selected source.context.formula

theorem runInstrumentedFlipSearch_found_of_relation
    {rootFormula : Cnf}
    {selected : Var}
    {source target : GeneratedStructuralBranchContext rootFormula}
    (relation : GeneratedStructuralFlipAtRelation selected source target) :
    (runInstrumentedFlipSearch selected source target).relation? ≠ none := by
  have formulaOutput :
      (instrumentedFormulaFlip selected source).output =
        Cnf.flipAt selected source.context.formula :=
    runCnfFlip_output selected source.context.formula
  have formulaSame :
      target.context.formula =
        (instrumentedFormulaFlip selected source).output :=
    Eq.trans relation.formulaExact formulaOutput.symm
  have formulaTrue :
      (instrumentedFormulaComparison selected source target).equal = true := by
    unfold instrumentedFormulaComparison
    rw [formulaSame]
    exact runCnfComparison_equal_implies_true _
  unfold runInstrumentedFlipSearch
  split
  · rename_i formulaFalse
    rw [formulaFalse] at formulaTrue
    cases formulaTrue
  · have historyOutput :
        (instrumentedHistoryFlip selected source).output =
          flipStructuralDecisionsAt selected source.context.decisions :=
      runDecisionHistoryFlip_output selected source.context.decisions
    have historySame :
        target.context.decisions =
          (instrumentedHistoryFlip selected source).output :=
      Eq.trans relation.decisionsExact historyOutput.symm
    have historyTrue :
        (instrumentedHistoryComparison selected source target).equal = true := by
      unfold instrumentedHistoryComparison
      rw [historySame]
      exact runDecisionHistoryComparison_equal_implies_true _
    split
    · rename_i historyFalse
      rw [historyFalse] at historyTrue
      cases historyTrue
    · intro impossible
      cases impossible

theorem runInstrumentedFlipSearch_none_of_history_mismatch
    {rootFormula : Cnf}
    {selected : Var}
    {source target : GeneratedStructuralBranchContext rootFormula}
    (formulaExact :
      target.context.formula =
        Cnf.flipAt selected source.context.formula)
    (historyMismatch :
      target.context.decisions ≠
        flipStructuralDecisionsAt selected source.context.decisions) :
    (runInstrumentedFlipSearch selected source target).relation? = none := by
  have formulaOutput :
      (instrumentedFormulaFlip selected source).output =
        Cnf.flipAt selected source.context.formula :=
    runCnfFlip_output selected source.context.formula
  have formulaSame :
      target.context.formula =
        (instrumentedFormulaFlip selected source).output :=
    Eq.trans formulaExact formulaOutput.symm
  have formulaTrue :
      (instrumentedFormulaComparison selected source target).equal = true := by
    unfold instrumentedFormulaComparison
    rw [formulaSame]
    exact runCnfComparison_equal_implies_true _
  unfold runInstrumentedFlipSearch
  split
  · rename_i formulaFalse
    rw [formulaFalse] at formulaTrue
  · have historyOutput :
        (instrumentedHistoryFlip selected source).output =
          flipStructuralDecisionsAt selected source.context.decisions :=
      runDecisionHistoryFlip_output selected source.context.decisions
    have comparisonDifferent :
        target.context.decisions ≠
          (instrumentedHistoryFlip selected source).output := by
      intro same
      exact historyMismatch (Eq.trans same historyOutput)
    have historyFalse :
        (instrumentedHistoryComparison selected source target).equal = false := by
      unfold instrumentedHistoryComparison
      exact
        runDecisionHistoryComparison_false_of_ne
          target.context.decisions
          (instrumentedHistoryFlip selected source).output
          comparisonDifferent
    split
    · rfl
    · rename_i historyTrue
      rw [historyTrue] at historyFalse
      cases historyFalse

/-! ## Instrumented endogenous candidate exploration -/

/-- One candidate attempt, including the structural work used to decide it. -/
structure InstrumentedCandidateAttempt
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (candidate : Var) where
  discovery? : Option (CandidateFlipDiscovery state candidate)
  stats : InstrumentedFlipSearchStats

/--
One candidate attempt.  The selected witness and the counters are both
produced by the same instrumented relation search; no shadow finder is run.
-/
def runInstrumentedCandidateAttempt
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (candidate : Var) : InstrumentedCandidateAttempt state candidate :=
  if freshness :
      structuralDecisionsAvoidCheck candidate state.context.decisions = true then
      let fresh :=
        structuralDecisionsAvoid_of_check_true
          candidate
          state.context.decisions
          freshness
      let source :=
        GeneratedStructuralBranchContext.child
          state candidate false fresh
      let target :=
        GeneratedStructuralBranchContext.child
          state candidate true fresh
      let search := runInstrumentedFlipSearch candidate source target
      match search.relation? with
      | none =>
          { discovery? := none
            stats := search.stats }
      | some relation =>
          { discovery? :=
              some
                { fresh := fresh
                  relation := relation }
            stats := search.stats }
  else
    { discovery? := none
      stats := zeroInstrumentedFlipSearchStats }

/-- Data retained for every attempted candidate, including rejected ones. -/
structure InstrumentedCandidateAttemptRecord where
  candidate : Var
  succeeded : Bool
  stats : InstrumentedFlipSearchStats
  deriving DecidableEq, Repr

def instrumentedCandidateAttemptRecord
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    (candidate : Var)
    (attempt : InstrumentedCandidateAttempt state candidate) :
    InstrumentedCandidateAttemptRecord :=
  { candidate := candidate
    succeeded := attempt.discovery?.isSome
    stats := attempt.stats }

/-- Outcome of the one-pass exploration, with the complete attempted prefix. -/
structure InstrumentedEndogenousDiscoveryOutcome
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) where
  discovered? : Option (EndogenousFlipDiscovery state)
  attemptTrace : List InstrumentedCandidateAttemptRecord

def exploreInstrumentedCandidates
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    List Var -> InstrumentedEndogenousDiscoveryOutcome state
  | [] =>
      { discovered? := none
        attemptTrace := [] }
  | candidate :: rest =>
      let attempt := runInstrumentedCandidateAttempt state candidate
      let record := instrumentedCandidateAttemptRecord candidate attempt
      match attempt.discovery? with
      | some candidateDiscovery =>
          { discovered? := some ⟨candidate, candidateDiscovery⟩
            attemptTrace := [record] }
      | none =>
          let tail := exploreInstrumentedCandidates state rest
          { discovered? := tail.discovered?
            attemptTrace := record :: tail.attemptTrace }

/-- Extraction and instrumented exploration are produced in one run. -/
structure InstrumentedEndogenousDiscoveryRun
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) where
  extraction : CandidateExtractionRun
  outcome : InstrumentedEndogenousDiscoveryOutcome state

def runInstrumentedEndogenousDiscovery
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    InstrumentedEndogenousDiscoveryRun state :=
  let extraction := runCandidateExtraction state
  { extraction := extraction
    outcome :=
      exploreInstrumentedCandidates state extraction.candidates }

def aggregateInstrumentedAttemptStats :
    List InstrumentedCandidateAttemptRecord -> InstrumentedFlipSearchStats
  | [] => zeroInstrumentedFlipSearchStats
  | attempt :: rest =>
      attempt.stats.add (aggregateInstrumentedAttemptStats rest)

theorem runInstrumentedCandidateAttempt_discovery_exact
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula)
    (candidate : Var) :
    (runInstrumentedCandidateAttempt state candidate).discovery? =
      tryEndogenousFlipCandidate state candidate := by
  by_cases freshness :
      structuralDecisionsAvoidCheck candidate state.context.decisions = true
  · unfold runInstrumentedCandidateAttempt
    rw [dif_pos freshness]
    unfold tryEndogenousFlipCandidate
    split
    · rename_i checkFalse
      rw [checkFalse] at freshness
      cases freshness
    · rename_i checkTrue
      have proofExact : checkTrue = freshness :=
        Subsingleton.elim _ _
      cases proofExact
      simp only [runInstrumentedFlipSearch_relation_exact]
      split
      · rename_i relationMissing
        rw [relationMissing]
      · rename_i relation relationFound
        rw [relationFound]
  · have freshnessFalse :
        structuralDecisionsAvoidCheck
          candidate state.context.decisions = false := by
      cases checked :
          structuralDecisionsAvoidCheck candidate state.context.decisions with
      | false => rfl
      | true => exact False.elim (freshness checked)
    have tryNone :
        tryEndogenousFlipCandidate state candidate = none := by
      unfold tryEndogenousFlipCandidate
      split
      · rfl
      · rename_i checkTrue
        rw [checkTrue] at freshnessFalse
        cases freshnessFalse
    rw [tryNone]
    unfold runInstrumentedCandidateAttempt
    rw [dif_neg freshness]

theorem exploreInstrumentedCandidates_discovered_exact
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    forall candidates : List Var,
      (exploreInstrumentedCandidates state candidates).discovered? =
        (exploreStructuralCandidates state candidates).discovered?
  | [] => rfl
  | candidate :: rest => by
      unfold exploreInstrumentedCandidates exploreStructuralCandidates
      dsimp only
      rw [runInstrumentedCandidateAttempt_discovery_exact]
      cases candidateResult :
          tryEndogenousFlipCandidate state candidate with
      | none =>
          exact exploreInstrumentedCandidates_discovered_exact state rest
      | some _candidateDiscovery =>
          rfl

theorem exploreInstrumentedCandidates_attemptTrace_length
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    forall candidates : List Var,
      (exploreInstrumentedCandidates state candidates).attemptTrace.length =
        (exploreStructuralCandidates state candidates).attempts
  | [] => rfl
  | candidate :: rest => by
      unfold exploreInstrumentedCandidates exploreStructuralCandidates
      dsimp only
      rw [runInstrumentedCandidateAttempt_discovery_exact]
      cases candidateResult :
          tryEndogenousFlipCandidate state candidate with
      | none =>
          change
            (exploreInstrumentedCandidates
                state rest).attemptTrace.length + 1 =
              (exploreStructuralCandidates state rest).attempts + 1
          exact
            congrArg
              (fun attempts => attempts + 1)
              (exploreInstrumentedCandidates_attemptTrace_length state rest)
      | some _candidateDiscovery =>
          rfl

theorem exploreInstrumentedCandidates_attemptedCandidates
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    forall candidates : List Var,
      (exploreInstrumentedCandidates
          state candidates).attemptTrace.map
            InstrumentedCandidateAttemptRecord.candidate =
        candidates.take
          (exploreStructuralCandidates state candidates).attempts
  | [] => rfl
  | candidate :: rest => by
      unfold exploreInstrumentedCandidates exploreStructuralCandidates
      dsimp only
      rw [runInstrumentedCandidateAttempt_discovery_exact]
      cases candidateResult :
          tryEndogenousFlipCandidate state candidate with
      | none =>
          change
            candidate ::
                (exploreInstrumentedCandidates
                  state rest).attemptTrace.map
                    InstrumentedCandidateAttemptRecord.candidate =
              candidate ::
                rest.take
                  (exploreStructuralCandidates state rest).attempts
          exact
            congrArg
              (List.cons candidate)
              (exploreInstrumentedCandidates_attemptedCandidates
                state rest)
      | some _candidateDiscovery =>
          rfl

theorem runInstrumentedEndogenousDiscovery_discovered_exact
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    (runInstrumentedEndogenousDiscovery state).outcome.discovered? =
      (runEndogenousFlipDiscovery state).outcome.discovered? := by
  unfold
    runInstrumentedEndogenousDiscovery
    runEndogenousFlipDiscovery
  exact
    exploreInstrumentedCandidates_discovered_exact
      state
      (runCandidateExtraction state).candidates

theorem runInstrumentedEndogenousDiscovery_attemptTrace_length
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    (runInstrumentedEndogenousDiscovery
        state).outcome.attemptTrace.length =
      (runEndogenousFlipDiscovery state).outcome.attempts := by
  unfold
    runInstrumentedEndogenousDiscovery
    runEndogenousFlipDiscovery
  exact
    exploreInstrumentedCandidates_attemptTrace_length
      state
      (runCandidateExtraction state).candidates

theorem runInstrumentedEndogenousDiscovery_attemptedCandidates
    {rootFormula : Cnf}
    (state : GeneratedStructuralBranchContext rootFormula) :
    (runInstrumentedEndogenousDiscovery
        state).outcome.attemptTrace.map
          InstrumentedCandidateAttemptRecord.candidate =
      (runCandidateExtraction state).candidates.take
        (runEndogenousFlipDiscovery state).outcome.attempts := by
  unfold
    runInstrumentedEndogenousDiscovery
    runEndogenousFlipDiscovery
  exact
    exploreInstrumentedCandidates_attemptedCandidates
      state
      (runCandidateExtraction state).candidates

/-! ## Operational execution of the discovered transport code -/

/-- Concrete source assignment used by the operational benchmark. -/
def operationalFalseAssignment : Assignment :=
  fun _variable => false

/-- The concrete assignment realizes every generated false-only history. -/
theorem operationalFalseAssignment_holds :
    forall variables : List Var,
      StructuralDecisionsHold
        operationalFalseAssignment
        (falseDecisionHistory variables)
  | [] => True.intro
  | _variable :: rest =>
      ⟨rfl, operationalFalseAssignment_holds rest⟩

/-- An actual continuation of the common source state. -/
def operationalSourceContinuation
    (input : Nat) :
    GeneratedStructuralBranchContinuation
      (operationalSource input) := by
  refine ⟨operationalFalseAssignment, ?_⟩
  change
    operationalFalseAssignment (growingDiscoverySplitVar input) = false ∧
      StructuralDecisionsHold
        operationalFalseAssignment
        (operationalCommonParentPath input).state.context.decisions
  constructor
  · rfl
  · rw [(operationalCommonParentPath input).decisionsExact]
    exact
      operationalFalseAssignment_holds
        (operationalSourcePathVariables input)

/-- Public result of executing one instrumented relation search. -/
structure OperationalTransportRun where
  terminalBit : Option Bool
  codeAtoms : Nat
  terminalReadouts : Nat
  stats : InstrumentedFlipSearchStats
  deriving DecidableEq, Repr

/--
Consume a completed search run.  This API cannot reconstruct or bypass
validation: code production is a pattern match on the supplied run's relation.
-/
def executeInstrumentedSearchResult
    {rootFormula : Cnf}
    (selected observed : Var)
    (source target : GeneratedStructuralBranchContext rootFormula)
    (continuation : GeneratedStructuralBranchContinuation source)
    (search : InstrumentedFlipSearchRun selected source target) :
    OperationalTransportRun :=
  match search.relation? with
  | none =>
      { terminalBit := none
        codeAtoms := 0
        terminalReadouts := 0
        stats := search.stats }
  | some relation =>
      let code := TransportCode.ofGenerator relation
      let transported :=
        (code.eval
          (generatedStructuralFlipAtAction rootFormula selected)).map
          continuation
      { terminalBit := some (transported.1 observed)
        codeAtoms := code.size
        terminalReadouts := 1
        stats := search.stats }

/--
On success the published terminal is definitionally the readout of the
continuation returned by evaluation of the discovered one-atom code.
-/
theorem executeInstrumentedSearchResult_success_exact
    {rootFormula : Cnf}
    (selected observed : Var)
    (source target : GeneratedStructuralBranchContext rootFormula)
    (continuation : GeneratedStructuralBranchContinuation source)
    (search : InstrumentedFlipSearchRun selected source target)
    (relation : GeneratedStructuralFlipAtRelation selected source target)
    (found : search.relation? = some relation) :
    (executeInstrumentedSearchResult
        selected observed source target continuation search).terminalBit =
          some
            (((((TransportCode.ofGenerator relation).eval
                (generatedStructuralFlipAtAction rootFormula selected)).map
              continuation).1) observed) /\
      (executeInstrumentedSearchResult
        selected observed source target continuation search).codeAtoms =
          (TransportCode.ofGenerator relation).size /\
      (executeInstrumentedSearchResult
        selected observed source target continuation search).terminalReadouts =
          1 := by
  unfold executeInstrumentedSearchResult
  rw [found]
  exact ⟨rfl, rfl, rfl⟩

/--
Search, code construction, code evaluation, and terminal observation in that
order.  In the successful branch the terminal bit is read from the continuation
returned by `TransportCode.eval`; the target state is never used as a result.
-/
def executeInstrumentedTransport
    {rootFormula : Cnf}
    (selected observed : Var)
    (source target : GeneratedStructuralBranchContext rootFormula)
    (continuation : GeneratedStructuralBranchContinuation source) :
    OperationalTransportRun :=
  executeInstrumentedSearchResult
    selected
    observed
    source
    target
    continuation
    (runInstrumentedFlipSearch selected source target)

theorem executeInstrumentedTransport_stats
    {rootFormula : Cnf}
    (selected observed : Var)
    (source target : GeneratedStructuralBranchContext rootFormula)
    (continuation : GeneratedStructuralBranchContinuation source) :
    (executeInstrumentedTransport
      selected observed source target continuation).stats =
        (runInstrumentedFlipSearch selected source target).stats := by
  unfold executeInstrumentedTransport executeInstrumentedSearchResult
  cases found : (runInstrumentedFlipSearch selected source target).relation? <;>
    rfl

theorem instrumentedFormulaComparison_true_of_exact
    {rootFormula : Cnf}
    {selected : Var}
    {source target : GeneratedStructuralBranchContext rootFormula}
    (formulaExact :
      target.context.formula =
        Cnf.flipAt selected source.context.formula) :
    (instrumentedFormulaComparison selected source target).equal = true := by
  have outputExact :
      (instrumentedFormulaFlip selected source).output =
        Cnf.flipAt selected source.context.formula :=
    runCnfFlip_output selected source.context.formula
  unfold instrumentedFormulaComparison
  rw [formulaExact, ← outputExact]
  exact runCnfComparison_equal_implies_true _

/-- Once formula comparison succeeds, the recorded history work is the work run. -/
theorem runInstrumentedFlipSearch_historyComparisonDecisionVisits
    {rootFormula : Cnf}
    (selected : Var)
    (source target : GeneratedStructuralBranchContext rootFormula)
    (formulaTrue :
      (instrumentedFormulaComparison selected source target).equal = true) :
    (runInstrumentedFlipSearch selected source target).stats.historyComparisonDecisionVisits =
      (instrumentedHistoryComparison selected source target).decisionVisits := by
  unfold runInstrumentedFlipSearch
  split
  · rename_i formulaFalse
    rw [formulaFalse] at formulaTrue
    cases formulaTrue
  · split <;> rfl

/-- The successful same-input organization executes one transport atom. -/
def operationalPositiveRun (input : Nat) : OperationalTransportRun :=
  executeInstrumentedTransport
    (growingDiscoverySplitVar input)
    (growingDiscoverySplitVar input)
    (operationalSource input)
    (operationalPositiveTarget input)
    (operationalSourceContinuation input)

/-- The provenance-mismatched organization executes the identical procedure. -/
def operationalNegativeRun (input : Nat) : OperationalTransportRun :=
  executeInstrumentedTransport
    (growingDiscoverySplitVar input)
    (growingDiscoverySplitVar input)
    (operationalSource input)
    (operationalNegativeTarget input)
    (operationalSourceContinuation input)

/-- Code evaluation flips the selected source bit in the positive case. -/
theorem operationalPositiveRun_terminal
    (input : Nat) :
    (operationalPositiveRun input).terminalBit = some true := by
  unfold
    operationalPositiveRun
    executeInstrumentedTransport
    executeInstrumentedSearchResult
  generalize relationExact :
      (runInstrumentedFlipSearch
        (growingDiscoverySplitVar input)
        (operationalSource input)
        (operationalPositiveTarget input)).relation? = relationOption
  cases relationOption with
  | none =>
      exact
        False.elim
          ((runInstrumentedFlipSearch_found_of_relation
              (operationalPositiveRelation input))
            relationExact)
  | some relation =>
      dsimp [TransportCode.ofGenerator, TransportCode.eval]
      change
        some
            ((relation.mapContinuation
                (operationalSourceContinuation input)).1
              (growingDiscoverySplitVar input)) =
          some true
      rw [
        relation.mapContinuation_assignment
          (operationalSourceContinuation input),
        Assignment.flipAt_selected
      ]
      rfl

/-- The positive run's executed syntax contains exactly one primitive atom. -/
theorem operationalPositiveRun_codeAtoms
    (input : Nat) :
    (operationalPositiveRun input).codeAtoms = 1 := by
  unfold
    operationalPositiveRun
    executeInstrumentedTransport
    executeInstrumentedSearchResult
  generalize relationExact :
      (runInstrumentedFlipSearch
        (growingDiscoverySplitVar input)
        (operationalSource input)
        (operationalPositiveTarget input)).relation? = relationOption
  cases relationOption with
  | none =>
      exact
        False.elim
          ((runInstrumentedFlipSearch_found_of_relation
              (operationalPositiveRelation input))
            relationExact)
  | some _relation =>
      rfl

/-- The successful branch records the readout performed on the transported continuation. -/
theorem operationalPositiveRun_terminalReadouts
    (input : Nat) :
    (operationalPositiveRun input).terminalReadouts = 1 := by
  unfold
    operationalPositiveRun
    executeInstrumentedTransport
    executeInstrumentedSearchResult
  generalize relationExact :
      (runInstrumentedFlipSearch
        (growingDiscoverySplitVar input)
        (operationalSource input)
        (operationalPositiveTarget input)).relation? = relationOption
  cases relationOption with
  | none =>
      exact
        False.elim
          ((runInstrumentedFlipSearch_found_of_relation
              (operationalPositiveRelation input))
            relationExact)
  | some _relation =>
      rfl

/-- The failed history comparison prevents code production and execution. -/
theorem operationalNegativeRun_terminal
    (input : Nat) :
    (operationalNegativeRun input).terminalBit = none := by
  unfold
    operationalNegativeRun
    executeInstrumentedTransport
    executeInstrumentedSearchResult
  generalize relationExact :
      (runInstrumentedFlipSearch
        (growingDiscoverySplitVar input)
        (operationalSource input)
        (operationalNegativeTarget input)).relation? = relationOption
  cases relationOption with
  | none => rfl
  | some _relation =>
      have missing :=
        runInstrumentedFlipSearch_none_of_history_mismatch
          (operationalNegative_formula_matches input)
          (operationalNegative_decisions_mismatch input)
      rw [relationExact] at missing
      cases missing

theorem operationalNegativeRun_codeAtoms
    (input : Nat) :
    (operationalNegativeRun input).codeAtoms = 0 := by
  unfold
    operationalNegativeRun
    executeInstrumentedTransport
    executeInstrumentedSearchResult
  generalize relationExact :
      (runInstrumentedFlipSearch
        (growingDiscoverySplitVar input)
        (operationalSource input)
        (operationalNegativeTarget input)).relation? = relationOption
  cases relationOption with
  | none => rfl
  | some _relation =>
      have missing :=
        runInstrumentedFlipSearch_none_of_history_mismatch
          (operationalNegative_formula_matches input)
          (operationalNegative_decisions_mismatch input)
      rw [relationExact] at missing
      cases missing

/-- A failed relation search performs no readout on a fabricated terminal. -/
theorem operationalNegativeRun_terminalReadouts
    (input : Nat) :
    (operationalNegativeRun input).terminalReadouts = 0 := by
  unfold
    operationalNegativeRun
    executeInstrumentedTransport
    executeInstrumentedSearchResult
  generalize relationExact :
      (runInstrumentedFlipSearch
        (growingDiscoverySplitVar input)
        (operationalSource input)
        (operationalNegativeTarget input)).relation? = relationOption
  cases relationOption with
  | none => rfl
  | some _relation =>
      have missing :=
        runInstrumentedFlipSearch_none_of_history_mismatch
          (operationalNegative_formula_matches input)
          (operationalNegative_decisions_mismatch input)
      rw [relationExact] at missing
      cases missing

/-- The successful history comparison traverses the complete growing path. -/
theorem operationalPositive_historyComparison_decisionVisits
    (input : Nat) :
    (instrumentedHistoryComparison
      (growingDiscoverySplitVar input)
      (operationalSource input)
      (operationalPositiveTarget input)).decisionVisits =
        input + 2 := by
  unfold instrumentedHistoryComparison instrumentedHistoryFlip
  rw [
    runDecisionHistoryFlip_output,
    ← (operationalPositiveRelation input).decisionsExact,
    runDecisionHistoryComparison_equal_decisionVisits
  ]
  change
    ((operationalCommonParentPath input).state.context.decisions).length + 1 =
      input + 2
  rw [
    (operationalCommonParentPath input).decisionsExact,
    falseDecisionHistory_length
  ]
  unfold operationalSourcePathVariables
  rw [pathVariablesFrom_length]

/-- The failed comparison also reaches the final, deeply placed mismatch. -/
theorem operationalNegative_historyComparison_decisionVisits
    (input : Nat) :
    (instrumentedHistoryComparison
      (growingDiscoverySplitVar input)
      (operationalSource input)
      (operationalNegativeTarget input)).decisionVisits =
        input + 2 := by
  unfold instrumentedHistoryComparison instrumentedHistoryFlip
  rw [runDecisionHistoryFlip_output]
  change
    (runDecisionHistoryComparison
      ({ var := growingDiscoverySplitVar input, value := true } ::
        (operationalMismatchedParentPath input).state.context.decisions)
      (flipStructuralDecisionsAt
        (growingDiscoverySplitVar input)
        ({ var := growingDiscoverySplitVar input, value := false } ::
          (operationalCommonParentPath input).state.context.decisions))).decisionVisits =
      input + 2
  rw [
    (operationalMismatchedParentPath input).decisionsExact,
    (operationalCommonParentPath input).decisionsExact
  ]
  dsimp [flipStructuralDecisionsAt, StructuralBranchDecision.flipAt]
  rw [if_pos rfl]
  have sourceAvoids :
      StructuralDecisionsAvoid
        (growingDiscoverySplitVar input)
        (falseDecisionHistory (operationalSourcePathVariables input)) := by
    rw [← (operationalCommonParentPath input).decisionsExact]
    exact operationalEngineFreshCommon input
  rw [flipStructuralDecisionsAt_eq_self sourceAvoids]
  simp only [Bool.not_false]
  have headTrue :
      (runDecisionComparison
        { var := growingDiscoverySplitVar input, value := true }
        { var := growingDiscoverySplitVar input, value := true }).equal = true :=
    runDecisionComparison_equal_implies_true _
  rw [runDecisionHistoryComparison, headTrue]
  change
    (runDecisionHistoryComparison
      (falseDecisionHistory (operationalMismatchedPathVariables input))
      (falseDecisionHistory (operationalSourcePathVariables input))).decisionVisits + 1 =
        input + 2
  unfold operationalMismatchedPathVariables operationalSourcePathVariables
  rw [
    runDecisionHistoryComparison_pathVariablesFrom_decisionVisits
      (input + 4)
      input
      (operationalTargetMarker input)
      (operationalSourceMarker input)
      (by
        intro same
        exact
          Constructive.nat_ne_add_one
            (operationalSourceMarker input)
            same.symm)
  ]

theorem operationalPositiveRun_historyComparisonDecisionVisits
    (input : Nat) :
    (operationalPositiveRun input).stats.historyComparisonDecisionVisits =
      input + 2 := by
  calc
    (operationalPositiveRun input).stats.historyComparisonDecisionVisits =
        (runInstrumentedFlipSearch
          (growingDiscoverySplitVar input)
          (operationalSource input)
          (operationalPositiveTarget input)).stats.historyComparisonDecisionVisits := by
            rw [
              operationalPositiveRun,
              executeInstrumentedTransport_stats
            ]
    _ =
        (instrumentedHistoryComparison
          (growingDiscoverySplitVar input)
          (operationalSource input)
          (operationalPositiveTarget input)).decisionVisits :=
      runInstrumentedFlipSearch_historyComparisonDecisionVisits
        _ _ _
        (instrumentedFormulaComparison_true_of_exact
          (operationalPositiveRelation input).formulaExact)
    _ = input + 2 :=
      operationalPositive_historyComparison_decisionVisits input

theorem operationalNegativeRun_historyComparisonDecisionVisits
    (input : Nat) :
    (operationalNegativeRun input).stats.historyComparisonDecisionVisits =
      input + 2 := by
  calc
    (operationalNegativeRun input).stats.historyComparisonDecisionVisits =
        (runInstrumentedFlipSearch
          (growingDiscoverySplitVar input)
          (operationalSource input)
          (operationalNegativeTarget input)).stats.historyComparisonDecisionVisits := by
            rw [
              operationalNegativeRun,
              executeInstrumentedTransport_stats
            ]
    _ =
        (instrumentedHistoryComparison
          (growingDiscoverySplitVar input)
          (operationalSource input)
          (operationalNegativeTarget input)).decisionVisits :=
      runInstrumentedFlipSearch_historyComparisonDecisionVisits
        _ _ _
        (instrumentedFormulaComparison_true_of_exact
          (operationalNegative_formula_matches input))
    _ = input + 2 :=
      operationalNegative_historyComparison_decisionVisits input

/-! ## Endogenous discovery retained by the operational pipeline -/

/--
Data-only trace exported by discovery.  It retains the complete extracted
candidate stream, recursively produced extraction counters, the exact number
of attempted candidates, and the selected variable when one was found.
-/
structure RetainedDiscoveryTrace where
  candidates : List Var
  extractionStats : CandidateExtractionStats
  attemptTrace : List InstrumentedCandidateAttemptRecord
  relationStats : InstrumentedFlipSearchStats
  selected? : Option Var
  deriving DecidableEq, Repr

def RetainedDiscoveryTrace.attempts
    (trace : RetainedDiscoveryTrace) : Nat :=
  trace.attemptTrace.length

/-- Retain executable discovery output without reconstructing its answer. -/
def retainDiscoveryTrace
    {rootFormula : Cnf}
    {state : GeneratedStructuralBranchContext rootFormula}
    (run : InstrumentedEndogenousDiscoveryRun state) : RetainedDiscoveryTrace :=
  { candidates := run.extraction.candidates
    extractionStats := run.extraction.stats
    attemptTrace := run.outcome.attemptTrace
    relationStats :=
      aggregateInstrumentedAttemptStats run.outcome.attemptTrace
    selected? := run.outcome.discovered?.map EndogenousFlipDiscovery.var }

/-- The proof-relevant discovery run used by the integrated benchmark. -/
def operationalInstrumentedDiscoveryRun
    (input : Nat) :
    InstrumentedEndogenousDiscoveryRun
      (distinctGrowingDiscoveryRoot input) :=
  runInstrumentedEndogenousDiscovery
    (distinctGrowingDiscoveryRoot input)

/-- The public data trace is projected from that actual proof-relevant run. -/
def operationalDiscoveryTrace (input : Nat) : RetainedDiscoveryTrace :=
  retainDiscoveryTrace (operationalInstrumentedDiscoveryRun input)

theorem operationalInstrumentedDiscoveryRun_found
    (input : Nat) :
    exists discovery,
      (operationalInstrumentedDiscoveryRun
        input).outcome.discovered? = some discovery /\
      discovery.var = growingDiscoverySplitVar input := by
  rcases distinctGrowingDiscovery_found_after_exact_attempts input with
    ⟨discovery, found, selected, _attempts⟩
  refine ⟨discovery, ?_, selected⟩
  unfold operationalInstrumentedDiscoveryRun
  rw [runInstrumentedEndogenousDiscovery_discovered_exact]
  exact found

theorem operationalDiscoveryTrace_selected
    (input : Nat) :
    (operationalDiscoveryTrace input).selected? =
      some (growingDiscoverySplitVar input) := by
  rcases distinctGrowingDiscovery_found_after_exact_attempts input with
    ⟨discovery, found, selected, _attempts⟩
  unfold
    operationalDiscoveryTrace
    operationalInstrumentedDiscoveryRun
    retainDiscoveryTrace
  rw [runInstrumentedEndogenousDiscovery_discovered_exact]
  rw [found]
  change some discovery.var = some (growingDiscoverySplitVar input)
  rw [selected]

theorem operationalInstrumentedDiscovery_selected_of_found
    (input : Nat)
    (discovery :
      EndogenousFlipDiscovery (distinctGrowingDiscoveryRoot input))
    (found :
      (operationalInstrumentedDiscoveryRun
        input).outcome.discovered? = some discovery) :
    discovery.var = growingDiscoverySplitVar input := by
  have selected := operationalDiscoveryTrace_selected input
  unfold operationalDiscoveryTrace retainDiscoveryTrace at selected
  rw [found] at selected
  exact Option.some.inj selected

theorem operationalDiscoveryTrace_attempts
    (input : Nat) :
    (operationalDiscoveryTrace input).attempts = input + 2 := by
  rcases distinctGrowingDiscovery_found_after_exact_attempts input with
    ⟨_discovery, _found, _selected, attempts⟩
  unfold
    operationalDiscoveryTrace
    operationalInstrumentedDiscoveryRun
    retainDiscoveryTrace
    RetainedDiscoveryTrace.attempts
  rw [runInstrumentedEndogenousDiscovery_attemptTrace_length]
  exact attempts

theorem operationalDiscoveryTrace_extraction
    (input : Nat) :
    (operationalDiscoveryTrace input).extractionStats.clauseVisits = 3 /\
      (operationalDiscoveryTrace input).extractionStats.literalVisits =
        input + 5 :=
  distinctGrowingDiscovery_extraction_stats input

/-- The retained trace contains every rejected decoy and the successful head. -/
theorem operationalDiscoveryTrace_attemptedCandidates
    (input : Nat) :
    (operationalDiscoveryTrace input).attemptTrace.map
        InstrumentedCandidateAttemptRecord.candidate =
      distinctDecoyVariables (input + 1) ++
        [growingDiscoverySplitVar input] := by
  rcases distinctGrowingDiscovery_found_after_exact_attempts input with
    ⟨_discovery, _found, _selected, attempts⟩
  unfold
    operationalDiscoveryTrace
    operationalInstrumentedDiscoveryRun
    retainDiscoveryTrace
  rw [runInstrumentedEndogenousDiscovery_attemptedCandidates]
  change
    (extractStructuralCandidates
        (distinctGrowingDiscoveryRoot input)).take
          ((runEndogenousFlipDiscovery
            (distinctGrowingDiscoveryRoot input)).outcome.attempts) =
      distinctDecoyVariables (input + 1) ++
        [growingDiscoverySplitVar input]
  rw [
    distinctGrowingDiscovery_candidates,
    attempts
  ]
  have attemptLengthExact :
      input + 2 =
        (distinctDecoyVariables (input + 1)).length + 1 := by
    rw [distinctDecoyVariables_length]
  rw [attemptLengthExact]
  exact
    take_append_head
      (distinctDecoyVariables (input + 1))
      (growingDiscoverySplitVar input)
      [growingDiscoveryAnchorVar input,
        growingDiscoverySplitVar input,
        growingDiscoveryAnchorVar input]

theorem operationalDiscoveryTrace_relationStats_exact
    (input : Nat) :
    (operationalDiscoveryTrace input).relationStats =
      aggregateInstrumentedAttemptStats
        (operationalDiscoveryTrace input).attemptTrace :=
  rfl

/-- The two same-input organizations differ only in retained provenance. -/
inductive OperationalOrganization where
  | reconstructible
  | provenanceMismatch
  deriving DecidableEq, Repr

def operationalTarget
    (input : Nat) :
    OperationalOrganization ->
      GeneratedStructuralBranchContext
        (distinctGrowingDiscoveryFormula input)
  | .reconstructible => operationalPositiveTarget input
  | .provenanceMismatch => operationalNegativeTarget input

/--
A schedule contains the exact trace that produced its selected variable.
Neither a variable nor a target endpoint can be passed separately to the
official producer below.
-/
structure OperationalDiscoverySchedule (input : Nat) where
  discoveryRun :
    InstrumentedEndogenousDiscoveryRun
      (distinctGrowingDiscoveryRoot input)
  discovered :
    EndogenousFlipDiscovery (distinctGrowingDiscoveryRoot input)
  discoveredFromRun :
    discoveryRun.outcome.discovered? = some discovered
  organization : OperationalOrganization

/-- Discovery output is the sole entry point to schedule production. -/
def scheduleOperationalFromDiscovery
    (input : Nat)
    (organization : OperationalOrganization) :
    Option (OperationalDiscoverySchedule input) :=
  let discoveryRun := operationalInstrumentedDiscoveryRun input
  match discoveredExact : discoveryRun.outcome.discovered? with
  | none => none
  | some discovered =>
      some
        { discoveryRun := discoveryRun
          discovered := discovered
          discoveredFromRun := discoveredExact
          organization := organization }

/-- Validation is indexed by the schedule it consumed. -/
structure OperationalValidationRun
    {input : Nat}
    (schedule : OperationalDiscoverySchedule input) where
  search :
    InstrumentedFlipSearchRun
      schedule.discovered.var
      (operationalSource input)
      (operationalTarget input schedule.organization)

def validateOperationalSchedule
    {input : Nat}
    (schedule : OperationalDiscoverySchedule input) :
    OperationalValidationRun schedule :=
  { search :=
      runInstrumentedFlipSearch
        schedule.discovered.var
        (operationalSource input)
        (operationalTarget input schedule.organization) }

/--
Execution consumes the exact validation run indexed by its schedule.  It does
not receive the input target, relation, or expected result as a free argument.
-/
def executeOperationalSchedule
    {input : Nat}
    (schedule : OperationalDiscoverySchedule input)
    (validation : OperationalValidationRun schedule) :
    OperationalTransportRun :=
  executeInstrumentedSearchResult
    schedule.discovered.var
    schedule.discovered.var
    (operationalSource input)
    (operationalTarget input schedule.organization)
    (operationalSourceContinuation input)
    validation.search

/-- Zero work is recorded when discovery returns no executable candidate. -/
def emptyInstrumentedFlipSearchStats : InstrumentedFlipSearchStats :=
  { formulaTransformClauseVisits := 0
    formulaTransformLiteralVisits := 0
    formulaComparisonClauseVisits := 0
    formulaComparisonLiteralVisits := 0
    historyTransformDecisionVisits := 0
    historyComparisonDecisionVisits := 0
    variableConstructorVisits := 0 }

/-- Complete causal output: discovery trace followed by operational execution. -/
structure IntegratedOperationalRun where
  discovery : RetainedDiscoveryTrace
  execution : OperationalTransportRun
  deriving DecidableEq, Repr

/--
The selected variable is read only from the retained discovery trace.  A
missing discovery cannot enter transport search, code production, or code
evaluation.
-/
def runIntegratedOperational
    (input : Nat)
    (organization : OperationalOrganization) : IntegratedOperationalRun :=
  let discoveryRun := operationalInstrumentedDiscoveryRun input
  let discoveryTrace := retainDiscoveryTrace discoveryRun
  match discoveredExact : discoveryRun.outcome.discovered? with
  | none =>
      { discovery := discoveryTrace
        execution :=
          { terminalBit := none
            codeAtoms := 0
            terminalReadouts := 0
            stats := emptyInstrumentedFlipSearchStats } }
  | some discovered =>
      let schedule : OperationalDiscoverySchedule input :=
        { discoveryRun := discoveryRun
          discovered := discovered
          discoveredFromRun := discoveredExact
          organization := organization }
      let validation := validateOperationalSchedule schedule
      { discovery := discoveryTrace
        execution :=
          executeOperationalSchedule schedule validation }

/-- The discovery-fed positive organization executes to `true`. -/
theorem runIntegratedOperational_reconstructible
    (input : Nat) :
    (runIntegratedOperational
      input
      .reconstructible).execution.terminalBit = some true := by
  unfold runIntegratedOperational
  simp only
  split
  · rename_i missing
    rcases operationalInstrumentedDiscoveryRun_found input with
      ⟨_discovery, found, _selected⟩
    rw [missing] at found
    cases found
  · rename_i discovered discoveredExact
    have selectedExact :=
      operationalInstrumentedDiscovery_selected_of_found
        input discovered discoveredExact
    simp only [
      operationalTarget,
      validateOperationalSchedule,
      executeOperationalSchedule,
      executeInstrumentedTransport
    ]
    rw [selectedExact]
    simpa only [
      operationalPositiveRun,
      executeInstrumentedTransport
    ] using operationalPositiveRun_terminal input

/-- The same pipeline rejects only the deeply mismatched provenance. -/
theorem runIntegratedOperational_provenanceMismatch
    (input : Nat) :
    (runIntegratedOperational
      input
      .provenanceMismatch).execution.terminalBit = none := by
  unfold runIntegratedOperational
  simp only
  split
  · rfl
  · rename_i discovered discoveredExact
    have selectedExact :=
      operationalInstrumentedDiscovery_selected_of_found
        input discovered discoveredExact
    simp only [
      operationalTarget,
      validateOperationalSchedule,
      executeOperationalSchedule,
      executeInstrumentedTransport
    ]
    rw [selectedExact]
    simpa only [
      operationalNegativeRun,
      executeInstrumentedTransport
    ] using operationalNegativeRun_terminal input

/-- The discovery work is retained unchanged by either downstream outcome. -/
theorem runIntegratedOperational_discovery
    (input : Nat)
    (organization : OperationalOrganization) :
    (runIntegratedOperational input organization).discovery =
      operationalDiscoveryTrace input := by
  unfold runIntegratedOperational operationalDiscoveryTrace
  simp only
  split <;> rfl

/-- The complete phase chain produces exactly the organization-specific run. -/
theorem runIntegratedOperational_execution
    (input : Nat)
    (organization : OperationalOrganization) :
    (runIntegratedOperational input organization).execution =
      match organization with
      | .reconstructible => operationalPositiveRun input
      | .provenanceMismatch => operationalNegativeRun input := by
  unfold runIntegratedOperational
  simp only
  split
  · rename_i missing
    rcases operationalInstrumentedDiscoveryRun_found input with
      ⟨_discovery, found, _selected⟩
    rw [missing] at found
    cases found
  · rename_i discovered discoveredExact
    have selectedExact :=
      operationalInstrumentedDiscovery_selected_of_found
        input discovered discoveredExact
    simp only [
      operationalTarget,
      validateOperationalSchedule,
      executeOperationalSchedule,
      executeInstrumentedTransport
    ]
    rw [selectedExact]
    cases organization <;> rfl

theorem runIntegratedOperational_reconstructible_codeAtoms
    (input : Nat) :
    (runIntegratedOperational
      input
      .reconstructible).execution.codeAtoms = 1 := by
  rw [runIntegratedOperational_execution]
  exact operationalPositiveRun_codeAtoms input

theorem runIntegratedOperational_provenanceMismatch_codeAtoms
    (input : Nat) :
    (runIntegratedOperational
      input
      .provenanceMismatch).execution.codeAtoms = 0 := by
  rw [runIntegratedOperational_execution]
  exact operationalNegativeRun_codeAtoms input

theorem runIntegratedOperational_reconstructible_terminalReadouts
    (input : Nat) :
    (runIntegratedOperational
      input
      .reconstructible).execution.terminalReadouts = 1 := by
  rw [runIntegratedOperational_execution]
  exact operationalPositiveRun_terminalReadouts input

theorem runIntegratedOperational_provenanceMismatch_terminalReadouts
    (input : Nat) :
    (runIntegratedOperational
      input
      .provenanceMismatch).execution.terminalReadouts = 0 := by
  rw [runIntegratedOperational_execution]
  exact operationalNegativeRun_terminalReadouts input

theorem runIntegratedOperational_reconstructible_historyVisits
    (input : Nat) :
    (runIntegratedOperational
      input
      .reconstructible).execution.stats.historyComparisonDecisionVisits =
        input + 2 := by
  rw [runIntegratedOperational_execution]
  exact operationalPositiveRun_historyComparisonDecisionVisits input

theorem runIntegratedOperational_provenanceMismatch_historyVisits
    (input : Nat) :
    (runIntegratedOperational
      input
      .provenanceMismatch).execution.stats.historyComparisonDecisionVisits =
        input + 2 := by
  rw [runIntegratedOperational_execution]
  exact operationalNegativeRun_historyComparisonDecisionVisits input

/-- The trace type genuinely carries data; it is not a proof subsingleton. -/
def emptyRetainedDiscoveryTrace : RetainedDiscoveryTrace :=
  { candidates := []
    extractionStats := { clauseVisits := 0, literalVisits := 0 }
    attemptTrace := []
    relationStats := zeroInstrumentedFlipSearchStats
    selected? := none }

def selectedRetainedDiscoveryTrace : RetainedDiscoveryTrace :=
  { candidates := [0]
    extractionStats := { clauseVisits := 1, literalVisits := 1 }
    attemptTrace :=
      [{ candidate := 0
         succeeded := true
         stats := zeroInstrumentedFlipSearchStats }]
    relationStats := zeroInstrumentedFlipSearchStats
    selected? := some 0 }

theorem retainedDiscoveryTrace_not_subsingleton :
    ¬ Subsingleton RetainedDiscoveryTrace := by
  intro subsingleton
  have same :
      emptyRetainedDiscoveryTrace = selectedRetainedDiscoveryTrace :=
    subsingleton.elim _ _
  have selectedSame := congrArg RetainedDiscoveryTrace.selected? same
  cases selectedSame

/--
Public experiment entry point.  Its only argument is the input index; variables,
endpoints, relations, codes, and terminal values remain internal products of
the two executions.
-/
structure OperationalProjectionExperimentRun where
  reconstructible : IntegratedOperationalRun
  provenanceMismatch : IntegratedOperationalRun
  deriving DecidableEq, Repr

def runOperationalProjectionExperiment
    (input : Nat) : OperationalProjectionExperimentRun :=
  { reconstructible :=
      runIntegratedOperational input .reconstructible
    provenanceMismatch :=
      runIntegratedOperational input .provenanceMismatch }

theorem runOperationalProjectionExperiment_outputs
    (input : Nat) :
    (runOperationalProjectionExperiment
        input).reconstructible.execution.terminalBit = some true /\
      (runOperationalProjectionExperiment
        input).provenanceMismatch.execution.terminalBit = none :=
  ⟨runIntegratedOperational_reconstructible input,
    runIntegratedOperational_provenanceMismatch input⟩

/-- Canonical accounting projected only from the actual integrated run. -/
structure IntegratedOperationalStats where
  extractionClauseVisits : Nat
  extractionLiteralVisits : Nat
  discoveryAttempts : Nat
  discoveryRelationStats : InstrumentedFlipSearchStats
  formulaTransformClauseVisits : Nat
  formulaTransformLiteralVisits : Nat
  formulaComparisonClauseVisits : Nat
  formulaComparisonLiteralVisits : Nat
  historyTransformDecisionVisits : Nat
  historyComparisonDecisionVisits : Nat
  variableConstructorVisits : Nat
  codeAtoms : Nat
  terminalReadouts : Nat
  deriving DecidableEq, Repr

def IntegratedOperationalStats.total
    (stats : IntegratedOperationalStats) : Nat :=
  stats.extractionClauseVisits +
    stats.extractionLiteralVisits +
    stats.discoveryAttempts +
    stats.discoveryRelationStats.total +
    stats.formulaTransformClauseVisits +
    stats.formulaTransformLiteralVisits +
    stats.formulaComparisonClauseVisits +
    stats.formulaComparisonLiteralVisits +
    stats.historyTransformDecisionVisits +
    stats.historyComparisonDecisionVisits +
    stats.variableConstructorVisits +
    stats.codeAtoms +
    stats.terminalReadouts

def integratedOperationalStats
    (input : Nat)
    (organization : OperationalOrganization) : IntegratedOperationalStats :=
  let run := runIntegratedOperational input organization
  { extractionClauseVisits := run.discovery.extractionStats.clauseVisits
    extractionLiteralVisits := run.discovery.extractionStats.literalVisits
    discoveryAttempts := run.discovery.attempts
    discoveryRelationStats := run.discovery.relationStats
    formulaTransformClauseVisits :=
      run.execution.stats.formulaTransformClauseVisits
    formulaTransformLiteralVisits :=
      run.execution.stats.formulaTransformLiteralVisits
    formulaComparisonClauseVisits :=
      run.execution.stats.formulaComparisonClauseVisits
    formulaComparisonLiteralVisits :=
      run.execution.stats.formulaComparisonLiteralVisits
    historyTransformDecisionVisits :=
      run.execution.stats.historyTransformDecisionVisits
    historyComparisonDecisionVisits :=
      run.execution.stats.historyComparisonDecisionVisits
    variableConstructorVisits :=
      run.execution.stats.variableConstructorVisits
    codeAtoms := run.execution.codeAtoms
    terminalReadouts := run.execution.terminalReadouts }

theorem integratedOperationalStats_discoveryAttempts
    (input : Nat)
    (organization : OperationalOrganization) :
    (integratedOperationalStats input organization).discoveryAttempts =
      input + 2 := by
  unfold integratedOperationalStats
  simp only
  rw [runIntegratedOperational_discovery]
  exact operationalDiscoveryTrace_attempts input

theorem integratedOperationalStats_extractionLiteralVisits
    (input : Nat)
    (organization : OperationalOrganization) :
    (integratedOperationalStats
      input
      organization).extractionLiteralVisits = input + 5 := by
  unfold integratedOperationalStats
  simp only
  rw [runIntegratedOperational_discovery]
  exact (operationalDiscoveryTrace_extraction input).2

theorem integratedOperationalStats_reconstructible_terminalReadouts
    (input : Nat) :
    (integratedOperationalStats
      input
      .reconstructible).terminalReadouts = 1 := by
  unfold integratedOperationalStats
  simp only
  rw [runIntegratedOperational_execution]
  exact operationalPositiveRun_terminalReadouts input

theorem integratedOperationalStats_provenanceMismatch_terminalReadouts
    (input : Nat) :
    (integratedOperationalStats
      input
      .provenanceMismatch).terminalReadouts = 0 := by
  unfold integratedOperationalStats
  simp only
  rw [runIntegratedOperational_execution]
  exact operationalNegativeRun_terminalReadouts input

/-! ## Input-aware projection and constructive non-factorization -/

/-- One member of the same-input two-organization family. -/
structure OperationalInstance where
  input : Nat
  organization : OperationalOrganization
  deriving DecidableEq, Repr

/--
An intentionally strong extensional snapshot.  Unlike the withdrawn
output-only projection it retains the input, complete root/source/target CNFs,
both depths, and the complete data-only discovery trace.  It erases only the
constituted decision histories.
-/
structure InputAwareExtensionalSnapshot where
  input : Nat
  rootFormula : Cnf
  sourceFormula : Cnf
  targetFormula : Cnf
  sourceDepth : Nat
  targetDepth : Nat
  discovery : RetainedDiscoveryTrace
  deriving DecidableEq

def inputAwareExtensionalProjection
    (caseValue : OperationalInstance) : InputAwareExtensionalSnapshot :=
  { input := caseValue.input
    rootFormula := distinctGrowingDiscoveryFormula caseValue.input
    sourceFormula := (operationalSource caseValue.input).context.formula
    targetFormula :=
      (operationalTarget
        caseValue.input
        caseValue.organization).context.formula
    sourceDepth := (operationalSource caseValue.input).depth
    targetDepth :=
      (operationalTarget caseValue.input caseValue.organization).depth
    discovery := operationalDiscoveryTrace caseValue.input }

/-- The observed value is produced by the integrated executable pipeline. -/
def operationalObservation
    (caseValue : OperationalInstance) : Option Bool :=
  (runIntegratedOperational
    caseValue.input
    caseValue.organization).execution.terminalBit

def reconstructibleInstance (input : Nat) : OperationalInstance :=
  { input := input
    organization := .reconstructible }

def provenanceMismatchInstance (input : Nat) : OperationalInstance :=
  { input := input
    organization := .provenanceMismatch }

/--
For every input, even the stronger input-aware snapshot identifies the two
organizations.  No disjoint-instance argument is involved.
-/
theorem operational_same_input_same_extensional_projection
    (input : Nat) :
    inputAwareExtensionalProjection (reconstructibleInstance input) =
      inputAwareExtensionalProjection (provenanceMismatchInstance input) := by
  unfold
    inputAwareExtensionalProjection
    reconstructibleInstance
    provenanceMismatchInstance
    operationalTarget
  rw [
    operationalTarget_formulas_same,
    operationalPositiveTarget_depth,
    operationalNegativeTarget_depth
  ]

/-- The executable continuation distinguishes those equal snapshots. -/
theorem operational_same_input_observations_different
    (input : Nat) :
    operationalObservation (reconstructibleInstance input) ≠
      operationalObservation (provenanceMismatchInstance input) := by
  change
    (runIntegratedOperational
      input
      .reconstructible).execution.terminalBit ≠
        (runIntegratedOperational
          input
          .provenanceMismatch).execution.terminalBit
  rw [
    runIntegratedOperational_reconstructible,
    runIntegratedOperational_provenanceMismatch
  ]
  intro impossible
  cases impossible

/--
No function of the input-aware extensional snapshot can reproduce the
operational continuation result.  The witness pair exists at every input.
-/
theorem operationalObservation_not_factors_through_inputAwareProjection
    (input : Nat) :
    ¬ ValueFactorsThrough
        inputAwareExtensionalProjection
        operationalObservation :=
  value_not_factors_of_same_projection
    inputAwareExtensionalProjection
    operationalObservation
    (reconstructibleInstance input)
    (provenanceMismatchInstance input)
    (operational_same_input_same_extensional_projection input)
    (operational_same_input_observations_different input)

/-- Exact adequacy claim refuted here; it is not a P-versus-NP statement. -/
def InputAwareProjectionContextuallyAdequate : Prop :=
  ValueFactorsThrough
    inputAwareExtensionalProjection
    operationalObservation

theorem inputAwareProjection_not_contextually_adequate :
    ¬ InputAwareProjectionContextuallyAdequate := by
  exact operationalObservation_not_factors_through_inputAwareProjection 0

/-! ## Non-spectator growth certificates -/

theorem operationalDepth_strict
    (input : Nat) :
    (operationalSource input).depth <
      (operationalSource (input + 1)).depth := by
  rw [operationalSource_depth, operationalSource_depth]
  exact Nat.lt_succ_self (input + 2)

theorem operationalDiscoveryAttempts_strict
    (input : Nat) :
    (operationalDiscoveryTrace input).attempts <
      (operationalDiscoveryTrace (input + 1)).attempts := by
  rw [
    operationalDiscoveryTrace_attempts,
    operationalDiscoveryTrace_attempts
  ]
  exact Nat.lt_succ_self (input + 2)

theorem operationalExtractionLiteralVisits_strict
    (input : Nat) :
    (operationalDiscoveryTrace input).extractionStats.literalVisits <
      (operationalDiscoveryTrace (input + 1)).extractionStats.literalVisits := by
  rw [
    (operationalDiscoveryTrace_extraction input).2,
    (operationalDiscoveryTrace_extraction (input + 1)).2
  ]
  exact Nat.lt_succ_self (input + 5)

theorem operationalPositiveHistoryWork_strict
    (input : Nat) :
    (runIntegratedOperational
      input
      .reconstructible).execution.stats.historyComparisonDecisionVisits <
      (runIntegratedOperational
        (input + 1)
        .reconstructible).execution.stats.historyComparisonDecisionVisits := by
  rw [
    runIntegratedOperational_reconstructible_historyVisits,
    runIntegratedOperational_reconstructible_historyVisits
  ]
  exact Nat.lt_succ_self (input + 2)

theorem operationalNegativeHistoryWork_strict
    (input : Nat) :
    (runIntegratedOperational
      input
      .provenanceMismatch).execution.stats.historyComparisonDecisionVisits <
      (runIntegratedOperational
        (input + 1)
        .provenanceMismatch).execution.stats.historyComparisonDecisionVisits := by
  rw [
    runIntegratedOperational_provenanceMismatch_historyVisits,
    runIntegratedOperational_provenanceMismatch_historyVisits
  ]
  exact Nat.lt_succ_self (input + 2)

/--
Integrated readiness package.  It records construction and scope, not a global
closure marker: the theorem is exactly contextual inadequacy of the declared
input-aware projection for the declared operational continuation observation.
-/
structure OperationalProjectionInadequacyCertificate : Prop where
  constitutionsDiffer :
    forall input,
      (operationalPositiveTarget input).context.decisions ≠
        (operationalNegativeTarget input).context.decisions
  discoveryAttemptTraceExact :
    forall input,
      (operationalDiscoveryTrace input).attemptTrace.map
          InstrumentedCandidateAttemptRecord.candidate =
        distinctDecoyVariables (input + 1) ++
          [growingDiscoverySplitVar input]
  discoveryRelationAccountingExact :
    forall input,
      (operationalDiscoveryTrace input).relationStats =
        aggregateInstrumentedAttemptStats
          (operationalDiscoveryTrace input).attemptTrace
  everyRelationTestChargesItsSource :
    forall
      {rootFormula : Cnf}
      (selected : Var)
      (source target : GeneratedStructuralBranchContext rootFormula),
      (runInstrumentedFlipSearch
        selected source target).stats.formulaTransformLiteralVisits =
          Cnf.literalCount source.context.formula
  reconstructibleExecutionExact :
    forall input,
      (runIntegratedOperational
          input
          .reconstructible).execution.terminalBit = some true /\
        (runIntegratedOperational
          input
          .reconstructible).execution.codeAtoms = 1 /\
        (runIntegratedOperational
          input
          .reconstructible).execution.terminalReadouts = 1
  provenanceMismatchExecutionExact :
    forall input,
      (runIntegratedOperational
          input
          .provenanceMismatch).execution.terminalBit = none /\
        (runIntegratedOperational
          input
          .provenanceMismatch).execution.codeAtoms = 0 /\
        (runIntegratedOperational
          input
          .provenanceMismatch).execution.terminalReadouts = 0
  sameInputSeparation :
    forall input,
      inputAwareExtensionalProjection (reconstructibleInstance input) =
        inputAwareExtensionalProjection (provenanceMismatchInstance input) /\
      operationalObservation (reconstructibleInstance input) ≠
        operationalObservation (provenanceMismatchInstance input)
  noFactorization :
    ¬ InputAwareProjectionContextuallyAdequate
  depthGrows :
    forall input,
      (operationalSource input).depth <
        (operationalSource (input + 1)).depth
  discoveryWorkGrows :
    forall input,
      (operationalDiscoveryTrace input).attempts <
        (operationalDiscoveryTrace (input + 1)).attempts
  extractionWorkGrows :
    forall input,
      (operationalDiscoveryTrace input).extractionStats.literalVisits <
        (operationalDiscoveryTrace (input + 1)).extractionStats.literalVisits
  positiveHistoryWorkGrows :
    forall input,
      (runIntegratedOperational
        input
        .reconstructible).execution.stats.historyComparisonDecisionVisits <
        (runIntegratedOperational
          (input + 1)
          .reconstructible).execution.stats.historyComparisonDecisionVisits
  negativeHistoryWorkGrows :
    forall input,
      (runIntegratedOperational
        input
        .provenanceMismatch).execution.stats.historyComparisonDecisionVisits <
        (runIntegratedOperational
          (input + 1)
          .provenanceMismatch).execution.stats.historyComparisonDecisionVisits

theorem operationalProjectionInadequacyCertified :
    OperationalProjectionInadequacyCertificate :=
  { constitutionsDiffer := operationalTarget_constitutions_different
    discoveryAttemptTraceExact :=
      operationalDiscoveryTrace_attemptedCandidates
    discoveryRelationAccountingExact :=
      operationalDiscoveryTrace_relationStats_exact
    everyRelationTestChargesItsSource :=
      runInstrumentedFlipSearch_formulaTransformLiteralVisits
    reconstructibleExecutionExact := fun input =>
      ⟨runIntegratedOperational_reconstructible input,
        runIntegratedOperational_reconstructible_codeAtoms input,
        runIntegratedOperational_reconstructible_terminalReadouts input⟩
    provenanceMismatchExecutionExact := fun input =>
      ⟨runIntegratedOperational_provenanceMismatch input,
        runIntegratedOperational_provenanceMismatch_codeAtoms input,
        runIntegratedOperational_provenanceMismatch_terminalReadouts input⟩
    sameInputSeparation := fun input =>
      ⟨operational_same_input_same_extensional_projection input,
        operational_same_input_observations_different input⟩
    noFactorization := inputAwareProjection_not_contextually_adequate
    depthGrows := operationalDepth_strict
    discoveryWorkGrows := operationalDiscoveryAttempts_strict
    extractionWorkGrows := operationalExtractionLiteralVisits_strict
    positiveHistoryWorkGrows := operationalPositiveHistoryWork_strict
    negativeHistoryWorkGrows := operationalNegativeHistoryWork_strict }

/-- Review boundary for this scoped repair; deliberately not a closure status. -/
inductive OperationalProjectionRepairStatus where
  | readyForIndependentAdversarialAudit
  deriving DecidableEq, Repr

def operationalProjectionRepairStatus : OperationalProjectionRepairStatus :=
  .readyForIndependentAdversarialAudit

theorem operationalProjectionRepair_readyForIndependentAudit :
    operationalProjectionRepairStatus =
      .readyForIndependentAdversarialAudit :=
  rfl

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.runNatComparison_true_implies_equal
#print axioms ConstitutiveSearch.SAT.runNatComparison_equal_implies_true
#print axioms ConstitutiveSearch.SAT.runNatComparison_false_of_ne
#print axioms ConstitutiveSearch.SAT.runLiteralComparison_true_implies_equal
#print axioms ConstitutiveSearch.SAT.runLiteralComparison_equal_implies_true
#print axioms ConstitutiveSearch.SAT.runClauseComparison_true_implies_equal
#print axioms ConstitutiveSearch.SAT.runClauseComparison_equal_implies_true
#print axioms ConstitutiveSearch.SAT.runCnfComparison_true_implies_equal
#print axioms ConstitutiveSearch.SAT.runCnfComparison_false_of_ne
#print axioms ConstitutiveSearch.SAT.runCnfComparison_equal_implies_true
#print axioms ConstitutiveSearch.SAT.runLiteralFlip_output
#print axioms ConstitutiveSearch.SAT.runClauseFlip_output
#print axioms ConstitutiveSearch.SAT.runCnfFlip_output
#print axioms ConstitutiveSearch.SAT.runDecisionFlip_output
#print axioms ConstitutiveSearch.SAT.runDecisionHistoryFlip_output
#print axioms ConstitutiveSearch.SAT.instrumentedFormulaComparison
#print axioms ConstitutiveSearch.SAT.instrumentedHistoryComparison
#print axioms ConstitutiveSearch.SAT.runDecisionComparison_true_implies_equal
#print axioms ConstitutiveSearch.SAT.runDecisionComparison_equal_implies_true
#print axioms ConstitutiveSearch.SAT.runDecisionComparison_false_of_var_ne
#print axioms ConstitutiveSearch.SAT.runDecisionHistoryComparison_true_implies_equal
#print axioms ConstitutiveSearch.SAT.runDecisionHistoryComparison_equal_implies_true
#print axioms ConstitutiveSearch.SAT.runDecisionHistoryComparison_equal_decisionVisits
#print axioms ConstitutiveSearch.SAT.generateFalsePath
#print axioms ConstitutiveSearch.SAT.operationalCommonParentPath
#print axioms ConstitutiveSearch.SAT.operationalMismatchedParentPath
#print axioms ConstitutiveSearch.SAT.operationalSource_depth
#print axioms ConstitutiveSearch.SAT.operationalNegativeTarget_depth
#print axioms ConstitutiveSearch.SAT.operationalPositiveRelation
#print axioms ConstitutiveSearch.SAT.operationalNegative_decisions_mismatch
#print axioms ConstitutiveSearch.SAT.operationalTarget_constitutions_different
#print axioms ConstitutiveSearch.SAT.runCnfFlip_literalVisits
#print axioms ConstitutiveSearch.SAT.runCnfComparison_equal_literalVisits
#print axioms ConstitutiveSearch.SAT.runDecisionHistoryComparison_pathVariablesFrom_decisionVisits
#print axioms ConstitutiveSearch.SAT.runInstrumentedFlipSearch
#print axioms ConstitutiveSearch.SAT.runInstrumentedFlipSearch_relation_exact
#print axioms ConstitutiveSearch.SAT.runInstrumentedFlipSearch_formulaTransformLiteralVisits
#print axioms ConstitutiveSearch.SAT.runInstrumentedFlipSearch_found_of_relation
#print axioms ConstitutiveSearch.SAT.runInstrumentedFlipSearch_none_of_history_mismatch
#print axioms ConstitutiveSearch.SAT.InstrumentedCandidateAttempt
#print axioms ConstitutiveSearch.SAT.runInstrumentedCandidateAttempt
#print axioms ConstitutiveSearch.SAT.InstrumentedCandidateAttemptRecord
#print axioms ConstitutiveSearch.SAT.exploreInstrumentedCandidates
#print axioms ConstitutiveSearch.SAT.runInstrumentedEndogenousDiscovery
#print axioms ConstitutiveSearch.SAT.runInstrumentedCandidateAttempt_discovery_exact
#print axioms ConstitutiveSearch.SAT.exploreInstrumentedCandidates_discovered_exact
#print axioms ConstitutiveSearch.SAT.exploreInstrumentedCandidates_attemptTrace_length
#print axioms ConstitutiveSearch.SAT.exploreInstrumentedCandidates_attemptedCandidates
#print axioms ConstitutiveSearch.SAT.runInstrumentedEndogenousDiscovery_discovered_exact
#print axioms ConstitutiveSearch.SAT.runInstrumentedEndogenousDiscovery_attemptTrace_length
#print axioms ConstitutiveSearch.SAT.runInstrumentedEndogenousDiscovery_attemptedCandidates
#print axioms ConstitutiveSearch.SAT.operationalSourceContinuation
#print axioms ConstitutiveSearch.SAT.executeInstrumentedSearchResult
#print axioms ConstitutiveSearch.SAT.executeInstrumentedSearchResult_success_exact
#print axioms ConstitutiveSearch.SAT.operationalPositiveRun_terminal
#print axioms ConstitutiveSearch.SAT.operationalNegativeRun_terminal
#print axioms ConstitutiveSearch.SAT.operationalPositiveRun_terminalReadouts
#print axioms ConstitutiveSearch.SAT.operationalNegativeRun_terminalReadouts
#print axioms ConstitutiveSearch.SAT.operationalPositiveRun_historyComparisonDecisionVisits
#print axioms ConstitutiveSearch.SAT.operationalNegativeRun_historyComparisonDecisionVisits
#print axioms ConstitutiveSearch.SAT.retainDiscoveryTrace
#print axioms ConstitutiveSearch.SAT.operationalInstrumentedDiscoveryRun
#print axioms ConstitutiveSearch.SAT.operationalInstrumentedDiscoveryRun_found
#print axioms ConstitutiveSearch.SAT.operationalDiscoveryTrace_selected
#print axioms ConstitutiveSearch.SAT.operationalInstrumentedDiscovery_selected_of_found
#print axioms ConstitutiveSearch.SAT.operationalDiscoveryTrace_attempts
#print axioms ConstitutiveSearch.SAT.operationalDiscoveryTrace_extraction
#print axioms ConstitutiveSearch.SAT.operationalDiscoveryTrace_attemptedCandidates
#print axioms ConstitutiveSearch.SAT.operationalDiscoveryTrace_relationStats_exact
#print axioms ConstitutiveSearch.SAT.OperationalDiscoverySchedule
#print axioms ConstitutiveSearch.SAT.scheduleOperationalFromDiscovery
#print axioms ConstitutiveSearch.SAT.OperationalValidationRun
#print axioms ConstitutiveSearch.SAT.validateOperationalSchedule
#print axioms ConstitutiveSearch.SAT.executeOperationalSchedule
#print axioms ConstitutiveSearch.SAT.runIntegratedOperational
#print axioms ConstitutiveSearch.SAT.runIntegratedOperational_execution
#print axioms ConstitutiveSearch.SAT.runIntegratedOperational_reconstructible
#print axioms ConstitutiveSearch.SAT.runIntegratedOperational_provenanceMismatch
#print axioms ConstitutiveSearch.SAT.runIntegratedOperational_reconstructible_codeAtoms
#print axioms ConstitutiveSearch.SAT.runIntegratedOperational_provenanceMismatch_codeAtoms
#print axioms ConstitutiveSearch.SAT.runIntegratedOperational_reconstructible_terminalReadouts
#print axioms ConstitutiveSearch.SAT.runIntegratedOperational_provenanceMismatch_terminalReadouts
#print axioms ConstitutiveSearch.SAT.retainedDiscoveryTrace_not_subsingleton
#print axioms ConstitutiveSearch.SAT.OperationalProjectionExperimentRun
#print axioms ConstitutiveSearch.SAT.runOperationalProjectionExperiment
#print axioms ConstitutiveSearch.SAT.runOperationalProjectionExperiment_outputs
#print axioms ConstitutiveSearch.SAT.IntegratedOperationalStats
#print axioms ConstitutiveSearch.SAT.IntegratedOperationalStats.total
#print axioms ConstitutiveSearch.SAT.integratedOperationalStats
#print axioms ConstitutiveSearch.SAT.integratedOperationalStats_discoveryAttempts
#print axioms ConstitutiveSearch.SAT.integratedOperationalStats_extractionLiteralVisits
#print axioms ConstitutiveSearch.SAT.integratedOperationalStats_reconstructible_terminalReadouts
#print axioms ConstitutiveSearch.SAT.integratedOperationalStats_provenanceMismatch_terminalReadouts
#print axioms ConstitutiveSearch.SAT.inputAwareExtensionalProjection
#print axioms ConstitutiveSearch.SAT.operational_same_input_same_extensional_projection
#print axioms ConstitutiveSearch.SAT.operational_same_input_observations_different
#print axioms ConstitutiveSearch.SAT.operationalObservation_not_factors_through_inputAwareProjection
#print axioms ConstitutiveSearch.SAT.inputAwareProjection_not_contextually_adequate
#print axioms ConstitutiveSearch.SAT.operationalDepth_strict
#print axioms ConstitutiveSearch.SAT.operationalDiscoveryAttempts_strict
#print axioms ConstitutiveSearch.SAT.operationalExtractionLiteralVisits_strict
#print axioms ConstitutiveSearch.SAT.operationalPositiveHistoryWork_strict
#print axioms ConstitutiveSearch.SAT.operationalNegativeHistoryWork_strict
#print axioms ConstitutiveSearch.SAT.OperationalProjectionInadequacyCertificate
#print axioms ConstitutiveSearch.SAT.operationalProjectionInadequacyCertified
#print axioms ConstitutiveSearch.SAT.OperationalProjectionRepairStatus
#print axioms ConstitutiveSearch.SAT.operationalProjectionRepair_readyForIndependentAudit
/- AXIOM_AUDIT_END -/
