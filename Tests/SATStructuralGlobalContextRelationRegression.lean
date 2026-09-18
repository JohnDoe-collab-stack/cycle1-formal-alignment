import ConstitutiveSearch.SAT.StructuralGlobalContextRelation

namespace ConstitutiveSearch.Tests.SATStructuralGlobalContextRelationRegression

open ConstitutiveSearch
open SAT

abbrev c0p : Clause :=
  [Literal.positive 0, Literal.positive 2]

abbrev c0n : Clause :=
  [Literal.negative 0, Literal.positive 2]

abbrev c1p : Clause :=
  [Literal.positive 1, Literal.positive 2]

abbrev c1n : Clause :=
  [Literal.negative 1, Literal.positive 2]

abbrev formula : Cnf :=
  [c0p, c0n, c1p, c1n]

abbrev root :
    GeneratedStructuralBranchContext formula :=
  GeneratedStructuralBranchContext.root formula

theorem rootVar0Fresh :
    StructuralDecisionsAvoid
      0
      root.context.decisions :=
  True.intro

abbrev falseParent :
    GeneratedStructuralBranchContext formula :=
  GeneratedStructuralBranchContext.child
    root 0 false rootVar0Fresh

abbrev trueParent :
    GeneratedStructuralBranchContext formula :=
  GeneratedStructuralBranchContext.child
    root 0 true rootVar0Fresh

theorem parent_histories_differ :
    falseParent.context.decisions ≠
      trueParent.context.decisions := by
  decide

theorem falseParentVar1Fresh :
    StructuralDecisionsAvoid
      1
      falseParent.context.decisions := by
  constructor
  · decide
  · exact True.intro

theorem trueParentVar1Fresh :
    StructuralDecisionsAvoid
      1
      trueParent.context.decisions := by
  constructor
  · decide
  · exact True.intro

/-- Deep source and target have different immediate parents. -/
abbrev source :
    GeneratedStructuralBranchContext formula :=
  GeneratedStructuralBranchContext.child
    falseParent 1 true falseParentVar1Fresh

abbrev target :
    GeneratedStructuralBranchContext formula :=
  GeneratedStructuralBranchContext.child
    trueParent 1 true trueParentVar1Fresh

theorem formulas_flip_exact :
    target.context.formula =
      Cnf.flipAt 0 source.context.formula := by
  rfl

theorem histories_flip_exact :
    target.context.decisions =
      flipStructuralDecisionsAt
        0
        source.context.decisions := by
  rfl

def sourceToTarget :
    GeneratedStructuralFlipAtRelation
      0
      source
      target :=
  { formulaExact := formulas_flip_exact
    decisionsExact := histories_flip_exact }

/-- Source assignment realizes x0=false and x1=true. -/
def sourceAssignment : Assignment
  | 0 => false
  | _ => true

theorem sourceRootSatisfies :
    Satisfies sourceAssignment formula :=
  .cons rfl
    (.cons rfl
      (.cons rfl
        (.cons rfl .nil)))

theorem sourceFalseParentSatisfies :
    Satisfies
      sourceAssignment
      falseParent.context.formula :=
  (branchWeakening formula 0 false).preservesSatisfaction
    sourceRootSatisfies

theorem sourceResidualSatisfies :
    Satisfies
      sourceAssignment
      source.context.formula :=
  (branchWeakening
      falseParent.context.formula
      1
      true).preservesSatisfaction
    sourceFalseParentSatisfies

def sourceContinuation :
    GeneratedStructuralBranchContinuation source :=
  ⟨sourceAssignment,
    ⟨rfl, ⟨rfl, True.intro⟩⟩⟩

theorem sourceContinuation_accept :
    GeneratedStructuralBranchAccept
      source
      sourceContinuation :=
  sourceResidualSatisfies

/-- Total structural transport is available independently of acceptance. -/
def targetContinuation :
    GeneratedStructuralBranchContinuation target :=
  sourceToTarget.mapContinuation sourceContinuation

theorem targetContinuation_accept :
    GeneratedStructuralBranchAccept
      target
      targetContinuation :=
  sourceToTarget.mapContinuation_accept
    sourceContinuation
    sourceContinuation_accept

theorem target_x0_true :
    targetContinuation.1 0 = true := by
  change
    (sourceToTarget.mapContinuation sourceContinuation).1 0 =
      true
  rw [GeneratedStructuralFlipAtRelation.mapContinuation_assignment]
  rw [Assignment.flipAt_selected]
  rfl

theorem target_x1_true :
    targetContinuation.1 1 = true := by
  change
    (sourceToTarget.mapContinuation sourceContinuation).1 1 =
      true
  rw [GeneratedStructuralFlipAtRelation.mapContinuation_assignment]
  rw [Assignment.flipAt_other 0 1]
  · rfl
  · decide

theorem global_search_found :
    (generatedStructuralFlipAtSearch formula 0).find
        source
        target ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

def heterogeneousPair :
    List (GeneratedStructuralBranchContext formula) :=
  [source, target]

def reducedHeterogeneousPair :=
  normalizeGeneratedStructuralFrontierByFlip
    formula
    0
    heterogeneousPair

theorem heterogeneous_width_one :
    reducedHeterogeneousPair.width = 1 := by
  rfl

theorem heterogeneous_viable_iff :
    FrontierViable
        (generatedStructuralBranchSystem formula)
        heterogeneousPair ↔
      FrontierViable
        (generatedStructuralBranchSystem formula)
        reducedHeterogeneousPair.retained :=
  reducedHeterogeneousPair.viable_iff

theorem heterogeneous_source_viable :
    FrontierViable
      (generatedStructuralBranchSystem formula)
      heterogeneousPair := by
  exact
    ⟨.head sourceContinuation,
      sourceContinuation_accept⟩

theorem heterogeneous_retained_viable :
    FrontierViable
      (generatedStructuralBranchSystem formula)
      reducedHeterogeneousPair.retained :=
  heterogeneous_viable_iff.mp heterogeneous_source_viable

end ConstitutiveSearch.Tests.SATStructuralGlobalContextRelationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATStructuralGlobalContextRelationRegression.parent_histories_differ
#print axioms ConstitutiveSearch.Tests.SATStructuralGlobalContextRelationRegression.formulas_flip_exact
#print axioms ConstitutiveSearch.Tests.SATStructuralGlobalContextRelationRegression.histories_flip_exact
#print axioms ConstitutiveSearch.Tests.SATStructuralGlobalContextRelationRegression.sourceToTarget
#print axioms ConstitutiveSearch.Tests.SATStructuralGlobalContextRelationRegression.sourceRootSatisfies
#print axioms ConstitutiveSearch.Tests.SATStructuralGlobalContextRelationRegression.sourceResidualSatisfies
#print axioms ConstitutiveSearch.Tests.SATStructuralGlobalContextRelationRegression.sourceContinuation
#print axioms ConstitutiveSearch.Tests.SATStructuralGlobalContextRelationRegression.sourceContinuation_accept
#print axioms ConstitutiveSearch.Tests.SATStructuralGlobalContextRelationRegression.targetContinuation
#print axioms ConstitutiveSearch.Tests.SATStructuralGlobalContextRelationRegression.targetContinuation_accept
#print axioms ConstitutiveSearch.Tests.SATStructuralGlobalContextRelationRegression.target_x0_true
#print axioms ConstitutiveSearch.Tests.SATStructuralGlobalContextRelationRegression.target_x1_true
#print axioms ConstitutiveSearch.Tests.SATStructuralGlobalContextRelationRegression.global_search_found
#print axioms ConstitutiveSearch.Tests.SATStructuralGlobalContextRelationRegression.reducedHeterogeneousPair
#print axioms ConstitutiveSearch.Tests.SATStructuralGlobalContextRelationRegression.heterogeneous_viable_iff
#print axioms ConstitutiveSearch.Tests.SATStructuralGlobalContextRelationRegression.heterogeneous_retained_viable
/- AXIOM_AUDIT_END -/
