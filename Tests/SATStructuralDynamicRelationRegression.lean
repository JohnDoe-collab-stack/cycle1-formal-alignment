import ConstitutiveSearch.SAT.StructuralDynamicRelation

namespace ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression

open ConstitutiveSearch
open SAT

abbrev c0p : Clause :=
  [Literal.positive 0, Literal.positive 2]

abbrev c0n : Clause :=
  [Literal.negative 0, Literal.positive 2]

abbrev formula : Cnf :=
  [c0p, c0n]

abbrev root :
    GeneratedStructuralBranchContext formula :=
  GeneratedStructuralBranchContext.root formula

theorem rootVar0Fresh :
    StructuralDecisionsAvoid
      0
      root.context.decisions :=
  True.intro

def splitAnchor :
    GeneratedSplitAnchor formula :=
  { parent := root
    var := 0
    fresh := rootVar0Fresh }

abbrev falseChild :
    GeneratedStructuralBranchContext formula :=
  splitAnchor.falseChild

abbrev trueChild :
    GeneratedStructuralBranchContext formula :=
  splitAnchor.trueChild

theorem split_frontier_exact :
    splitAnchor.frontier =
      [falseChild, trueChild] := by
  rfl

abbrev Constitution :=
  GeneratedSplitConstitution formula

abbrev system :=
  generatedStructuralBranchSystem formula

/--
Before the split certificate is constituted, the generated children already
exist as the current frontier but the dynamic relation engine has no anchor.
-/
def state0 : ConstitutiveState system Constitution :=
  { frontier := [root]
    constitution := none }

def state1 : ConstitutiveState system Constitution :=
  { frontier := splitAnchor.frontier
    constitution := none }

/--
The frontier is unchanged; only the exact certificate of the split that created
it is now part of constituted state.
-/
def state2 : ConstitutiveState system Constitution :=
  { frontier := splitAnchor.frontier
    constitution := some splitAnchor }

theorem frontier_unchanged_when_anchor_constituted :
    state1.frontier = state2.frontier := by
  rfl

/-- The dynamic flip is absent before the certified split is constituted. -/
theorem relation_absent_before :
    (constitutedSplitFlipSearch formula).find
        state1
        falseChild
        trueChild = none := by
  rfl

/-- The same pair becomes related after constituting the actual split certificate. -/
theorem relation_present_after :
    (constitutedSplitFlipSearch formula).find
        state2
        falseChild
        trueChild ≠ none := by
  intro impossible
  change some _ = none at impossible
  cases impossible

def beforeReduction :=
  (constitutedSplitFlipSearch formula).normalizeAt
    (constitutedSplitFlipAction formula)
    state1
    state1.frontier

def afterReduction :=
  (constitutedSplitFlipSearch formula).normalizeAt
    (constitutedSplitFlipAction formula)
    state2
    state2.frontier

theorem width_before :
    beforeReduction.width = 2 := by
  rfl

theorem width_after :
    afterReduction.width = 1 := by
  rfl

theorem retained_after :
    afterReduction.retained = [trueChild] := by
  rfl

def state3 : ConstitutiveState system Constitution :=
  { frontier := afterReduction.retained
    constitution := some splitAnchor }

/--
This constitutive relation is tied to the exact split certificate used in this
trajectory.  No semantic SAT answer is stored in it.
-/
inductive PathConstitutes : Constitution → Constitution → Type where
  | expand : PathConstitutes none none
  | recordSplit : PathConstitutes none (some splitAnchor)
  | reduce : PathConstitutes (some splitAnchor) (some splitAnchor)

def expandStep :
    ConstitutiveStep
      system
      PathConstitutes
      state0
      state1 :=
  { preservation := splitAnchor.expansion
    constitutes := .expand }

def recordSplitStep :
    ConstitutiveStep
      system
      PathConstitutes
      state1
      state2 :=
  { preservation :=
      AcceptedFrontierPreservation.identity
        system
        splitAnchor.frontier
    constitutes := .recordSplit }

def reduceStep :
    ConstitutiveStep
      system
      PathConstitutes
      state2
      state3 :=
  { preservation := afterReduction.preservation
    constitutes := .reduce }

def trajectory01 :
    FrontierTrajectory
      system
      PathConstitutes
      state0
      state1 :=
  .snoc (.refl state0) expandStep

def trajectory02 :
    FrontierTrajectory
      system
      PathConstitutes
      state0
      state2 :=
  .snoc trajectory01 recordSplitStep

def fullTrajectory :
    FrontierTrajectory
      system
      PathConstitutes
      state0
      state3 :=
  .snoc trajectory02 reduceStep

theorem trajectory_length :
    fullTrajectory.length = 3 := by
  rfl

theorem trajectory_widthTrace :
    fullTrajectory.widthTrace = [1, 2, 2, 1] := by
  rfl

theorem trajectory_maxWidth :
    fullTrajectory.maxWidth = 2 := by
  rfl

/-- Concrete source assignment satisfying the root while realizing x0=false. -/
def sourceAssignment : Assignment
  | 0 => false
  | _ => true

theorem sourceRootSatisfies :
    Satisfies sourceAssignment formula :=
  .cons rfl
    (.cons rfl .nil)

theorem sourceFalseChildSatisfies :
    Satisfies
      sourceAssignment
      falseChild.context.formula :=
  (branchWeakening formula 0 false).preservesSatisfaction
    sourceRootSatisfies

def sourceContinuation :
    GeneratedStructuralBranchContinuation falseChild :=
  ⟨sourceAssignment, ⟨rfl, True.intro⟩⟩

theorem sourceContinuation_accept :
    GeneratedStructuralBranchAccept
      falseChild
      sourceContinuation :=
  sourceFalseChildSatisfies

theorem split_frontier_viable :
    FrontierViable system state1.frontier := by
  exact
    ⟨.head sourceContinuation,
      sourceContinuation_accept⟩

theorem anchor_constitution_preserves_viable :
    FrontierViable system state1.frontier ↔
      FrontierViable system state2.frontier :=
  recordSplitStep.viable_iff

theorem complete_trajectory_viable_iff :
    FrontierViable system state0.frontier ↔
      FrontierViable system state3.frontier :=
  fullTrajectory.viable_iff

theorem reduced_frontier_viable :
    FrontierViable system state3.frontier :=
  afterReduction.viable_iff.mp
    (anchor_constitution_preserves_viable.mp split_frontier_viable)

end ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.splitAnchor
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.split_frontier_exact
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.frontier_unchanged_when_anchor_constituted
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.relation_absent_before
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.relation_present_after
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.beforeReduction
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.afterReduction
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.width_before
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.width_after
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.retained_after
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.PathConstitutes
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.expandStep
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.recordSplitStep
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.reduceStep
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.fullTrajectory
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.trajectory_widthTrace
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.trajectory_maxWidth
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.sourceRootSatisfies
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.sourceContinuation
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.sourceContinuation_accept
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.complete_trajectory_viable_iff
#print axioms ConstitutiveSearch.Tests.SATStructuralDynamicRelationRegression.reduced_frontier_viable
/- AXIOM_AUDIT_END -/
