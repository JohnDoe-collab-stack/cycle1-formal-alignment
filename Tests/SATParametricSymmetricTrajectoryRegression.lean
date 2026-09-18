import ConstitutiveSearch.SAT.ParametricSymmetricTrajectory

namespace ConstitutiveSearch.Tests.SATParametricSymmetricTrajectoryRegression

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

theorem rootFlipSymmetric :
    FlipSymmetricAt root.context.formula 0 := by
  rfl

abbrev firstTrue :
    GeneratedStructuralBranchContext formula :=
  GeneratedStructuralBranchContext.child
    root
    0
    true
    rootVar0Fresh

theorem firstTrueVar1Fresh :
    StructuralDecisionsAvoid
      1
      firstTrue.context.decisions := by
  constructor
  · decide
  · exact True.intro

theorem firstTrueFlipSymmetric :
    FlipSymmetricAt firstTrue.context.formula 1 := by
  rfl

abbrev secondTrue :
    GeneratedStructuralBranchContext formula :=
  GeneratedStructuralBranchContext.child
    firstTrue
    1
    true
    firstTrueVar1Fresh

def secondLevel :
    FlipSymmetricTrajectory
      firstTrue
      secondTrue
      1 :=
  .step
    1
    firstTrueVar1Fresh
    firstTrueFlipSymmetric
    (.done secondTrue)

def twoLevel :
    FlipSymmetricTrajectory
      root
      secondTrue
      2 :=
  .step
    0
    rootVar0Fresh
    rootFlipSymmetric
    secondLevel

theorem twoLevel_widthTrace :
    twoLevel.widthTrace =
      [1, 2, 1, 2, 1] := by
  rfl

theorem twoLevel_width_bound :
    ∀ width : Nat,
      width ∈ twoLevel.widthTrace →
        width ≤ 2 := by
  intro width member
  exact twoLevel.width_le_two width member

theorem twoLevel_attains_two :
    2 ∈ twoLevel.widthTrace := by
  rfl

def allTrue : Assignment :=
  fun _ => true

theorem allTrueSatisfies :
    Satisfies allTrue formula :=
  .cons rfl
    (.cons rfl
      (.cons rfl
        (.cons rfl .nil)))

def rootContinuation :
    GeneratedStructuralBranchContinuation root :=
  ⟨allTrue, True.intro⟩

theorem rootContinuation_accept :
    GeneratedStructuralBranchAccept
      root
      rootContinuation :=
  allTrueSatisfies

theorem initial_viable :
    FrontierViable
      (generatedStructuralBranchSystem formula)
      [root] := by
  exact
    ⟨.head rootContinuation,
      rootContinuation_accept⟩

theorem endpoint_viable_iff :
    FrontierViable
        (generatedStructuralBranchSystem formula)
        [root] ↔
      FrontierViable
        (generatedStructuralBranchSystem formula)
        [secondTrue] :=
  twoLevel.viable_iff

theorem final_viable :
    FrontierViable
      (generatedStructuralBranchSystem formula)
      [secondTrue] :=
  endpoint_viable_iff.mp initial_viable

end ConstitutiveSearch.Tests.SATParametricSymmetricTrajectoryRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricTrajectoryRegression.rootFlipSymmetric
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricTrajectoryRegression.firstTrueFlipSymmetric
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricTrajectoryRegression.secondLevel
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricTrajectoryRegression.twoLevel
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricTrajectoryRegression.twoLevel_widthTrace
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricTrajectoryRegression.twoLevel_width_bound
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricTrajectoryRegression.twoLevel_attains_two
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricTrajectoryRegression.rootContinuation
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricTrajectoryRegression.rootContinuation_accept
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricTrajectoryRegression.initial_viable
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricTrajectoryRegression.endpoint_viable_iff
#print axioms ConstitutiveSearch.Tests.SATParametricSymmetricTrajectoryRegression.final_viable
/- AXIOM_AUDIT_END -/
