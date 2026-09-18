import ConstitutiveSearch.FrontierTrajectory
import ConstitutiveSearch.SAT.StructuralGlobalContextRelation

namespace ConstitutiveSearch.Tests.FrontierTrajectoryRegression

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

abbrev firstFalse :
    GeneratedStructuralBranchContext formula :=
  GeneratedStructuralBranchContext.child
    root 0 false rootVar0Fresh

abbrev firstTrue :
    GeneratedStructuralBranchContext formula :=
  GeneratedStructuralBranchContext.child
    root 0 true rootVar0Fresh

theorem firstTrueVar1Fresh :
    StructuralDecisionsAvoid
      1
      firstTrue.context.decisions := by
  constructor
  · decide
  · exact True.intro

abbrev secondFalse :
    GeneratedStructuralBranchContext formula :=
  GeneratedStructuralBranchContext.child
    firstTrue 1 false firstTrueVar1Fresh

abbrev secondTrue :
    GeneratedStructuralBranchContext formula :=
  GeneratedStructuralBranchContext.child
    firstTrue 1 true firstTrueVar1Fresh

def firstReduction :=
  normalizeGeneratedStructuralFrontierByFlip
    formula
    0
    [firstFalse, firstTrue]

theorem firstReduction_retained :
    firstReduction.retained = [firstTrue] := by
  rfl

def secondReduction :=
  normalizeGeneratedStructuralFrontierByFlip
    formula
    1
    [secondFalse, secondTrue]

theorem secondReduction_retained :
    secondReduction.retained = [secondTrue] := by
  rfl

/--
The constituted component records which branch variables have become part of
the path.  Reduction itself does not add a new determination.
-/
inductive PathConstitutes : List Var → List Var → Type where
  | decide0 : PathConstitutes [] [0]
  | reduce0 : PathConstitutes [0] [0]
  | decide1 : PathConstitutes [0] [1, 0]
  | reduce1 : PathConstitutes [1, 0] [1, 0]

abbrev searchSystem :=
  generatedStructuralBranchSystem formula

def state0 : ConstitutiveState searchSystem (List Var) :=
  { frontier := [root]
    constitution := [] }

def state1 : ConstitutiveState searchSystem (List Var) :=
  { frontier := [firstFalse, firstTrue]
    constitution := [0] }

def state2 : ConstitutiveState searchSystem (List Var) :=
  { frontier := [firstTrue]
    constitution := [0] }

def state3 : ConstitutiveState searchSystem (List Var) :=
  { frontier := [secondFalse, secondTrue]
    constitution := [1, 0] }

def state4 : ConstitutiveState searchSystem (List Var) :=
  { frontier := [secondTrue]
    constitution := [1, 0] }

def expand0 :
    ConstitutiveStep
      searchSystem
      PathConstitutes
      state0
      state1 :=
  { preservation :=
      generatedStructuralExpansion
        root
        0
        rootVar0Fresh
    constitutes := .decide0 }

def reduce0 :
    ConstitutiveStep
      searchSystem
      PathConstitutes
      state1
      state2 :=
  { preservation := firstReduction.preservation
    constitutes := .reduce0 }

def expand1 :
    ConstitutiveStep
      searchSystem
      PathConstitutes
      state2
      state3 :=
  { preservation :=
      generatedStructuralExpansion
        firstTrue
        1
        firstTrueVar1Fresh
    constitutes := .decide1 }

def reduce1 :
    ConstitutiveStep
      searchSystem
      PathConstitutes
      state3
      state4 :=
  { preservation := secondReduction.preservation
    constitutes := .reduce1 }

def trajectory01 :
    FrontierTrajectory
      searchSystem
      PathConstitutes
      state0
      state1 :=
  .snoc (.refl state0) expand0

def trajectory02 :
    FrontierTrajectory
      searchSystem
      PathConstitutes
      state0
      state2 :=
  .snoc trajectory01 reduce0

def trajectory03 :
    FrontierTrajectory
      searchSystem
      PathConstitutes
      state0
      state3 :=
  .snoc trajectory02 expand1

def fullTrajectory :
    FrontierTrajectory
      searchSystem
      PathConstitutes
      state0
      state4 :=
  .snoc trajectory03 reduce1

theorem fullTrajectory_length :
    fullTrajectory.length = 4 := by
  rfl

theorem fullTrajectory_widthTrace :
    fullTrajectory.widthTrace = [1, 2, 1, 2, 1] := by
  rfl

theorem fullTrajectory_maxWidth :
    fullTrajectory.maxWidth = 2 := by
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
      searchSystem
      state0.frontier := by
  exact
    ⟨.head rootContinuation,
      rootContinuation_accept⟩

theorem trajectory_viable_iff :
    FrontierViable
        searchSystem
        state0.frontier ↔
      FrontierViable
        searchSystem
        state4.frontier :=
  fullTrajectory.viable_iff

theorem final_viable :
    FrontierViable
      searchSystem
      state4.frontier :=
  trajectory_viable_iff.mp initial_viable

end ConstitutiveSearch.Tests.FrontierTrajectoryRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.FrontierTrajectoryRegression.firstReduction
#print axioms ConstitutiveSearch.Tests.FrontierTrajectoryRegression.firstReduction_retained
#print axioms ConstitutiveSearch.Tests.FrontierTrajectoryRegression.secondReduction
#print axioms ConstitutiveSearch.Tests.FrontierTrajectoryRegression.secondReduction_retained
#print axioms ConstitutiveSearch.Tests.FrontierTrajectoryRegression.PathConstitutes
#print axioms ConstitutiveSearch.Tests.FrontierTrajectoryRegression.expand0
#print axioms ConstitutiveSearch.Tests.FrontierTrajectoryRegression.reduce0
#print axioms ConstitutiveSearch.Tests.FrontierTrajectoryRegression.expand1
#print axioms ConstitutiveSearch.Tests.FrontierTrajectoryRegression.reduce1
#print axioms ConstitutiveSearch.Tests.FrontierTrajectoryRegression.fullTrajectory
#print axioms ConstitutiveSearch.Tests.FrontierTrajectoryRegression.fullTrajectory_length
#print axioms ConstitutiveSearch.Tests.FrontierTrajectoryRegression.fullTrajectory_widthTrace
#print axioms ConstitutiveSearch.Tests.FrontierTrajectoryRegression.fullTrajectory_maxWidth
#print axioms ConstitutiveSearch.Tests.FrontierTrajectoryRegression.initial_viable
#print axioms ConstitutiveSearch.Tests.FrontierTrajectoryRegression.trajectory_viable_iff
#print axioms ConstitutiveSearch.Tests.FrontierTrajectoryRegression.final_viable
/- AXIOM_AUDIT_END -/
