import ConstitutiveSearch.SAT.GeneratedStructuralContext

namespace ConstitutiveSearch.Tests.SATGeneratedStructuralContextRegression

open ConstitutiveSearch
open SAT

abbrev c0 : Clause :=
  [Literal.positive 0]

abbrev c1 : Clause :=
  [Literal.positive 1]

abbrev formula : Cnf :=
  [c0, c1]

abbrev root :
    GeneratedStructuralBranchContext formula :=
  GeneratedStructuralBranchContext.root formula

theorem rootVar0Fresh :
    StructuralDecisionsAvoid
      0
      root.context.decisions :=
  True.intro

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

theorem root_depth :
    root.depth = 0 :=
  rfl

theorem first_depth :
    firstTrue.depth = 1 :=
  rfl

theorem second_depth :
    secondTrue.depth = 2 :=
  rfl

theorem second_history :
    secondTrue.context.decisions =
      [{ var := 1, value := true },
        { var := 0, value := true }] :=
  rfl

def allTrue : Assignment :=
  fun _ => true

theorem allTrue_root_accept :
    Satisfies allTrue formula :=
  .cons rfl
    (.cons rfl .nil)

def rootContinuation :
    GeneratedStructuralBranchContinuation root :=
  ⟨allTrue, True.intro⟩

def firstTrueContinuation :
    GeneratedStructuralBranchContinuation firstTrue :=
  ⟨allTrue, ⟨rfl, True.intro⟩⟩

def secondTrueContinuation :
    GeneratedStructuralBranchContinuation secondTrue :=
  ⟨allTrue, ⟨rfl, ⟨rfl, True.intro⟩⟩⟩

theorem rootContinuation_accept :
    GeneratedStructuralBranchAccept
      root rootContinuation :=
  allTrue_root_accept

theorem firstTrueContinuation_accept :
    GeneratedStructuralBranchAccept
      firstTrue firstTrueContinuation :=
  (branchWeakening formula 0 true).preservesSatisfaction
    allTrue_root_accept

theorem secondTrueContinuation_accept :
    GeneratedStructuralBranchAccept
      secondTrue secondTrueContinuation :=
  (branchWeakening firstTrue.context.formula 1 true).preservesSatisfaction
    firstTrueContinuation_accept

/-- Different generated parents coexist in one uniform frontier type. -/
def heterogeneousFrontier :
    List (GeneratedStructuralBranchContext formula) :=
  [firstTrue, secondFalse, secondTrue]

def secondExpansion :=
  generatedStructuralExpansion
    firstTrue
    1
    firstTrueVar1Fresh

theorem second_expansion_viable_iff :
    FrontierViable
        (generatedStructuralBranchSystem formula)
        [firstTrue] ↔
      FrontierViable
        (generatedStructuralBranchSystem formula)
        [secondFalse, secondTrue] :=
  secondExpansion.viable_iff

end ConstitutiveSearch.Tests.SATGeneratedStructuralContextRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATGeneratedStructuralContextRegression.rootVar0Fresh
#print axioms ConstitutiveSearch.Tests.SATGeneratedStructuralContextRegression.firstTrueVar1Fresh
#print axioms ConstitutiveSearch.Tests.SATGeneratedStructuralContextRegression.root_depth
#print axioms ConstitutiveSearch.Tests.SATGeneratedStructuralContextRegression.first_depth
#print axioms ConstitutiveSearch.Tests.SATGeneratedStructuralContextRegression.second_depth
#print axioms ConstitutiveSearch.Tests.SATGeneratedStructuralContextRegression.second_history
#print axioms ConstitutiveSearch.Tests.SATGeneratedStructuralContextRegression.rootContinuation
#print axioms ConstitutiveSearch.Tests.SATGeneratedStructuralContextRegression.firstTrueContinuation
#print axioms ConstitutiveSearch.Tests.SATGeneratedStructuralContextRegression.secondTrueContinuation
#print axioms ConstitutiveSearch.Tests.SATGeneratedStructuralContextRegression.rootContinuation_accept
#print axioms ConstitutiveSearch.Tests.SATGeneratedStructuralContextRegression.firstTrueContinuation_accept
#print axioms ConstitutiveSearch.Tests.SATGeneratedStructuralContextRegression.secondTrueContinuation_accept
#print axioms ConstitutiveSearch.Tests.SATGeneratedStructuralContextRegression.heterogeneousFrontier
#print axioms ConstitutiveSearch.Tests.SATGeneratedStructuralContextRegression.secondExpansion
#print axioms ConstitutiveSearch.Tests.SATGeneratedStructuralContextRegression.second_expansion_viable_iff
/- AXIOM_AUDIT_END -/
