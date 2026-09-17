import ConstitutiveSearch.SAT.StructuralBranchContext

namespace ConstitutiveSearch.Tests.SATStructuralBranchContextRegression

open ConstitutiveSearch
open SAT

abbrev c0 : Clause :=
  [Literal.positive 0]

abbrev c1 : Clause :=
  [Literal.positive 1]

abbrev formula : Cnf :=
  [c0, c1]

abbrev root : StructuralBranchContext :=
  structuralRootContext formula

abbrev firstTrue : StructuralBranchContext :=
  structuralChildContext root 0 true

abbrev secondTrue : StructuralBranchContext :=
  structuralChildContext firstTrue 1 true

def allTrue : Assignment :=
  fun _ => true

def allFalse : Assignment :=
  fun _ => false

theorem allTrue_root_accept :
    Satisfies allTrue formula :=
  .cons rfl
    (.cons rfl .nil)

/-- A rejected assignment remains a valid structural root continuation. -/
def rejectedRootContinuation :
    StructuralBranchContinuation root :=
  ⟨allFalse, True.intro⟩

theorem rejectedRoot_not_accepted :
    structuralBranchContextSystem.Accept
        root rejectedRootContinuation →
      False := by
  intro accepted
  cases accepted with
  | cons headSatisfied _tailSatisfied =>
      cases headSatisfied

def rootContinuation :
    StructuralBranchContinuation root :=
  ⟨allTrue, True.intro⟩

theorem rootContinuation_accept :
    structuralBranchContextSystem.Accept
      root rootContinuation :=
  allTrue_root_accept

/-- The first constituted decision is represented structurally. -/
def firstTrueContinuation :
    StructuralBranchContinuation firstTrue :=
  ⟨allTrue, ⟨rfl, True.intro⟩⟩

theorem firstTrue_history :
    StructuralDecisionsHold
      firstTrueContinuation.1
      firstTrue.decisions :=
  firstTrueContinuation.2

theorem firstTrue_accept :
    structuralBranchContextSystem.Accept
      firstTrue firstTrueContinuation :=
  (branchWeakening formula 0 true).preservesSatisfaction
    allTrue_root_accept

/-- A second decision extends the same structural history. -/
def secondTrueContinuation :
    StructuralBranchContinuation secondTrue :=
  ⟨allTrue, ⟨rfl, ⟨rfl, True.intro⟩⟩⟩

theorem secondTrue_history :
    StructuralDecisionsHold
      secondTrueContinuation.1
      secondTrue.decisions :=
  secondTrueContinuation.2

theorem secondTrue_accept :
    structuralBranchContextSystem.Accept
      secondTrue secondTrueContinuation :=
  (branchWeakening firstTrue.formula 1 true).preservesSatisfaction
    firstTrue_accept

def firstExpansion :=
  structuralContextExpansion root 0

def secondExpansion :=
  structuralContextExpansion firstTrue 1

theorem first_expansion_viable_iff :
    FrontierViable
        structuralBranchContextSystem
        [root] ↔
      FrontierViable
        structuralBranchContextSystem
        [structuralChildContext root 0 false,
          structuralChildContext root 0 true] :=
  firstExpansion.viable_iff

theorem second_expansion_viable_iff :
    FrontierViable
        structuralBranchContextSystem
        [firstTrue] ↔
      FrontierViable
        structuralBranchContextSystem
        [structuralChildContext firstTrue 1 false,
          structuralChildContext firstTrue 1 true] :=
  secondExpansion.viable_iff

/-- The generated two-level history is exactly newest decision first. -/
theorem secondTrue_decisions_exact :
    secondTrue.decisions =
      [{ var := 1, value := true },
        { var := 0, value := true }] :=
  rfl

end ConstitutiveSearch.Tests.SATStructuralBranchContextRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATStructuralBranchContextRegression.rejectedRootContinuation
#print axioms ConstitutiveSearch.Tests.SATStructuralBranchContextRegression.rejectedRoot_not_accepted
#print axioms ConstitutiveSearch.Tests.SATStructuralBranchContextRegression.rootContinuation
#print axioms ConstitutiveSearch.Tests.SATStructuralBranchContextRegression.rootContinuation_accept
#print axioms ConstitutiveSearch.Tests.SATStructuralBranchContextRegression.firstTrueContinuation
#print axioms ConstitutiveSearch.Tests.SATStructuralBranchContextRegression.firstTrue_history
#print axioms ConstitutiveSearch.Tests.SATStructuralBranchContextRegression.firstTrue_accept
#print axioms ConstitutiveSearch.Tests.SATStructuralBranchContextRegression.secondTrueContinuation
#print axioms ConstitutiveSearch.Tests.SATStructuralBranchContextRegression.secondTrue_history
#print axioms ConstitutiveSearch.Tests.SATStructuralBranchContextRegression.secondTrue_accept
#print axioms ConstitutiveSearch.Tests.SATStructuralBranchContextRegression.firstExpansion
#print axioms ConstitutiveSearch.Tests.SATStructuralBranchContextRegression.secondExpansion
#print axioms ConstitutiveSearch.Tests.SATStructuralBranchContextRegression.first_expansion_viable_iff
#print axioms ConstitutiveSearch.Tests.SATStructuralBranchContextRegression.second_expansion_viable_iff
#print axioms ConstitutiveSearch.Tests.SATStructuralBranchContextRegression.secondTrue_decisions_exact
/- AXIOM_AUDIT_END -/
