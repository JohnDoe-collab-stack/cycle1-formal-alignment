import ConstitutiveSearch.SAT.BranchContext
import ConstitutiveSearch.FiniteFrontierNormalization

namespace ConstitutiveSearch.Tests.SATBranchContextRegression

open SAT

abbrev c0p : Clause :=
  [Literal.positive 0, Literal.positive 2]

abbrev c0n : Clause :=
  [Literal.negative 0, Literal.positive 2]

abbrev c1p : Clause :=
  [Literal.positive 1, Literal.positive 2]

abbrev c1n : Clause :=
  [Literal.negative 1, Literal.positive 2]

abbrev branchingFormula : Cnf :=
  [c0p, c0n, c1p, c1n]

abbrev root : BranchContext :=
  rootContext branchingFormula

abbrev firstFalse : BranchContext :=
  childContext root 0 false

abbrev firstTrue : BranchContext :=
  childContext root 0 true

abbrev secondFalse : BranchContext :=
  childContext firstTrue 1 false

abbrev secondTrue : BranchContext :=
  childContext firstTrue 1 true

/-- The first branch records exactly one decision. -/
theorem firstTrue_decisions_exact :
    firstTrue.decisions =
      [{ var := 0, value := true }] := by
  rfl

/-- Recursive branching prepends the new decision and preserves the old one. -/
theorem secondTrue_decisions_exact :
    secondTrue.decisions =
      [ { var := 1, value := true },
        { var := 0, value := true } ] := by
  rfl

/-- The root expands exactly into its two first-level child contexts. -/
def firstExpansion :
    FrontierTransport BranchContextCompletion
      [root]
      [firstFalse, firstTrue] :=
  FrontierCompletion.expandHead (contextSplit root 0)

/--
The true first-level branch is then split again while the false sibling is
preserved as another frontier state.
-/
def secondExpansion :
    FrontierTransport BranchContextCompletion
      [firstFalse, firstTrue]
      [secondFalse, secondTrue, firstFalse] :=
  (FrontierCompletion.swapFirstTwo
    (Completion := BranchContextCompletion)
    (first := firstFalse)
    (second := firstTrue)
    (rest := [])).trans
    (FrontierCompletion.expandHead
      (rest := [firstFalse])
      (contextSplit firstTrue 1))

/-- Two exact OR steps compose into one three-leaf frontier expansion. -/
def twoLevelExpansion :
    FrontierTransport BranchContextCompletion
      [root]
      [secondFalse, secondTrue, firstFalse] :=
  firstExpansion.trans secondExpansion

/-- One concrete satisfying root completion used only to test transport data. -/
def allTrue : Assignment :=
  fun _var => true

def rootAllTrue : root.Carrier :=
  ⟨allTrue,
    .cons rfl
      (.cons rfl
        (.cons rfl
          (.cons rfl .nil)))⟩

/-- The actual first decision of the concrete completion is true. -/
def firstTrueCompletion : firstTrue.Carrier :=
  .ofParent rootAllTrue

/-- The actual second decision is also true. -/
def secondTrueCompletion : secondTrue.Carrier :=
  .ofParent firstTrueCompletion

example :
    secondTrue.assignment secondTrueCompletion 1 = true :=
  childContext_newDecisionExact firstTrue 1 true secondTrueCompletion

example :
    secondTrue.assignment secondTrueCompletion 0 = true := by
  exact
    (childContext_parentDecisionsExact
      firstTrue 1 true secondTrueCompletion).1

/-- The full decision history is realized by the final concrete completion. -/
theorem secondTrue_completion_realizes_history :
    DecisionsHold
      (secondTrue.assignment secondTrueCompletion)
      secondTrue.decisions :=
  secondTrue.decisionsExact secondTrueCompletion

/-- Splitting and merging at each recursive level reconstructs the parent completion. -/
theorem first_split_roundTrip :
    (contextSplit root 0).merge
        ((contextSplit root 0).split rootAllTrue) =
      rootAllTrue :=
  (contextSplit root 0).mergeSplit rootAllTrue

theorem second_split_roundTrip :
    (contextSplit firstTrue 1).merge
        ((contextSplit firstTrue 1).split firstTrueCompletion) =
      firstTrueCompletion :=
  (contextSplit firstTrue 1).mergeSplit firstTrueCompletion

/-- The composed two-level expansion transports a concrete root completion. -/
def sourceFrontierCompletion :
    FrontierCompletion BranchContextCompletion [root] :=
  .head rootAllTrue

def expandedFrontierCompletion :
    FrontierCompletion BranchContextCompletion
      [secondFalse, secondTrue, firstFalse] :=
  twoLevelExpansion.map sourceFrontierCompletion

example :
    Nonempty
      (FrontierCompletion BranchContextCompletion
        [secondFalse, secondTrue, firstFalse]) :=
  ⟨expandedFrontierCompletion⟩

end ConstitutiveSearch.Tests.SATBranchContextRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATBranchContextRegression.firstTrue_decisions_exact
#print axioms ConstitutiveSearch.Tests.SATBranchContextRegression.secondTrue_decisions_exact
#print axioms ConstitutiveSearch.Tests.SATBranchContextRegression.firstExpansion
#print axioms ConstitutiveSearch.Tests.SATBranchContextRegression.secondExpansion
#print axioms ConstitutiveSearch.Tests.SATBranchContextRegression.twoLevelExpansion
#print axioms ConstitutiveSearch.Tests.SATBranchContextRegression.rootAllTrue
#print axioms ConstitutiveSearch.Tests.SATBranchContextRegression.secondTrueCompletion
#print axioms ConstitutiveSearch.Tests.SATBranchContextRegression.secondTrue_completion_realizes_history
#print axioms ConstitutiveSearch.Tests.SATBranchContextRegression.first_split_roundTrip
#print axioms ConstitutiveSearch.Tests.SATBranchContextRegression.second_split_roundTrip
#print axioms ConstitutiveSearch.Tests.SATBranchContextRegression.expandedFrontierCompletion
/- AXIOM_AUDIT_END -/
