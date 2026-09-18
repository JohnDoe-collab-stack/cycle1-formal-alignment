import ConstitutiveSearch.SAT.StructuralProgress

namespace ConstitutiveSearch.Tests.SATStructuralProgressRegression

open ConstitutiveSearch
open SAT

abbrev c0 : Clause :=
  [Literal.positive 0]

abbrev c1 : Clause :=
  [Literal.positive 1]

abbrev formula : Cnf :=
  [c0, c1]

theorem formula_resource_exact :
    formula.variableOccurrences = [0, 1] := by
  rfl

abbrev root :
    GeneratedStructuralBranchContext formula :=
  GeneratedStructuralBranchContext.root formula

theorem rootVar1Fresh :
    StructuralDecisionsAvoid
      1
      root.context.decisions :=
  True.intro

/--
Select variable 1 first even though the finite syntax resource is [0,1].
This demonstrates that resource accounting imposes no traversal order.
-/
def removeVar1 :
    VarRemoval 1 [0, 1] [0] :=
  .tail (by decide) (.head [])

abbrev first :
    GeneratedStructuralBranchContext formula :=
  GeneratedStructuralBranchContext.child
    root
    1
    true
    rootVar1Fresh

theorem firstVar0Fresh :
    StructuralDecisionsAvoid
      0
      first.context.decisions := by
  constructor
  · decide
  · exact True.intro

def removeVar0 :
    VarRemoval 0 [0] [] :=
  .head []

abbrev second :
    GeneratedStructuralBranchContext formula :=
  GeneratedStructuralBranchContext.child
    first
    0
    true
    firstVar0Fresh

def generatedRoot :
    FormulaResourceGeneratedFrom
      formula
      [0, 1]
      root :=
  .root

def generatedFirst :
    FormulaResourceGeneratedFrom
      formula
      [0]
      first :=
  .child
    generatedRoot
    1
    true
    rootVar1Fresh
    removeVar1

def generatedSecond :
    FormulaResourceGeneratedFrom
      formula
      []
      second :=
  .child
    generatedFirst
    0
    true
    firstVar0Fresh
    removeVar0

theorem second_depth :
    second.depth = 2 := by
  rfl

theorem second_history :
    second.context.decisions =
      [{ var := 0, value := true },
       { var := 1, value := true }] := by
  rfl

/-- No external iteration count: exact budget is derived from the consumed syntax. -/
theorem exact_budget :
    second.depth + [].length =
      formula.variableOccurrences.length :=
  generatedSecond.budget_exact

theorem depth_bounded_by_input_resource :
    second.depth ≤
      formula.variableOccurrences.length :=
  generatedSecond.depth_le_initial

/-- The full two-decision path consumed the complete two-occurrence resource. -/
theorem complete_resource_consumption :
    formula.variableOccurrences.length = 2 ∧
      second.depth = 2 := by
  exact ⟨rfl, rfl⟩

end ConstitutiveSearch.Tests.SATStructuralProgressRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATStructuralProgressRegression.formula_resource_exact
#print axioms ConstitutiveSearch.Tests.SATStructuralProgressRegression.removeVar1
#print axioms ConstitutiveSearch.Tests.SATStructuralProgressRegression.removeVar0
#print axioms ConstitutiveSearch.Tests.SATStructuralProgressRegression.generatedRoot
#print axioms ConstitutiveSearch.Tests.SATStructuralProgressRegression.generatedFirst
#print axioms ConstitutiveSearch.Tests.SATStructuralProgressRegression.generatedSecond
#print axioms ConstitutiveSearch.Tests.SATStructuralProgressRegression.second_depth
#print axioms ConstitutiveSearch.Tests.SATStructuralProgressRegression.second_history
#print axioms ConstitutiveSearch.Tests.SATStructuralProgressRegression.exact_budget
#print axioms ConstitutiveSearch.Tests.SATStructuralProgressRegression.depth_bounded_by_input_resource
#print axioms ConstitutiveSearch.Tests.SATStructuralProgressRegression.complete_resource_consumption
/- AXIOM_AUDIT_END -/
