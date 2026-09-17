import ConstitutiveSearch.SAT.RestrictionTransport

namespace ConstitutiveSearch.Tests.SATRestrictionTransportRegression

open SAT

abbrev clauseZero : Clause :=
  [Literal.positive 0]

abbrev clauseOne : Clause :=
  [Literal.positive 1]

abbrev formula : Cnf :=
  [clauseZero, clauseOne]

/-- Fixing variable zero to true deletes exactly the clause it already satisfies. -/
theorem residual_true_zero :
    branchResidual formula 0 true = [clauseOne] := by
  rfl

/-- Fixing variable zero to false does not delete the positive unit clause. -/
theorem residual_false_zero :
    branchResidual formula 0 false = formula := by
  rfl

def allTrue : Assignment :=
  fun _ => true

def fullCompletion : Completion formula :=
  ⟨allTrue, .cons rfl (.cons rfl .nil)⟩

/-- The satisfying assignment is definitionally indexed by the chosen true branch. -/
def trueBranchCompletion :
    ValueIndexedCompletion formula 0 true :=
  ValueIndexedCompletion.ofCompletion fullCompletion

/-- The branch completion transports to the residual CNF while retaining the bit provenance. -/
def trueResidualCompletion :
    ResidualBranchCompletion formula 0 true :=
  branchToResidual trueBranchCompletion

example : trueResidualCompletion.assignment 0 = true :=
  trueResidualCompletion.valueExact

example :
    Satisfies trueResidualCompletion.assignment
      (branchResidual formula 0 true) :=
  trueResidualCompletion.residualSatisfaction

/-- Residual data reconstructs a completion of the original branch. -/
def reconstructedBranch :
    ValueIndexedCompletion formula 0 true :=
  residualToBranch trueResidualCompletion

example : reconstructedBranch.underlying.1 0 = true :=
  indexedCompletion_valueExact reconstructedBranch

/-- Positive completion existence is equivalent between the branch and its residual view. -/
theorem true_branch_residual_equivalent :
    Nonempty (ValueIndexedCompletion formula 0 true) ↔
      Nonempty (ResidualBranchCompletion formula 0 true) :=
  branch_residual_nonempty_iff formula 0 true

end ConstitutiveSearch.Tests.SATRestrictionTransportRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATRestrictionTransportRegression.residual_true_zero
#print axioms ConstitutiveSearch.Tests.SATRestrictionTransportRegression.residual_false_zero
#print axioms ConstitutiveSearch.Tests.SATRestrictionTransportRegression.fullCompletion
#print axioms ConstitutiveSearch.Tests.SATRestrictionTransportRegression.trueBranchCompletion
#print axioms ConstitutiveSearch.Tests.SATRestrictionTransportRegression.trueResidualCompletion
#print axioms ConstitutiveSearch.Tests.SATRestrictionTransportRegression.reconstructedBranch
#print axioms ConstitutiveSearch.Tests.SATRestrictionTransportRegression.true_branch_residual_equivalent
/- AXIOM_AUDIT_END -/