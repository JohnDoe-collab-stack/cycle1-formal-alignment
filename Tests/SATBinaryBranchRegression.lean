import ConstitutiveSearch.SAT.BinaryBranch

namespace ConstitutiveSearch.Tests.SATBinaryBranchRegression

open SAT

abbrev emptyFormula : Cnf := []

def allFalse : Assignment :=
  fun _ => false

def allTrue : Assignment :=
  fun _ => true

def falseCompletion : Completion emptyFormula :=
  ⟨allFalse, .nil⟩

def trueCompletion : Completion emptyFormula :=
  ⟨allTrue, .nil⟩

abbrev splitAtZero :=
  variableBranchSplit emptyFormula 0

/-- The false assignment enters the false branch by computation. -/
example :
    splitAtZero.split falseCompletion =
      .inl ⟨falseCompletion, rfl⟩ :=
  rfl

/-- The true assignment enters the true branch by computation. -/
example :
    splitAtZero.split trueCompletion =
      .inr ⟨trueCompletion, rfl⟩ :=
  rfl

/-- Merging after the exact branch split reconstructs the supplied completion. -/
example :
    splitAtZero.merge (splitAtZero.split falseCompletion) = falseCompletion :=
  splitAtZero.mergeSplit falseCompletion

end ConstitutiveSearch.Tests.SATBinaryBranchRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATBinaryBranchRegression.falseCompletion
#print axioms ConstitutiveSearch.Tests.SATBinaryBranchRegression.trueCompletion
#print axioms ConstitutiveSearch.Tests.SATBinaryBranchRegression.splitAtZero
/- AXIOM_AUDIT_END -/