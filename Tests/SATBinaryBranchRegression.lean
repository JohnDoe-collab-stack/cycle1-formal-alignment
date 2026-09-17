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

/-- The false assignment enters the false branch through exact parent indexing. -/
example :
    splitCompletion emptyFormula 0 falseCompletion =
      .inl (ValueIndexedCompletion.ofCompletion falseCompletion) :=
  rfl

/-- The true assignment enters the true branch through exact parent indexing. -/
example :
    splitCompletion emptyFormula 0 trueCompletion =
      .inr (ValueIndexedCompletion.ofCompletion trueCompletion) :=
  rfl

/-- Forgetting the branch after the exact split reconstructs the supplied completion. -/
example :
    mergeCompletion emptyFormula 0
        (splitCompletion emptyFormula 0 falseCompletion) =
      falseCompletion :=
  merge_split_completion emptyFormula 0 falseCompletion

/-- The parent indexing itself has exact round trips. -/
example :
    (parentIndexing emptyFormula 0).backward
        ((parentIndexing emptyFormula 0).forward trueCompletion) =
      trueCompletion :=
  (parentIndexing emptyFormula 0).forwardBackward trueCompletion

end ConstitutiveSearch.Tests.SATBinaryBranchRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATBinaryBranchRegression.falseCompletion
#print axioms ConstitutiveSearch.Tests.SATBinaryBranchRegression.trueCompletion
#print axioms ConstitutiveSearch.Tests.SATBinaryBranchRegression.merge_split_completion
/- AXIOM_AUDIT_END -/