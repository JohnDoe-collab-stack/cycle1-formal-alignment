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
theorem falseCompletion_entersFalseBranch :
    splitCompletion emptyFormula 0 falseCompletion =
      .inl (ValueIndexedCompletion.ofCompletion falseCompletion) :=
  rfl

/-- The true assignment enters the true branch through exact parent indexing. -/
theorem trueCompletion_entersTrueBranch :
    splitCompletion emptyFormula 0 trueCompletion =
      .inr (ValueIndexedCompletion.ofCompletion trueCompletion) :=
  rfl

/-- Forgetting the branch after the exact split reconstructs the supplied completion. -/
theorem false_merge_split_roundTrip :
    mergeCompletion emptyFormula 0
        (splitCompletion emptyFormula 0 falseCompletion) =
      falseCompletion :=
  merge_split_completion emptyFormula 0 falseCompletion

/-- The parent indexing itself has exact round trips. -/
theorem true_parentIndexing_roundTrip :
    (parentIndexing emptyFormula 0).backward
        ((parentIndexing emptyFormula 0).forward trueCompletion) =
      trueCompletion :=
  (parentIndexing emptyFormula 0).forwardBackward trueCompletion

end ConstitutiveSearch.Tests.SATBinaryBranchRegression

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.Tests.SATBinaryBranchRegression.falseCompletion
#print axioms ConstitutiveSearch.Tests.SATBinaryBranchRegression.trueCompletion
#print axioms ConstitutiveSearch.Tests.SATBinaryBranchRegression.falseCompletion_entersFalseBranch
#print axioms ConstitutiveSearch.Tests.SATBinaryBranchRegression.trueCompletion_entersTrueBranch
#print axioms ConstitutiveSearch.Tests.SATBinaryBranchRegression.false_merge_split_roundTrip
#print axioms ConstitutiveSearch.Tests.SATBinaryBranchRegression.true_parentIndexing_roundTrip
/- AXIOM_AUDIT_END -/