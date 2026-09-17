import ConstitutiveSearch.SAT.ConstraintTransport

/-!
# Exact SAT branching by one Boolean variable

This module isolates the OR step of SAT self-reduction from every later CNF
simplification.

For a fixed CNF and variable, a parent completion is exactly partitioned by the
Boolean value assigned to that variable.  The two child completion spaces keep
the same satisfying assignment together with the additional branch fact
`assignment var = false` or `assignment var = true`.

No satisfiability query is performed.  The split is defined directly on an
already supplied completion and is reversible by forgetting the branch fact.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Three structural views of one CNF at one branching variable. -/
inductive VariableBranchState where
  | parent : Cnf → Var → VariableBranchState
  | fixedFalse : Cnf → Var → VariableBranchState
  | fixedTrue : Cnf → Var → VariableBranchState

/-- Completion spaces for the parent and its two exact Boolean branches. -/
def VariableBranchCompletion : VariableBranchState → Type
  | .parent formula _var => Completion formula
  | .fixedFalse formula var =>
      { completion : Completion formula // completion.1 var = false }
  | .fixedTrue formula var =>
      { completion : Completion formula // completion.1 var = true }

/-- Exact constructive split of satisfying assignments by one variable value. -/
def variableBranchSplit
    (formula : Cnf)
    (var : Var) :
    ExactBinarySplit
      VariableBranchCompletion
      (.parent formula var)
      (.fixedFalse formula var)
      (.fixedTrue formula var) :=
  { split := fun completion =>
      match valueEq : completion.1 var with
      | false => .inl ⟨completion, valueEq⟩
      | true => .inr ⟨completion, valueEq⟩
    merge := fun branch =>
      match branch with
      | .inl completion => completion.1
      | .inr completion => completion.1
    splitMerge := by
      intro branch
      cases branch with
      | inl left =>
          rcases left with ⟨completion, branchEq⟩
          cases valueEq : completion.1 var with
          | false => rfl
          | true => cases branchEq
      | inr right =>
          rcases right with ⟨completion, branchEq⟩
          cases valueEq : completion.1 var with
          | false => cases branchEq
          | true => rfl
    mergeSplit := by
      intro completion
      cases valueEq : completion.1 var <;> rfl }

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.VariableBranchState
#print axioms ConstitutiveSearch.SAT.VariableBranchCompletion
#print axioms ConstitutiveSearch.SAT.variableBranchSplit
/- AXIOM_AUDIT_END -/