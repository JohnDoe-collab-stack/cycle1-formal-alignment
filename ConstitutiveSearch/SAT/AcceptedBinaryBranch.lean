import ConstitutiveSearch.SAT.AcceptedSAT

/-!
# Exact SAT branching on structural assignments

The parent continuation space contains every total assignment.  Child
continuations add only the exact Boolean decision chosen at one variable.
Satisfaction remains the separate acceptance predicate throughout.
-/

namespace ConstitutiveSearch
namespace SAT

/-- Assignment carrying one exact Boolean decision. -/
abbrev FixedAssignment
    (var : Var)
    (value : Bool) : Type :=
  { assignment : Assignment // assignment var = value }

/-- Split every assignment by its actual value at one variable. -/
def splitAssignment
    (var : Var)
    (assignment : Assignment) :
    FixedAssignment var false ⊕
      FixedAssignment var true :=
  match valueExact : assignment var with
  | false =>
      .inl ⟨assignment, valueExact⟩
  | true =>
      .inr ⟨assignment, valueExact⟩

/-- Forget the decision index and recover the underlying assignment. -/
def mergeAssignment
    {var : Var} :
    FixedAssignment var false ⊕
        FixedAssignment var true →
      Assignment
  | .inl assignment => assignment.1
  | .inr assignment => assignment.1

/-- Forgetting after splitting reconstructs the original assignment. -/
theorem merge_split_assignment
    (var : Var)
    (assignment : Assignment) :
    mergeAssignment (splitAssignment var assignment) =
      assignment := by
  unfold splitAssignment
  cases valueExact : assignment var <;> rfl

/-- Splitting after forgetting reconstructs the indexed branch. -/
theorem split_merge_assignment
    {var : Var}
    (branch :
      FixedAssignment var false ⊕
        FixedAssignment var true) :
    splitAssignment var (mergeAssignment branch) =
      branch := by
  cases branch with
  | inl leftAssignment =>
      cases leftAssignment with
      | mk assignment valueExact =>
          unfold mergeAssignment
          unfold splitAssignment
          rw [valueExact]
          apply congrArg Sum.inl
          apply Subtype.ext
          rfl
  | inr rightAssignment =>
      cases rightAssignment with
      | mk assignment valueExact =>
          unfold mergeAssignment
          unfold splitAssignment
          rw [valueExact]
          apply congrArg Sum.inr
          apply Subtype.ext
          rfl

/-- Parent and two structurally indexed child views of one SAT formula. -/
inductive StructuralVariableBranchState where
  | parent : Cnf → Var → StructuralVariableBranchState
  | fixedFalse : Cnf → Var → StructuralVariableBranchState
  | fixedTrue : Cnf → Var → StructuralVariableBranchState

/-- Structural continuations contain no satisfaction proof. -/
def StructuralVariableBranchContinuation :
    StructuralVariableBranchState →
      Type
  | .parent _formula _var =>
      Assignment
  | .fixedFalse _formula var =>
      FixedAssignment var false
  | .fixedTrue _formula var =>
      FixedAssignment var true

/-- Satisfaction is a predicate on structural branch continuations. -/
def StructuralVariableBranchAccept :
    (state : StructuralVariableBranchState) →
      StructuralVariableBranchContinuation state →
        Prop
  | .parent formula _var, assignment =>
      Satisfies assignment formula
  | .fixedFalse formula _var, assignment =>
      Satisfies assignment.1 formula
  | .fixedTrue formula _var, assignment =>
      Satisfies assignment.1 formula

/-- Hardened search system for one exact SAT branching view. -/
def structuralVariableBranchSystem : SearchSystem :=
  { State := StructuralVariableBranchState
    Continuation := StructuralVariableBranchContinuation
    Accept := StructuralVariableBranchAccept }

/-- Exact structural OR split by one assignment bit. -/
def structuralVariableBranchSplit
    (formula : Cnf)
    (var : Var) :
    AcceptingExactBinarySplit
      structuralVariableBranchSystem
      (.parent formula var)
      (.fixedFalse formula var)
      (.fixedTrue formula var) :=
  { split := splitAssignment var
    merge := mergeAssignment
    splitMerge := split_merge_assignment
    mergeSplit := merge_split_assignment var
    splitPreservesAccept := by
      intro assignment accepted
      unfold splitAssignment
      cases valueExact : assignment var <;> exact accepted
    mergePreservesAccept := by
      intro branch accepted
      cases branch with
      | inl _leftAssignment =>
          exact accepted
      | inr _rightAssignment =>
          exact accepted }

/-- Parent viability is exactly the disjunction of the two decision branches. -/
theorem structural_branch_viable_iff
    (formula : Cnf)
    (var : Var) :
    structuralVariableBranchSystem.Viable
        (.parent formula var) ↔
      structuralVariableBranchSystem.Viable
          (.fixedFalse formula var) ∨
        structuralVariableBranchSystem.Viable
          (.fixedTrue formula var) :=
  (structuralVariableBranchSplit formula var).viable_iff

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.FixedAssignment
#print axioms ConstitutiveSearch.SAT.splitAssignment
#print axioms ConstitutiveSearch.SAT.merge_split_assignment
#print axioms ConstitutiveSearch.SAT.split_merge_assignment
#print axioms ConstitutiveSearch.SAT.StructuralVariableBranchState
#print axioms ConstitutiveSearch.SAT.StructuralVariableBranchContinuation
#print axioms ConstitutiveSearch.SAT.StructuralVariableBranchAccept
#print axioms ConstitutiveSearch.SAT.structuralVariableBranchSystem
#print axioms ConstitutiveSearch.SAT.structuralVariableBranchSplit
#print axioms ConstitutiveSearch.SAT.structural_branch_viable_iff
/- AXIOM_AUDIT_END -/
