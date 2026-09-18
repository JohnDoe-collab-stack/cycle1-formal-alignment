import ConstitutiveSearch.SAT.GeneratedStructuralContext

/-!
# Structural progress from a finite SAT variable resource

This module derives a finite progress budget from SAT syntax rather than
imposing an external iteration counter.

The initial resource is the finite list of variable occurrences in the root
CNF. A generated decision may consume any matching occurrence from the
remaining resource; no fixed variable order is imposed.

Each step still carries the existing freshness proof, so resource accounting
does not replace constitutive provenance. It only certifies that every
generated decision consumes finite input structure.
-/

namespace ConstitutiveSearch
namespace SAT

namespace Literal

/-- Variable mentioned by one literal. -/
def varOf : Literal → Var
  | .positive var => var
  | .negative var => var

end Literal

namespace Clause

/-- Variable occurrences in one clause, preserving syntax order and duplicates. -/
def variableOccurrences : Clause → List Var
  | [] => []
  | literal :: rest =>
      literal.varOf :: variableOccurrences rest

end Clause

namespace Cnf

/-- Finite variable-occurrence resource carried by a CNF syntax tree. -/
def variableOccurrences : Cnf → List Var
  | [] => []
  | clause :: rest =>
      clause.variableOccurrences ++
        variableOccurrences rest

end Cnf

/--
Proof-relevant removal of one selected variable occurrence from a finite
resource. The selected occurrence may occur anywhere in the list.
-/
inductive VarRemoval
    (var : Var) :
    List Var → List Var → Type where
  | head
      (rest : List Var) :
      VarRemoval var (var :: rest) rest
  | tail
      {head : Var}
      {source target : List Var}
      (different : head ≠ var)
      (removed : VarRemoval var source target) :
      VarRemoval var
        (head :: source)
        (head :: target)

namespace VarRemoval

/-- Removing one occurrence decreases resource length by exactly one. -/
theorem length_eq
    {var : Var}
    {source target : List Var}
    (removed : VarRemoval var source target) :
    source.length = target.length + 1 := by
  induction removed with
  | head rest =>
      rfl
  | tail different removed inductionHypothesis =>
      simp only [List.length_cons]
      rw [inductionHypothesis]

/-- Executable search for one removable occurrence. -/
def find
    (var : Var) :
    (source : List Var) →
      Option
        (Sigma fun target =>
          VarRemoval var source target)
  | [] => none
  | current :: tail =>
      if same : current = var then
        by
          cases same
          exact some ⟨tail, .head tail⟩
      else
        match find var tail with
        | none => none
        | some ⟨remaining, removed⟩ =>
            some
              ⟨current :: remaining,
                .tail same removed⟩

end VarRemoval

/--
Generated SAT provenance augmented with a finite resource account.

The initial resource is fixed for the complete history. Each child consumes one
selected occurrence from the currently remaining resource and still requires
the ordinary freshness proof of GeneratedStructuralBranchContext.
-/
inductive ResourceGeneratedFrom
    (rootFormula : Cnf)
    (initial : List Var) :
    List Var →
      GeneratedStructuralBranchContext rootFormula →
        Type where
  | root :
      ResourceGeneratedFrom
        rootFormula
        initial
        initial
        (GeneratedStructuralBranchContext.root rootFormula)
  | child
      {available remaining : List Var}
      {parent : GeneratedStructuralBranchContext rootFormula}
      (parentGenerated :
        ResourceGeneratedFrom
          rootFormula
          initial
          available
          parent)
      (var : Var)
      (value : Bool)
      (fresh :
        StructuralDecisionsAvoid
          var
          parent.context.decisions)
      (removed :
        VarRemoval var available remaining) :
      ResourceGeneratedFrom
        rootFormula
        initial
        remaining
        (GeneratedStructuralBranchContext.child
          parent
          var
          value
          fresh)

namespace ResourceGeneratedFrom

/--
Exact finite-resource invariant: constituted depth plus remaining resource
equals the initial resource length.
-/
theorem budget_exact
    {rootFormula : Cnf}
    {initial remaining : List Var}
    {state : GeneratedStructuralBranchContext rootFormula}
    (generated :
      ResourceGeneratedFrom
        rootFormula
        initial
        remaining
        state) :
    state.depth + remaining.length =
      initial.length := by
  induction generated with
  | root =>
      rfl
  | @child available remaining parent parentGenerated var value fresh removed inductionHypothesis =>
      calc
        (GeneratedStructuralBranchContext.child
            parent var value fresh).depth +
              remaining.length
            = (parent.depth + 1) +
                remaining.length := by
                  rw [GeneratedStructuralBranchContext.child_depth]
        _ = parent.depth +
              (1 + remaining.length) := by
                rw [Nat.add_assoc]
        _ = parent.depth +
              (remaining.length + 1) := by
                rw [Nat.add_comm 1 remaining.length]
        _ = parent.depth +
              available.length := by
                rw [← removed.length_eq]
        _ = initial.length :=
              inductionHypothesis

/-- Constructive depth-bound certificate with remaining resource as slack. -/
theorem depth_bound_certificate
    {rootFormula : Cnf}
    {initial remaining : List Var}
    {state : GeneratedStructuralBranchContext rootFormula}
    (generated :
      ResourceGeneratedFrom
        rootFormula
        initial
        remaining
        state) :
    ∃ slack : Nat,
      state.depth + slack = initial.length :=
  ⟨remaining.length, generated.budget_exact⟩

/-- Numeric consequence of the exact resource invariant. -/
theorem depth_le_initial
    {rootFormula : Cnf}
    {initial remaining : List Var}
    {state : GeneratedStructuralBranchContext rootFormula}
    (generated :
      ResourceGeneratedFrom
        rootFormula
        initial
        remaining
        state) :
    state.depth ≤ initial.length := by
  rw [← generated.budget_exact]
  exact Nat.le_add_right _ _

end ResourceGeneratedFrom

/-- Resource-accounted generation using the root CNF's own syntax occurrences. -/
abbrev FormulaResourceGeneratedFrom
    (rootFormula : Cnf)
    (remaining : List Var)
    (state : GeneratedStructuralBranchContext rootFormula) :=
  ResourceGeneratedFrom
    rootFormula
    rootFormula.variableOccurrences
    remaining
    state

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.Literal.varOf
#print axioms ConstitutiveSearch.SAT.Clause.variableOccurrences
#print axioms ConstitutiveSearch.SAT.Cnf.variableOccurrences
#print axioms ConstitutiveSearch.SAT.VarRemoval
#print axioms ConstitutiveSearch.SAT.VarRemoval.length_eq
#print axioms ConstitutiveSearch.SAT.VarRemoval.find
#print axioms ConstitutiveSearch.SAT.ResourceGeneratedFrom
#print axioms ConstitutiveSearch.SAT.ResourceGeneratedFrom.budget_exact
#print axioms ConstitutiveSearch.SAT.ResourceGeneratedFrom.depth_bound_certificate
#print axioms ConstitutiveSearch.SAT.ResourceGeneratedFrom.depth_le_initial
#print axioms ConstitutiveSearch.SAT.FormulaResourceGeneratedFrom
/- AXIOM_AUDIT_END -/
