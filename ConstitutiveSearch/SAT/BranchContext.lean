import ConstitutiveSearch.SAT.RestrictionTransport

/-!
# SAT branch contexts with constitutive decision provenance

This module lifts the exact Boolean branch split from one isolated CNF to a
recursive branch context.

A branch context carries only data already constituted by the search history:

* the current residual CNF
* a concrete carrier of positive completions
* the assignment represented by each completion
* satisfaction of the current residual CNF
* the finite list of branch decisions already made
* exact realization of those decisions by every completion

A child context is formed by one exact Boolean decision. Its CNF is the existing
`branchResidual`. Its completion carrier is indexed by the actual value of the
selected variable in a parent completion. The new decision is prepended to the
parent provenance.

No satisfiability query, branch preference, complexity class, or context
absorption is introduced here.
-/

namespace ConstitutiveSearch
namespace SAT

/-- One branch decision recorded in the constitutive history. -/
structure BranchDecision where
  var : Var
  value : Bool
  deriving DecidableEq

/-- Every recorded branch decision is realized by one assignment. -/
def DecisionsHold
    (assignment : Assignment) : List BranchDecision → Prop
  | [] => True
  | decision :: rest =>
      assignment decision.var = decision.value ∧
        DecisionsHold assignment rest

/--
A recursive SAT branch state with explicit provenance of all decisions that
constituted the current residual state.
-/
structure BranchContext : Type 1 where
  formula : Cnf
  Carrier : Type
  assignment : Carrier → Assignment
  satisfaction :
    (completion : Carrier) →
      Satisfies (assignment completion) formula
  decisions : List BranchDecision
  decisionsExact :
    (completion : Carrier) →
      DecisionsHold (assignment completion) decisions

/-- Generic completion family exposed by a branch context. -/
def BranchContextCompletion (context : BranchContext) : Type :=
  context.Carrier

/-- Root context before any branch decision has been constituted. -/
def rootContext (formula : Cnf) : BranchContext :=
  { formula := formula
    Carrier := Completion formula
    assignment := fun completion => completion.1
    satisfaction := fun completion => completion.2
    decisions := []
    decisionsExact := fun _completion => True.intro }

/--
A parent completion indexed by the actual Boolean value assigned to one selected
variable. The index is generated from the completion itself.
-/
inductive IndexedContextCompletion
    (parent : BranchContext)
    (var : Var) : Bool → Type
  | ofParent
      (completion : parent.Carrier) :
      IndexedContextCompletion parent var
        (parent.assignment completion var)

namespace IndexedContextCompletion

/-- Forget the branch-value index and recover the parent completion. -/
def underlying
    {parent : BranchContext}
    {var : Var}
    {value : Bool} :
    IndexedContextCompletion parent var value → parent.Carrier
  | .ofParent completion => completion

/-- The indexed variable value is realized exactly by the underlying assignment. -/
theorem valueExact
    {parent : BranchContext}
    {var : Var}
    {value : Bool}
    (completion : IndexedContextCompletion parent var value) :
    parent.assignment completion.underlying var = value := by
  cases completion with
  | ofParent _completion =>
      rfl

end IndexedContextCompletion

/--
One child branch constituted from a parent by fixing one Boolean variable value.
The child residual uses the existing syntactic branch reduction unchanged.
-/
def childContext
    (parent : BranchContext)
    (var : Var)
    (value : Bool) : BranchContext :=
  { formula := branchResidual parent.formula var value
    Carrier := IndexedContextCompletion parent var value
    assignment := fun completion =>
      parent.assignment completion.underlying
    satisfaction := fun completion =>
      (branchWeakening parent.formula var value).preservesSatisfaction
        (parent.satisfaction completion.underlying)
    decisions := { var := var, value := value } :: parent.decisions
    decisionsExact := fun completion =>
      And.intro
        completion.valueExact
        (parent.decisionsExact completion.underlying) }

/-- The newest decision is exact in every completion of a child context. -/
theorem childContext_newDecisionExact
    (parent : BranchContext)
    (var : Var)
    (value : Bool)
    (completion : (childContext parent var value).Carrier) :
    (childContext parent var value).assignment completion var = value :=
  completion.valueExact

/-- Parent decision provenance persists unchanged inside every child completion. -/
theorem childContext_parentDecisionsExact
    (parent : BranchContext)
    (var : Var)
    (value : Bool)
    (completion : (childContext parent var value).Carrier) :
    DecisionsHold
      ((childContext parent var value).assignment completion)
      parent.decisions :=
  parent.decisionsExact completion.underlying

/--
Split one parent completion exactly into the false or true child according to
its actual assignment value at the selected variable.
-/
def splitContextCompletion
    (parent : BranchContext)
    (var : Var)
    (completion : parent.Carrier) :
    (childContext parent var false).Carrier ⊕
      (childContext parent var true).Carrier :=
  match valueEq : parent.assignment completion var with
  | false =>
      .inl
        (Eq.mp
          (congrArg
            (IndexedContextCompletion parent var)
            valueEq)
          (.ofParent completion))
  | true =>
      .inr
        (Eq.mp
          (congrArg
            (IndexedContextCompletion parent var)
            valueEq)
          (.ofParent completion))

/-- Forget one freshly constituted child decision and recover the parent completion. -/
def mergeContextCompletion
    (parent : BranchContext)
    (var : Var) :
    (childContext parent var false).Carrier ⊕
      (childContext parent var true).Carrier →
        parent.Carrier
  | .inl completion => completion.underlying
  | .inr completion => completion.underlying

/-- The recursive Boolean branch is an exact reversible split of completion spaces. -/
def contextSplit
    (parent : BranchContext)
    (var : Var) :
    ExactBinarySplit
      BranchContextCompletion
      parent
      (childContext parent var false)
      (childContext parent var true) :=
  { split := splitContextCompletion parent var
    merge := mergeContextCompletion parent var
    splitMerge := by
      intro branch
      cases branch with
      | inl completion =>
          cases completion with
          | ofParent raw =>
              unfold splitContextCompletion mergeContextCompletion
              cases valueEq : parent.assignment raw var <;> rfl
      | inr completion =>
          cases completion with
          | ofParent raw =>
              unfold splitContextCompletion mergeContextCompletion
              cases valueEq : parent.assignment raw var <;> rfl
    mergeSplit := by
      intro completion
      unfold splitContextCompletion mergeContextCompletion
      cases valueEq : parent.assignment completion var <;> rfl }

/-- Direct exact split at a context, useful for recursive clients. -/
def splitAtContext
    (parent : BranchContext)
    (var : Var)
    (completion : parent.Carrier) :
    (childContext parent var false).Carrier ⊕
      (childContext parent var true).Carrier :=
  (contextSplit parent var).split completion

/-- Merging the direct context split reconstructs the original parent completion. -/
theorem merge_splitAtContext
    (parent : BranchContext)
    (var : Var)
    (completion : parent.Carrier) :
    (contextSplit parent var).merge
        (splitAtContext parent var completion) =
      completion :=
  (contextSplit parent var).mergeSplit completion

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.BranchDecision
#print axioms ConstitutiveSearch.SAT.DecisionsHold
#print axioms ConstitutiveSearch.SAT.BranchContext
#print axioms ConstitutiveSearch.SAT.BranchContextCompletion
#print axioms ConstitutiveSearch.SAT.rootContext
#print axioms ConstitutiveSearch.SAT.IndexedContextCompletion
#print axioms ConstitutiveSearch.SAT.IndexedContextCompletion.underlying
#print axioms ConstitutiveSearch.SAT.IndexedContextCompletion.valueExact
#print axioms ConstitutiveSearch.SAT.childContext
#print axioms ConstitutiveSearch.SAT.childContext_newDecisionExact
#print axioms ConstitutiveSearch.SAT.childContext_parentDecisionsExact
#print axioms ConstitutiveSearch.SAT.splitContextCompletion
#print axioms ConstitutiveSearch.SAT.mergeContextCompletion
#print axioms ConstitutiveSearch.SAT.contextSplit
#print axioms ConstitutiveSearch.SAT.merge_splitAtContext
/- AXIOM_AUDIT_END -/
