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
`branchResidual`. Its completion carrier stores a parent completion together
with exact realization of the selected Boolean value. The new decision is
prepended to the parent provenance.

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
A parent completion together with exact realization of one selected branch
value. The proof field makes the value provenance explicit and avoids any later
cast between unrelated child carriers.
-/
structure IndexedContextCompletion
    (parent : BranchContext)
    (var : Var)
    (value : Bool) : Type where
  underlying : parent.Carrier
  valueExact : parent.assignment underlying var = value

namespace IndexedContextCompletion

/-- Canonically index a parent completion by the Boolean value it actually has. -/
def ofParent
    {parent : BranchContext}
    {var : Var}
    (completion : parent.Carrier) :
    IndexedContextCompletion
      parent var (parent.assignment completion var) :=
  { underlying := completion
    valueExact := rfl }

/--
Two indexed completions are equal once their underlying parent completions are
equal. Equality of proof fields contributes no additional branch identity.
-/
theorem ext_underlying
    {parent : BranchContext}
    {var : Var}
    {value : Bool}
    {left right : IndexedContextCompletion parent var value}
    (underlyingExact : left.underlying = right.underlying) :
    left = right := by
  cases left with
  | mk leftUnderlying leftValueExact =>
      cases right with
      | mk rightUnderlying rightValueExact =>
          dsimp at underlyingExact
          cases underlyingExact
          have proofExact : leftValueExact = rightValueExact :=
            Subsingleton.elim _ _
          cases proofExact
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

/-- A Boolean distinct from `false` is exactly `true`. -/
theorem bool_true_of_ne_false
    (value : Bool)
    (notFalse : value ≠ false) :
    value = true := by
  cases value with
  | false =>
      exact False.elim (notFalse rfl)
  | true =>
      rfl

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
  if valueFalse : parent.assignment completion var = false then
    .inl
      { underlying := completion
        valueExact := valueFalse }
  else
    .inr
      { underlying := completion
        valueExact :=
          bool_true_of_ne_false
            (parent.assignment completion var)
            valueFalse }

/-- Exact computation rule for a parent completion known to realize `false`. -/
theorem splitContextCompletion_false
    (parent : BranchContext)
    (var : Var)
    (completion : parent.Carrier)
    (valueExact : parent.assignment completion var = false) :
    splitContextCompletion parent var completion =
      Sum.inl
        ({ underlying := completion
           valueExact := valueExact } :
          IndexedContextCompletion parent var false) := by
  unfold splitContextCompletion
  rw [dif_pos valueExact]
  apply congrArg
    (fun indexed : IndexedContextCompletion parent var false =>
      (Sum.inl indexed :
        IndexedContextCompletion parent var false ⊕
          IndexedContextCompletion parent var true))
  exact IndexedContextCompletion.ext_underlying rfl

/-- Exact computation rule for a parent completion known to realize `true`. -/
theorem splitContextCompletion_true
    (parent : BranchContext)
    (var : Var)
    (completion : parent.Carrier)
    (valueExact : parent.assignment completion var = true) :
    splitContextCompletion parent var completion =
      Sum.inr
        ({ underlying := completion
           valueExact := valueExact } :
          IndexedContextCompletion parent var true) := by
  have notFalse : parent.assignment completion var ≠ false := by
    intro falseExact
    have impossible : true = false :=
      valueExact.symm.trans falseExact
    cases impossible
  unfold splitContextCompletion
  rw [dif_neg notFalse]
  apply congrArg
    (fun indexed : IndexedContextCompletion parent var true =>
      (Sum.inr indexed :
        IndexedContextCompletion parent var false ⊕
          IndexedContextCompletion parent var true))
  exact IndexedContextCompletion.ext_underlying rfl

/-- Forget one freshly constituted child decision and recover the parent completion. -/
def mergeContextCompletion
    (parent : BranchContext)
    (var : Var) :
    (childContext parent var false).Carrier ⊕
      (childContext parent var true).Carrier →
        parent.Carrier
  | .inl completion => completion.underlying
  | .inr completion => completion.underlying

/-- Every Boolean value is one of the two exact branch values. -/
theorem bool_false_or_true (value : Bool) :
    value = false ∨ value = true := by
  cases value with
  | false => exact Or.inl rfl
  | true => exact Or.inr rfl

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
          | mk underlying valueExact =>
              exact
                splitContextCompletion_false
                  parent var underlying valueExact
      | inr completion =>
          cases completion with
          | mk underlying valueExact =>
              exact
                splitContextCompletion_true
                  parent var underlying valueExact
    mergeSplit := by
      intro completion
      cases bool_false_or_true (parent.assignment completion var) with
      | inl valueExact =>
          rw [splitContextCompletion_false parent var completion valueExact]
          rfl
      | inr valueExact =>
          rw [splitContextCompletion_true parent var completion valueExact]
          rfl }

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
#print axioms ConstitutiveSearch.SAT.IndexedContextCompletion.ofParent
#print axioms ConstitutiveSearch.SAT.IndexedContextCompletion.ext_underlying
#print axioms ConstitutiveSearch.SAT.IndexedContextCompletion.valueExact
#print axioms ConstitutiveSearch.SAT.childContext
#print axioms ConstitutiveSearch.SAT.childContext_newDecisionExact
#print axioms ConstitutiveSearch.SAT.childContext_parentDecisionsExact
#print axioms ConstitutiveSearch.SAT.bool_true_of_ne_false
#print axioms ConstitutiveSearch.SAT.splitContextCompletion
#print axioms ConstitutiveSearch.SAT.splitContextCompletion_false
#print axioms ConstitutiveSearch.SAT.splitContextCompletion_true
#print axioms ConstitutiveSearch.SAT.mergeContextCompletion
#print axioms ConstitutiveSearch.SAT.bool_false_or_true
#print axioms ConstitutiveSearch.SAT.contextSplit
#print axioms ConstitutiveSearch.SAT.merge_splitAtContext
/- AXIOM_AUDIT_END -/
