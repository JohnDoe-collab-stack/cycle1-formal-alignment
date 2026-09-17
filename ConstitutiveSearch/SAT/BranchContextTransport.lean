import ConstitutiveSearch.SAT.BranchContext
import ConstitutiveSearch.SAT.ResidualFlipTransport

/-!
# Structural transport between recursive SAT branch contexts

This module lifts the residual flip transport from residual CNFs to actual
`BranchContext` children with explicit decision provenance.

The missing datum is reconstruction of a context carrier from data that are
already constitutively available:

* an assignment
* satisfaction of the current residual formula
* exact realization of the decisions that formed the context

That reconstruction is available at a root context and is inherited by every
`childContext`. A flip at a fresh branch variable then preserves the previously
constituted decision history, reconstructs a parent completion, and therefore
produces a genuine completion of the opposite child branch.

No satisfiability decision, branch preference, or semantic oracle is added.
-/

namespace ConstitutiveSearch
namespace SAT

/-- The selected variable does not occur among previously constituted decisions. -/
def DecisionsAvoid (var : Var) : List BranchDecision → Prop
  | [] => True
  | decision :: rest =>
      decision.var ≠ var ∧ DecisionsAvoid var rest

namespace DecisionsHold

/-- Flipping a variable absent from the decision history preserves that history. -/
theorem flipAt_of_avoids
    {assignment : Assignment}
    {decisions : List BranchDecision}
    {var : Var}
    (holds : DecisionsHold assignment decisions)
    (avoids : DecisionsAvoid var decisions) :
    DecisionsHold (Assignment.flipAt var assignment) decisions := by
  induction decisions with
  | nil =>
      exact True.intro
  | cons decision rest inductionHypothesis =>
      cases holds with
      | intro headHold tailHold =>
          cases avoids with
          | intro headAvoid tailAvoid =>
              constructor
              · rw [Assignment.flipAt_other var decision.var assignment headAvoid]
                exact headHold
              · exact inductionHypothesis tailHold tailAvoid

end DecisionsHold

/--
A positive reconstruction interface for one branch context. It does not enlarge
what counts as a valid completion. It only states that already verified
assignment, formula satisfaction, and decision provenance determine a carrier
witness whose represented assignment is exact.
-/
structure BranchContextReconstruction (context : BranchContext) : Type 1 where
  rebuild :
    (assignment : Assignment) →
      Satisfies assignment context.formula →
        DecisionsHold assignment context.decisions →
          context.Carrier
  assignment_rebuild :
    (assignment : Assignment) →
      (satisfaction : Satisfies assignment context.formula) →
        (decisionsExact : DecisionsHold assignment context.decisions) →
          context.assignment (rebuild assignment satisfaction decisionsExact) =
            assignment

/-- Root contexts are reconstructible directly from ordinary CNF completions. -/
def rootContextReconstruction
    (formula : Cnf) :
    BranchContextReconstruction (rootContext formula) :=
  { rebuild := fun assignment satisfaction _decisionsExact =>
      ⟨assignment, satisfaction⟩
    assignment_rebuild := by
      intro _assignment _satisfaction _decisionsExact
      rfl }

/-- Rebuild one child completion from verified child-level data. -/
def rebuildChildCompletion
    {parent : BranchContext}
    (parentReconstruction : BranchContextReconstruction parent)
    (var : Var)
    (value : Bool)
    (assignment : Assignment)
    (residualSatisfaction :
      Satisfies assignment (branchResidual parent.formula var value))
    (decisionsExact :
      DecisionsHold assignment
        ({ var := var, value := value } :: parent.decisions)) :
    (childContext parent var value).Carrier :=
  let parentSatisfaction : Satisfies assignment parent.formula :=
    restoreSatisfaction
      parent.formula assignment var value
      decisionsExact.1 residualSatisfaction
  let parentCompletion : parent.Carrier :=
    parentReconstruction.rebuild
      assignment parentSatisfaction decisionsExact.2
  let representedAssignmentExact :
      parent.assignment parentCompletion = assignment :=
    parentReconstruction.assignment_rebuild
      assignment parentSatisfaction decisionsExact.2
  { underlying := parentCompletion
    valueExact := by
      rw [representedAssignmentExact]
      exact decisionsExact.1 }

/-- Rebuilt child completions represent exactly the supplied assignment. -/
theorem rebuildChildCompletion_assignment
    {parent : BranchContext}
    (parentReconstruction : BranchContextReconstruction parent)
    (var : Var)
    (value : Bool)
    (assignment : Assignment)
    (residualSatisfaction :
      Satisfies assignment (branchResidual parent.formula var value))
    (decisionsExact :
      DecisionsHold assignment
        ({ var := var, value := value } :: parent.decisions)) :
    (childContext parent var value).assignment
        (rebuildChildCompletion
          parentReconstruction var value assignment
          residualSatisfaction decisionsExact) =
      assignment := by
  unfold rebuildChildCompletion
  dsimp [childContext]
  exact
    parentReconstruction.assignment_rebuild
      assignment
      (restoreSatisfaction
        parent.formula assignment var value
        decisionsExact.1 residualSatisfaction)
      decisionsExact.2

/-- Reconstructibility is inherited by every recursively generated child context. -/
def childContextReconstruction
    {parent : BranchContext}
    (parentReconstruction : BranchContextReconstruction parent)
    (var : Var)
    (value : Bool) :
    BranchContextReconstruction (childContext parent var value) :=
  { rebuild := fun assignment residualSatisfaction decisionsExact =>
      rebuildChildCompletion
        parentReconstruction var value assignment
        residualSatisfaction decisionsExact
    assignment_rebuild := by
      intro assignment residualSatisfaction decisionsExact
      exact
        rebuildChildCompletion_assignment
          parentReconstruction var value assignment
          residualSatisfaction decisionsExact }

/-- View an actual child-context completion as residual branch data. -/
def childContextToResidual
    (parent : BranchContext)
    (var : Var)
    (value : Bool)
    (completion : (childContext parent var value).Carrier) :
    ResidualBranchCompletion parent.formula var value :=
  { assignment := parent.assignment completion.underlying
    valueExact := completion.valueExact
    residualSatisfaction :=
      (childContext parent var value).satisfaction completion }

/--
Structural relation between two children of one parent context. Besides the
existing residual flip relation it records only freshness of the selected
variable relative to the already constituted decision history.
-/
structure ContextFlipRelation
    (parent : BranchContext)
    (var : Var)
    (source target : Bool) : Type where
  residual : ResidualFlipRelation parent.formula var source target
  fresh : DecisionsAvoid var parent.decisions

namespace ContextFlipRelation

/--
Lift one residual flip to an actual child-context completion. Previous decisions
are preserved because the flipped variable is fresh, then the parent carrier is
reconstructed from the transported assignment and reconstructed satisfaction.
-/
def mapCompletion
    {parent : BranchContext}
    {var : Var}
    {source target : Bool}
    (reconstruction : BranchContextReconstruction parent)
    (relation : ContextFlipRelation parent var source target)
    (completion : (childContext parent var source).Carrier) :
    (childContext parent var target).Carrier :=
  let sourceResidual : ResidualBranchCompletion parent.formula var source :=
    childContextToResidual parent var source completion
  let targetResidual : ResidualBranchCompletion parent.formula var target :=
    relation.residual.mapCompletion sourceResidual
  let targetParentSatisfaction :
      Satisfies targetResidual.assignment parent.formula :=
    restoreSatisfaction
      parent.formula
      targetResidual.assignment
      var
      target
      targetResidual.valueExact
      targetResidual.residualSatisfaction
  let targetParentDecisions :
      DecisionsHold targetResidual.assignment parent.decisions := by
    change
      DecisionsHold
        (Assignment.flipAt var (parent.assignment completion.underlying))
        parent.decisions
    exact
      DecisionsHold.flipAt_of_avoids
        (parent.decisionsExact completion.underlying)
        relation.fresh
  let rebuiltParent : parent.Carrier :=
    reconstruction.rebuild
      targetResidual.assignment
      targetParentSatisfaction
      targetParentDecisions
  let representedAssignmentExact :
      parent.assignment rebuiltParent = targetResidual.assignment :=
    reconstruction.assignment_rebuild
      targetResidual.assignment
      targetParentSatisfaction
      targetParentDecisions
  { underlying := rebuiltParent
    valueExact := by
      rw [representedAssignmentExact]
      exact targetResidual.valueExact }

/-- The lifted context transport represents exactly the residual-flipped assignment. -/
theorem mapCompletion_assignment
    {parent : BranchContext}
    {var : Var}
    {source target : Bool}
    (reconstruction : BranchContextReconstruction parent)
    (relation : ContextFlipRelation parent var source target)
    (completion : (childContext parent var source).Carrier) :
    (childContext parent var target).assignment
        (relation.mapCompletion reconstruction completion) =
      Assignment.flipAt var
        ((childContext parent var source).assignment completion) := by
  unfold mapCompletion
  dsimp [childContext, childContextToResidual, ResidualFlipRelation.mapCompletion]
  exact
    reconstruction.assignment_rebuild
      (Assignment.flipAt var (parent.assignment completion.underlying))
      _
      _

end ContextFlipRelation

/-- Completion family of the two actual child contexts of one parent. -/
def ChildContextCompletionFamily
    (parent : BranchContext)
    (var : Var) : Bool → Type :=
  fun value => (childContext parent var value).Carrier

/-- Structural context-flip action on actual child completion spaces. -/
def contextFlipAction
    (parent : BranchContext)
    (reconstruction : BranchContextReconstruction parent)
    (var : Var) :
    RelationalContinuationAction
      (ContextFlipRelation parent var)
      (ChildContextCompletionFamily parent var) :=
  { act := fun relation completion =>
      relation.mapCompletion reconstruction completion }

/--
Executable context relation search. Residual flip search is reused unchanged,
and transport is admitted only when the selected variable is fresh relative to
previous decisions.
-/
def contextFlipSearch
    (parent : BranchContext)
    (var : Var) :
    RelationSearch (ContextFlipRelation parent var) :=
  { find := fun source target =>
      match (residualFlipSearch parent.formula var).find source target with
      | none => none
      | some residual =>
          if fresh : DecisionsAvoid var parent.decisions then
            some
              { residual := residual
                fresh := fresh }
          else
            none }

/-- Reduce the two actual child contexts using reconstructed structural transport. -/
def reduceContextBranches
    (parent : BranchContext)
    (reconstruction : BranchContextReconstruction parent)
    (var : Var) :
    PairFrontierReduction
      (Completion := ChildContextCompletionFamily parent var)
      (contextFlipSearch parent var)
      false
      true :=
  reducePair
    (contextFlipSearch parent var)
    (contextFlipAction parent reconstruction var)
    false
    true

/-- Derived width of the actual child-context frontier. -/
def contextBranchWidth
    (parent : BranchContext)
    (reconstruction : BranchContextReconstruction parent)
    (var : Var) : Nat :=
  (reduceContextBranches parent reconstruction var).width

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.DecisionsAvoid
#print axioms ConstitutiveSearch.SAT.DecisionsHold.flipAt_of_avoids
#print axioms ConstitutiveSearch.SAT.BranchContextReconstruction
#print axioms ConstitutiveSearch.SAT.rootContextReconstruction
#print axioms ConstitutiveSearch.SAT.rebuildChildCompletion
#print axioms ConstitutiveSearch.SAT.rebuildChildCompletion_assignment
#print axioms ConstitutiveSearch.SAT.childContextReconstruction
#print axioms ConstitutiveSearch.SAT.childContextToResidual
#print axioms ConstitutiveSearch.SAT.ContextFlipRelation
#print axioms ConstitutiveSearch.SAT.ContextFlipRelation.mapCompletion
#print axioms ConstitutiveSearch.SAT.ContextFlipRelation.mapCompletion_assignment
#print axioms ConstitutiveSearch.SAT.ChildContextCompletionFamily
#print axioms ConstitutiveSearch.SAT.contextFlipAction
#print axioms ConstitutiveSearch.SAT.contextFlipSearch
#print axioms ConstitutiveSearch.SAT.reduceContextBranches
#print axioms ConstitutiveSearch.SAT.contextBranchWidth
/- AXIOM_AUDIT_END -/
