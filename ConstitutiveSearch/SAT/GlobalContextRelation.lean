import ConstitutiveSearch.SAT.GeneratedContext

/-!
# Global structural relations between generated SAT contexts

Sibling-only transport is not enough for a recursive frontier.  This module
lifts the existing polarity flip to the uniform state type
`GeneratedBranchContext rootFormula` and therefore allows comparison of states
that may have different immediate parents.

The relation is deliberately structural.  It requires exact compatibility of
both the current residual formula and the complete decision history under one
variable flip.  A source completion is transformed by flipping the assignment,
transporting formula satisfaction, transporting every recorded decision, and
reconstructing the target carrier from the target state's own generation
provenance.

No satisfiability query or common-parent hypothesis is used.
-/

namespace ConstitutiveSearch
namespace SAT

namespace BranchDecision

/-- Flip the recorded Boolean value exactly for the selected variable. -/
def flipAt (var : Var) (decision : BranchDecision) : BranchDecision :=
  if decision.var = var then
    { var := decision.var, value := !decision.value }
  else
    decision

end BranchDecision

/-- Flip one variable throughout a complete branch-decision history. -/
def flipDecisionsAt (var : Var) : List BranchDecision → List BranchDecision
  | [] => []
  | decision :: rest =>
      BranchDecision.flipAt var decision :: flipDecisionsAt var rest

namespace DecisionsHold

/--
Paired assignment and history flipping preserves exact realization of every
recorded decision.
-/
theorem flipAt
    {assignment : Assignment}
    {decisions : List BranchDecision}
    (holds : DecisionsHold assignment decisions)
    (var : Var) :
    DecisionsHold
      (Assignment.flipAt var assignment)
      (flipDecisionsAt var decisions) := by
  induction decisions with
  | nil =>
      exact True.intro
  | cons decision rest inductionHypothesis =>
      cases holds with
      | intro headHold tailHold =>
          by_cases same : decision.var = var
          · have selected :
                Assignment.flipAt var assignment decision.var =
                  !(assignment decision.var) := by
              rw [same]
              exact Assignment.flipAt_selected var assignment
            have flippedHead :
                Assignment.flipAt var assignment decision.var =
                  !decision.value := by
              rw [selected, headHold]
            constructor
            · rw [BranchDecision.flipAt, if_pos same]
              exact flippedHead
            · exact inductionHypothesis tailHold
          · have preserved :
                Assignment.flipAt var assignment decision.var =
                  assignment decision.var :=
              Assignment.flipAt_other var decision.var assignment same
            constructor
            · rw [BranchDecision.flipAt, if_neg same]
              rw [preserved]
              exact headHold
            · exact inductionHypothesis tailHold

end DecisionsHold

/--
Global polarity-flip relation between any two generated states of the same root
instance.  The states need not have the same immediate parent.
-/
structure GeneratedFlipAtRelation
    {rootFormula : Cnf}
    (var : Var)
    (source target : GeneratedBranchContext rootFormula) : Type where
  formulaExact :
    target.context.formula =
      Cnf.flipAt var source.context.formula
  decisionsExact :
    target.context.decisions =
      flipDecisionsAt var source.context.decisions

namespace GeneratedFlipAtRelation

/--
Transform a completion of one generated state into a completion of the target
state by acting on formula, assignment, history and target reconstruction.
-/
def mapCompletion
    {rootFormula : Cnf}
    {var : Var}
    {source target : GeneratedBranchContext rootFormula}
    (relation : GeneratedFlipAtRelation var source target)
    (completion : GeneratedBranchCompletion source) :
    GeneratedBranchCompletion target :=
  let sourceAssignment := source.context.assignment completion
  let targetAssignment := Assignment.flipAt var sourceAssignment
  let flippedSatisfaction :
      Satisfies targetAssignment
        (Cnf.flipAt var source.context.formula) :=
    (source.context.satisfaction completion).flipAt var
  let targetSatisfaction :
      Satisfies targetAssignment target.context.formula :=
    Eq.mp
      (congrArg
        (Satisfies targetAssignment)
        relation.formulaExact.symm)
      flippedSatisfaction
  let flippedDecisions :
      DecisionsHold targetAssignment
        (flipDecisionsAt var source.context.decisions) :=
    DecisionsHold.flipAt
      (source.context.decisionsExact completion)
      var
  let targetDecisions :
      DecisionsHold targetAssignment target.context.decisions :=
    Eq.mp
      (congrArg
        (DecisionsHold targetAssignment)
        relation.decisionsExact.symm)
      flippedDecisions
  target.reconstruction.rebuild
    targetAssignment targetSatisfaction targetDecisions

/-- The transported target completion represents exactly the flipped assignment. -/
theorem mapCompletion_assignment
    {rootFormula : Cnf}
    {var : Var}
    {source target : GeneratedBranchContext rootFormula}
    (relation : GeneratedFlipAtRelation var source target)
    (completion : GeneratedBranchCompletion source) :
    target.context.assignment (relation.mapCompletion completion) =
      Assignment.flipAt var (source.context.assignment completion) := by
  unfold mapCompletion
  exact
    target.reconstruction.assignment_rebuild
      (Assignment.flipAt var (source.context.assignment completion))
      _
      _

end GeneratedFlipAtRelation

/-- Structural action of global flip relations on generated completion spaces. -/
def generatedFlipAtAction
    {rootFormula : Cnf}
    (var : Var) :
    RelationalContinuationAction
      (GeneratedFlipAtRelation (rootFormula := rootFormula) var)
      GeneratedBranchCompletion :=
  { act := fun relation completion =>
      relation.mapCompletion completion }

/--
Executable search for a global generated-state flip relation.  Failure remains
only failure of this exact structural test.
-/
def generatedFlipAtSearch
    (rootFormula : Cnf)
    (var : Var) :
    RelationSearch
      (GeneratedFlipAtRelation (rootFormula := rootFormula) var) :=
  { find := fun source target =>
      if formulaExact :
          target.context.formula =
            Cnf.flipAt var source.context.formula then
        if decisionsExact :
            target.context.decisions =
              flipDecisionsAt var source.context.decisions then
          some
            { formulaExact := formulaExact
              decisionsExact := decisionsExact }
        else
          none
      else
        none }

/--
Preservation-aware normalization of an arbitrary heterogeneous generated-state
frontier using one selected global flip relation.
-/
def normalizeGeneratedFrontierByFlip
    (rootFormula : Cnf)
    (var : Var)
    (frontier : List (GeneratedBranchContext rootFormula)) :
    PreservingIrreducibleFrontierReduction
      (Completion := GeneratedBranchCompletion)
      (generatedFlipAtSearch rootFormula var)
      frontier :=
  normalizeFrontierPreserving
    (generatedFlipAtSearch rootFormula var)
    (generatedFlipAtAction var)
    frontier

end SAT
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.SAT.BranchDecision.flipAt
#print axioms ConstitutiveSearch.SAT.flipDecisionsAt
#print axioms ConstitutiveSearch.SAT.DecisionsHold.flipAt
#print axioms ConstitutiveSearch.SAT.GeneratedFlipAtRelation
#print axioms ConstitutiveSearch.SAT.GeneratedFlipAtRelation.mapCompletion
#print axioms ConstitutiveSearch.SAT.GeneratedFlipAtRelation.mapCompletion_assignment
#print axioms ConstitutiveSearch.SAT.generatedFlipAtAction
#print axioms ConstitutiveSearch.SAT.generatedFlipAtSearch
#print axioms ConstitutiveSearch.SAT.normalizeGeneratedFrontierByFlip
/- AXIOM_AUDIT_END -/
